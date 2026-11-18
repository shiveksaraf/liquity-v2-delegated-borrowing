// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {LiquityV2Constants} from "./LiquityV2Constants.sol";
import {LiquityV2CoreBase} from "./LiquityV2CoreBase.sol";

/// @title Design D BorrowerOperations (Rate-Bond Escrow)
/// @notice Resolves the flash-loan close-and-reopen impossibility theorem with minimal extra storage:
///         one packed 256-bit RateBond slot per active trove or batch plus an immutable per-batch
///         downward-cut log (CutEvent) closing lazy-sync timestamp clobbering.
contract DesignDBorrowerOps is LiquityV2CoreBase {
    /// @dev Packed strictly into 1 single 256-bit EVM storage slot (104 + 64 + 40 + 24 + 24 = 256 bits).
    struct RateBond {
        uint104 lockedBond;
        uint64 highWaterRate;
        uint40 lastUpdateTime;
        uint24 remainingTime;
        uint24 startCutIdx;
    }

    /// @dev Immutable downward batch-cut record packed into 1 single 256-bit slot (144 bits used).
    struct CutEvent {
        uint64 newRate;
        uint40 cutTime;
        uint40 coveredBefore;
    }

    struct BondAdjParams {
        bytes32 key;
        address payer;
        uint256 debt;
        uint256 oldRate;
        uint256 newRate;
        uint256 elapsed;
        bool isPremature;
        bool isSolo;
    }

    struct RemoveExitVars {
        bytes32 bKey;
        uint256 tVested;
        uint256 tForfeit;
        uint256 tCarry;
        uint256 bVested;
        uint256 bForfeit;
        uint256 bTransfer;
        uint256 bRem;
        uint256 bUnv;
        uint256 bHigh;
    }

    // --- Minimal Extra Storage: +3 base mapping slots (1 packed RateBond slot per active trove/batch) ---
    mapping(uint256 => RateBond) public troveBonds;
    mapping(address => RateBond) public batchBonds;
    mapping(address => CutEvent[]) internal batchCuts;

    error BondCastOverflow();

    event RateBondDeposited(bytes32 indexed key, address indexed payer, uint256 netDeposit, uint256 lockedBond);
    event RateBondVested(bytes32 indexed key, address indexed recipient, uint256 vestedAmount);
    event RateBondForfeited(bytes32 indexed key, uint256 forfeitedAmount, uint256 remainingLocked);

    constructor(uint256 _initialCollPrice) LiquityV2CoreBase(_initialCollPrice) {}

    /// @notice Allows an honest trove owner to claim vested escrow without changing their rate.
    function claimVestedTroveBond(uint256 _troveId) external returns (uint256 vested) {
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();

        uint256 syncForfeit;
        (vested, syncForfeit) = _syncAndVestTroveBond(_troveId, interestBatchManagerOf[_troveId]);
        _settleVestAndBurn(bytes32(_troveId), msg.sender, vested, syncForfeit);
    }

    /// @notice Allows an honest batch manager to claim vested escrow without changing the batch rate.
    function claimVestedBatchBond() external returns (uint256 vested) {
        if (!batches[msg.sender].exists) revert InvalidInterestBatchManager();

        vested = _vestBondAt(batchBonds[msg.sender], _toUint40(block.timestamp));
        _settleVestAndBurn(bytes32(uint256(uint160(msg.sender))), msg.sender, vested, 0);
    }

    function _computePrematureRateFee(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        TroveChange memory
    ) internal pure override returns (uint256) {
        if (_elapsed >= LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN || _newRate >= _oldRate) {
            return 0;
        }
        return calcInterestCeil(_debt * (_oldRate - _newRate), LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _elapsed);
    }

    function _onTroveRateAdjust(
        uint256 _troveId,
        address _payer,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        bool _isPremature,
        TroveChange memory _change
    ) internal override returns (uint256) {
        return _adjustWithBond(
            troveBonds[_troveId],
            BondAdjParams(bytes32(_troveId), _payer, _debt, _oldRate, _newRate, _elapsed, _isPremature, true),
            _change
        );
    }

    function _onBatchRateAdjust(
        address _manager,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        bool _isPremature,
        TroveChange memory _change
    ) internal override returns (uint256, bool) {
        return (
            _adjustWithBond(
                batchBonds[_manager],
                BondAdjParams(
                    bytes32(uint256(uint160(_manager))), _manager, _debt, _oldRate, _newRate, _elapsed, _isPremature, false
                ),
                _change
            ),
            true
        );
    }

    function _computeBatchJoinFee(
        uint256 _troveId,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newBatchRate,
        uint256 _elapsed,
        TroveChange memory _change
    ) internal view override returns (uint256) {
        uint256 baseFee = calcUpfrontFee(_debt, getNewApproxAvgInterestRateFromTroveChange(_change));
        if (_newBatchRate < _oldRate && _elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN) {
            uint256 cutFee =
                calcInterestCeil(_debt * (_oldRate - _newBatchRate), LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _elapsed);
            uint256 bondForfeit = _previewTroveCutForfeit(_troveId, _newBatchRate);
            uint256 uncovered = cutFee > bondForfeit ? cutFee - bondForfeit : 0;
            if (uncovered > baseFee) return uncovered;
        }
        return baseFee;
    }

    function _computeRemoveFromBatchFee(
        uint256,
        address,
        uint256,
        uint256,
        uint256,
        uint256,
        TroveChange memory
    ) internal pure override returns (uint256) {
        return 0;
    }

    function _onOpenTrove(uint256 _troveId, address _owner, uint256 _entireDebt, uint256 _rate) internal override {
        _lockExposureIncrease(_troveId, address(0), _owner, _entireDebt, _rate);
    }

    function _onOpenTroveInBatch(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256 _entireDebt,
        uint256,
        uint256 _batchRate
    ) internal override {
        _lockExposureIncrease(_troveId, _batchManager, _owner, _entireDebt, _batchRate);
    }

    function _onWithdrawBold(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256,
        uint256 _newTroveDebt,
        uint256,
        uint256 _activeRate
    ) internal override {
        _lockExposureIncrease(_troveId, _batchManager, _owner, _newTroveDebt, _activeRate);
    }

    function _onJoinBatch(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256 _oldRate,
        uint256 _newBatchRate,
        uint256,
        uint256 _newTroveDebt,
        uint256
    ) internal override {
        if (_newBatchRate > _oldRate) {
            _lockExposureIncrease(_troveId, _batchManager, _owner, _newTroveDebt, _newBatchRate);
            return;
        }

        RateBond storage tBond = troveBonds[_troveId];
        uint256 vested = _vestBondAt(tBond, _toUint40(block.timestamp));
        uint256 forfeit = 0;
        if (_newBatchRate < _oldRate && tBond.lockedBond > 0 && _newBatchRate < uint256(tBond.highWaterRate)) {
            forfeit = _applyCutForfeit(tBond, bytes32(_troveId), _toUint64(_newBatchRate));
        }

        if (tBond.lockedBond > 0) {
            if (batchBonds[_batchManager].lockedBond > 0) {
                _refreshJoinedTroveBond(_troveId, _owner, _batchManager, _newTroveDebt, _newBatchRate, vested, forfeit);
                return;
            }
            tBond.startCutIdx = _toUint24(batchCuts[_batchManager].length);
        }
        _settleVestAndBurn(bytes32(_troveId), _owner, vested, forfeit);
    }

    function _refreshJoinedTroveBond(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256 _newTroveDebt,
        uint256 _newBatchRate,
        uint256 _vested,
        uint256 _forfeit
    ) internal {
        RateBond storage tBond = troveBonds[_troveId];
        uint256 available = _vested + uint256(tBond.lockedBond);
        uint256 target = _targetBond(_newTroveDebt, _newBatchRate);
        _writeFreshBond(tBond, target, _newBatchRate, batchCuts[_batchManager].length);
        _settleBondDelta(bytes32(_troveId), _owner, target, available, _forfeit);
    }

    function _onRemoveFromBatch(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256 _oldBatchRate,
        uint256 _newRate,
        uint256 _exitingDebt
    ) internal override {
        RemoveExitVars memory v;
        v.bKey = bytes32(uint256(uint160(_batchManager)));
        (v.tVested, v.tForfeit) = _syncAndVestTroveBond(_troveId, _batchManager);

        RateBond storage tBond = troveBonds[_troveId];
        if (_newRate > _oldBatchRate) {
            v.tCarry = uint256(tBond.lockedBond);
            uint256 mgrOut = _unlockBatchSliceOnHikeExit(_batchManager, v.bKey, _exitingDebt, v.tCarry);
            uint256 target = _targetBond(_exitingDebt, _newRate);
            _writeFreshBond(tBond, target, _newRate, 0);
            _settleBondDelta(bytes32(_troveId), _owner, target, v.tVested + v.tCarry, v.tForfeit);
            _safeTransferBold(_batchManager, mgrOut);
            return;
        }

        if (_newRate < _oldBatchRate && tBond.lockedBond > 0 && _newRate < uint256(tBond.highWaterRate)) {
            v.tForfeit += _applyCutForfeit(tBond, bytes32(_troveId), _toUint64(_newRate));
        }
        tBond.startCutIdx = 0;
        v.tCarry = uint256(tBond.lockedBond);

        RateBond storage bBond = batchBonds[_batchManager];
        v.bVested = _vestBondAt(bBond, _toUint40(block.timestamp));
        v.bRem = uint256(bBond.remainingTime);
        v.bUnv = uint256(bBond.lockedBond);
        v.bHigh = uint256(bBond.highWaterRate);

        if (v.bUnv > 0 && v.bRem > 0 && _newRate < v.bHigh) {
            v.bForfeit = _cappedShortfall(_exitingDebt, v.bHigh - _newRate, v.bRem, v.tForfeit, v.bUnv);
            if (v.bForfeit > 0) {
                v.bUnv -= v.bForfeit;
                protocolYieldAccumulated += v.bForfeit;
                emit RateBondForfeited(v.bKey, v.bForfeit, v.bUnv);
            }
        }

        if (v.bUnv > 0 && v.bRem > 0 && _newRate > LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) {
            uint256 effRate = _newRate < v.bHigh ? _newRate : v.bHigh;
            if (effRate > LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) {
                v.bTransfer = _cappedShortfall(
                    _exitingDebt, effRate - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, v.bRem, v.tCarry, v.bUnv
                );
                if (v.bTransfer > 0) {
                    v.bUnv -= v.bTransfer;
                    _creditTransferredTroveBond(_troveId, _owner, v.tCarry + v.bTransfer, v.bTransfer, _newRate, v.bRem);
                }
            }
        }

        if (v.bForfeit > 0 || v.bTransfer > 0) {
            _writeRemainingBond(bBond, v.bUnv);
        }

        if (v.tVested > 0) emit RateBondVested(bytes32(_troveId), _owner, v.tVested);
        uint256 mgrRefund = msg.sender == _batchManager ? v.bVested : v.bVested + v.bForfeit + v.bTransfer;
        if (mgrRefund > 0) emit RateBondVested(v.bKey, _batchManager, mgrRefund);

        _safeTransferBold(_owner, v.tVested);
        _burnBold(v.tForfeit);
        if (msg.sender != _batchManager) _safePullBoldFromSender(v.bForfeit + v.bTransfer);
        _burnBold(v.bForfeit);
        _safeTransferBold(_batchManager, mgrRefund);
    }

    function _creditTransferredTroveBond(
        uint256 _troveId,
        address _owner,
        uint256 _newLocked,
        uint256 _added,
        uint256 _newRate,
        uint256 _bRem
    ) internal {
        RateBond storage tBond = troveBonds[_troveId];
        tBond.lockedBond = _toUint104(_newLocked);
        if (_newRate > uint256(tBond.highWaterRate)) tBond.highWaterRate = _toUint64(_newRate);
        tBond.lastUpdateTime = _toUint40(block.timestamp);
        if (_bRem > uint256(tBond.remainingTime)) tBond.remainingTime = _toUint24(_bRem);
        tBond.startCutIdx = 0;
        emit RateBondDeposited(bytes32(_troveId), _owner, _added, _newLocked);
    }

    function _unlockBatchSliceOnHikeExit(
        address _batchManager,
        bytes32 _bKey,
        uint256 _exitingDebt,
        uint256 _tCarry
    ) internal returns (uint256 mgrOut) {
        RateBond storage bBond = batchBonds[_batchManager];
        uint256 bVested = _vestBondAt(bBond, _toUint40(block.timestamp));
        uint256 bUnlock = 0;
        uint256 bUnv = uint256(bBond.lockedBond);
        uint256 bHigh = uint256(bBond.highWaterRate);
        uint256 bRem = uint256(bBond.remainingTime);
        if (bUnv > 0 && bRem > 0 && bHigh > LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) {
            bUnlock = _cappedShortfall(
                _exitingDebt, bHigh - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, bRem, _tCarry, bUnv
            );
            if (bUnlock > 0) _writeRemainingBond(bBond, bUnv - bUnlock);
        }
        mgrOut = bVested + bUnlock;
        if (mgrOut > 0) emit RateBondVested(_bKey, _batchManager, mgrOut);
    }

    function _onRepayBold(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256 _repayAmount,
        uint256,
        uint256
    ) internal override {
        (uint256 tVested, uint256 tForfeit) = _syncAndVestTroveBond(_troveId, _batchManager);
        RateBond storage bond = troveBonds[_troveId];
        uint256 unv = uint256(bond.lockedBond);
        uint256 hw = uint256(bond.highWaterRate);
        uint256 rem = uint256(bond.remainingTime);

        if (unv > 0 && hw > LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE && rem > 0) {
            uint256 rf = _cappedShortfall(_repayAmount, hw - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, rem, 0, unv);
            uint256 remLocked = unv - rf;
            _writeRemainingBond(bond, remLocked);
            protocolYieldAccumulated += rf;
            tForfeit += rf;
            emit RateBondForfeited(bytes32(_troveId), rf, remLocked);
        }
        if (tVested > 0) emit RateBondVested(bytes32(_troveId), _owner, tVested);
        _finishBatchExit(_owner, _batchManager, _repayAmount, tVested, tForfeit);
    }

    function _onCloseTrove(
        uint256 _troveId,
        address _owner,
        address _batchManager,
        uint256 _troveDebt,
        uint256
    ) internal override {
        (uint256 tVested, uint256 syncForfeit) = _syncAndVestTroveBond(_troveId, _batchManager);
        uint256 tRemForfeit = uint256(troveBonds[_troveId].lockedBond);
        delete troveBonds[_troveId];

        if (tRemForfeit > 0) {
            protocolYieldAccumulated += tRemForfeit;
            emit RateBondForfeited(bytes32(_troveId), tRemForfeit, 0);
        }
        if (tVested > 0) emit RateBondVested(bytes32(_troveId), _owner, tVested);

        _finishBatchExit(_owner, _batchManager, _troveDebt, tVested, syncForfeit + tRemForfeit);
    }

    function _finishBatchExit(
        address _owner,
        address _batchManager,
        uint256 _exitingDebt,
        uint256 _tVested,
        uint256 _tForfeit
    ) internal {
        uint256 bForfeit = 0;
        uint256 mgrRefund = 0;
        if (_batchManager != address(0)) {
            (bForfeit, mgrRefund) = _updateBatchExitState(
                batchBonds[_batchManager], bytes32(uint256(uint160(_batchManager))), _batchManager, _exitingDebt, _tForfeit
            );
        }
        _safeTransferBold(_owner, _tVested);
        _burnBold(_tForfeit);
        if (_batchManager != address(0)) {
            if (bForfeit > 0) {
                if (msg.sender != _batchManager) _safePullBoldFromSender(bForfeit);
                _burnBold(bForfeit);
            }
            _safeTransferBold(_batchManager, mgrRefund);
        }
    }

    function _syncAndVestTroveBond(uint256 _troveId, address _batchManager)
        internal
        returns (uint256 vested, uint256 syncForfeit)
    {
        RateBond storage tBond = troveBonds[_troveId];
        if (tBond.lockedBond == 0) return (0, 0);
        uint40 nowTs = _toUint40(block.timestamp);

        if (_batchManager != address(0)) {
            CutEvent[] storage cuts = batchCuts[_batchManager];
            uint256 cutsLen = cuts.length;
            uint256 i = uint256(tBond.startCutIdx);
            if (i < cutsLen) {
                uint256 vestEnd = uint256(tBond.lastUpdateTime) + uint256(tBond.remainingTime);
                uint256 origLockTime = vestEnd > LiquityV2Constants.UPFRONT_INTEREST_PERIOD
                    ? vestEnd - LiquityV2Constants.UPFRONT_INTEREST_PERIOD
                    : 0;
                for (; i < cutsLen && tBond.lockedBond > 0; ++i) {
                    CutEvent storage ev = cuts[i];
                    uint40 cTime = ev.cutTime;
                    if (uint256(cTime) >= vestEnd) break;
                    if (ev.coveredBefore == 0 || origLockTime + 1 >= uint256(ev.coveredBefore)) {
                        vested += _vestBondAt(tBond, cTime < nowTs ? cTime : nowTs);
                        if (tBond.lockedBond > 0 && ev.newRate < tBond.highWaterRate) {
                            syncForfeit += _applyCutForfeit(tBond, bytes32(_troveId), ev.newRate);
                        }
                    }
                }
                if (tBond.lockedBond > 0) tBond.startCutIdx = _toUint24(i);
            }
        }
        vested += _vestBondAt(tBond, nowTs);
    }

    function _applyCutForfeit(RateBond storage _bond, bytes32 _key, uint64 _newRate)
        internal
        returns (uint256 forfeit)
    {
        uint256 unv = uint256(_bond.lockedBond);
        uint256 hw = uint256(_bond.highWaterRate);
        forfeit = _cutForfeitAmt(unv, hw, uint256(_newRate));
        if (forfeit == 0) return 0;

        uint256 newLocked = unv - forfeit;
        if (newLocked == 0) {
            _clearBond(_bond);
        } else {
            // forge-lint: disable-next-line(unsafe-typecast)
            _bond.lockedBond = uint104(newLocked);
            _bond.highWaterRate = _newRate;
        }
        protocolYieldAccumulated += forfeit;
        emit RateBondForfeited(_key, forfeit, newLocked);
    }

    function _updateBatchExitState(
        RateBond storage _bond,
        bytes32 _key,
        address _manager,
        uint256 _exitingDebt,
        uint256 _alreadyForfeited
    ) internal returns (uint256 shareForfeit, uint256 managerRefund) {
        uint256 vested = _vestBondAt(_bond, _toUint40(block.timestamp));
        uint256 unv = uint256(_bond.lockedBond);
        uint256 hw = uint256(_bond.highWaterRate);
        uint256 rem = uint256(_bond.remainingTime);

        if (unv > 0 && rem > 0 && hw > LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) {
            shareForfeit = _cappedShortfall(
                _exitingDebt, hw - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, rem, _alreadyForfeited, unv
            );
            if (shareForfeit > 0) {
                uint256 remLocked = unv - shareForfeit;
                _writeRemainingBond(_bond, remLocked);
                protocolYieldAccumulated += shareForfeit;
                emit RateBondForfeited(_key, shareForfeit, remLocked);
            }
        }

        managerRefund = msg.sender == _manager ? vested : vested + shareForfeit;
        if (managerRefund > 0) emit RateBondVested(_key, _manager, managerRefund);
    }

    function _lockExposureIncrease(
        uint256 _troveId,
        address _batchManager,
        address _recipient,
        uint256 _newDebt,
        uint256 _rate
    ) internal {
        RateBond storage bond = troveBonds[_troveId];
        bytes32 key = bytes32(_troveId);
        (uint256 vested, uint256 syncForfeit) = _syncAndVestTroveBond(_troveId, _batchManager);
        uint256 available = vested + uint256(bond.lockedBond);

        if (_rate <= LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) {
            _settleVestAndBurn(key, _recipient, vested, syncForfeit);
            return;
        }

        uint256 target = _targetBond(_newDebt, _rate);
        uint256 cutIdx = _batchManager == address(0) ? 0 : batchCuts[_batchManager].length;
        _writeFreshBond(bond, target, _rate, cutIdx);
        _settleBondDelta(key, _recipient, target, available, syncForfeit);
    }

    function _adjustWithBond(RateBond storage _bond, BondAdjParams memory _p, TroveChange memory _change)
        internal
        returns (uint256)
    {
        uint256 lockedBefore = uint256(_bond.lockedBond);
        uint256 vested = _vestBondAt(_bond, _toUint40(block.timestamp));

        if (_p.newRate > _p.oldRate) {
            uint256 target = _targetBond(_p.debt, _p.newRate);
            _writeFreshBond(_bond, target, _p.newRate, 0);
            _settleBondDelta(_p.key, _p.payer, target, lockedBefore, 0);
            return 0;
        }

        uint256 forfeit = 0;
        bool handledByBond = false;
        uint256 coveredBefore = 0;
        if (_p.newRate < _p.oldRate && _bond.lockedBond > 0 && _p.newRate < uint256(_bond.highWaterRate)) {
            uint256 vestEnd = uint256(_bond.lastUpdateTime) + uint256(_bond.remainingTime);
            coveredBefore = (
                vestEnd > LiquityV2Constants.UPFRONT_INTEREST_PERIOD
                    ? vestEnd - LiquityV2Constants.UPFRONT_INTEREST_PERIOD
                    : 0
            ) + 1;
            forfeit = _applyCutForfeit(_bond, _p.key, _toUint64(_p.newRate));
            handledByBond = true;
        }

        if (!_p.isSolo && _p.newRate < _p.oldRate && _p.debt > 0) {
            batchCuts[_p.payer].push(
                CutEvent(_toUint64(_p.newRate), _toUint40(block.timestamp), handledByBond ? _toUint40(coveredBefore) : 0)
            );
        }

        _settleVestAndBurn(_p.key, _p.payer, vested, forfeit);

        if (_p.isSolo && _p.newRate < _p.oldRate && !handledByBond && _p.isPremature) {
            return _computePrematureRateFee(_p.debt, _p.oldRate, _p.newRate, _p.elapsed, _change);
        }
        return 0;
    }

    function _targetBond(uint256 _debt, uint256 _rate) internal pure returns (uint256) {
        return calcInterestCeil(
            _debt * (_rate - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE), LiquityV2Constants.UPFRONT_INTEREST_PERIOD
        );
    }

    function _cappedShortfall(uint256 _debt, uint256 _rateSpread, uint256 _time, uint256 _already, uint256 _cap)
        internal
        pure
        returns (uint256)
    {
        uint256 req = calcInterestCeil(_debt * _rateSpread, _time);
        uint256 need = req > _already ? req - _already : 0;
        return need >= _cap ? _cap : need;
    }

    function _cutForfeitAmt(uint256 _unv, uint256 _hw, uint256 _newRate) internal pure returns (uint256) {
        if (_unv == 0 || _newRate >= _hw || _hw <= LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) return 0;
        uint256 num = _unv * (_hw - _newRate);
        uint256 denom = _hw - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE;
        uint256 forfeit = (num - 1) / denom + 1;
        return forfeit > _unv ? _unv : forfeit;
    }

    function _clearBond(RateBond storage _bond) internal {
        _bond.lockedBond = 0;
        _bond.highWaterRate = 0;
        _bond.remainingTime = 0;
        _bond.startCutIdx = 0;
    }

    function _writeFreshBond(RateBond storage _bond, uint256 _target, uint256 _rate, uint256 _cutIdx) internal {
        _bond.lastUpdateTime = _toUint40(block.timestamp);
        if (_target == 0) {
            _clearBond(_bond);
        } else {
            _bond.lockedBond = _toUint104(_target);
            _bond.highWaterRate = _toUint64(_rate);
            _bond.remainingTime = _toUint24(LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
            _bond.startCutIdx = _toUint24(_cutIdx);
        }
    }

    function _writeRemainingBond(RateBond storage _bond, uint256 _remLocked) internal {
        if (_remLocked == 0) {
            _clearBond(_bond);
        } else {
            _bond.lockedBond = _toUint104(_remLocked);
        }
    }

    function _settleVestAndBurn(bytes32 _key, address _recipient, uint256 _vested, uint256 _forfeit) internal {
        if (_vested > 0) emit RateBondVested(_key, _recipient, _vested);
        _burnBold(_forfeit);
        _safeTransferBold(_recipient, _vested);
    }

    function _settleBondDelta(bytes32 _key, address _recipient, uint256 _target, uint256 _available, uint256 _burnAmt)
        internal
    {
        uint256 netDeposit = _target > _available ? _target - _available : 0;
        uint256 netRefund = _available > _target ? _available - _target : 0;
        if (netDeposit > 0) emit RateBondDeposited(_key, msg.sender, netDeposit, _target);
        else if (netRefund > 0) emit RateBondVested(_key, _recipient, netRefund);

        _burnBold(_burnAmt);
        _safePullBoldFromSender(netDeposit);
        _safeTransferBold(_recipient, netRefund);
    }

    function _vestBondAt(RateBond storage _bond, uint40 _ts) internal returns (uint256 vested) {
        uint256 locked = uint256(_bond.lockedBond);
        uint256 lastTs = uint256(_bond.lastUpdateTime);
        if (locked == 0 || uint256(_ts) <= lastTs) return 0;

        uint256 dt = uint256(_ts) - lastTs;
        uint256 rem = uint256(_bond.remainingTime);
        _bond.lastUpdateTime = _ts;
        if (dt >= rem || rem == 0) {
            vested = locked;
            _clearBond(_bond);
        } else {
            vested = (locked * dt) / rem;
            // forge-lint: disable-next-line(unsafe-typecast)
            _bond.lockedBond = uint104(locked - vested);
            // forge-lint: disable-next-line(unsafe-typecast)
            _bond.remainingTime = uint24(rem - dt);
        }
    }

    function _previewTroveCutForfeit(uint256 _troveId, uint256 _newRate) internal view returns (uint256) {
        RateBond storage bond = troveBonds[_troveId];
        uint256 locked = uint256(bond.lockedBond);
        if (locked == 0) return 0;
        uint256 dt = block.timestamp - uint256(bond.lastUpdateTime);
        uint256 rem = uint256(bond.remainingTime);
        uint256 unv = (dt >= rem || rem == 0) ? 0 : locked - (locked * dt) / rem;
        return _cutForfeitAmt(unv, uint256(bond.highWaterRate), _newRate);
    }

    function _burnBold(uint256 _amount) internal {
        if (_amount > 0) boldToken.burn(address(this), _amount);
    }

    function _safeTransferBold(address _to, uint256 _amount) internal {
        if (_amount > 0 && !boldToken.transfer(_to, _amount)) revert TransferFailed();
    }

    function _safePullBoldFromSender(uint256 _amount) internal {
        if (_amount > 0 && !boldToken.transferFrom(msg.sender, address(this), _amount)) revert TransferFailed();
    }

    function _checkBound(uint256 _x, uint256 _max) internal pure returns (uint256) {
        if (_x > _max) revert BondCastOverflow();
        return _x;
    }

    function _toUint104(uint256 _x) internal pure returns (uint104) {
        // forge-lint: disable-next-line(unsafe-typecast)
        return uint104(_checkBound(_x, type(uint104).max));
    }

    function _toUint64(uint256 _x) internal pure returns (uint64) {
        // forge-lint: disable-next-line(unsafe-typecast)
        return uint64(_checkBound(_x, type(uint64).max));
    }

    function _toUint40(uint256 _x) internal pure returns (uint40) {
        // forge-lint: disable-next-line(unsafe-typecast)
        return uint40(_checkBound(_x, type(uint40).max));
    }

    function _toUint24(uint256 _x) internal pure returns (uint24) {
        // forge-lint: disable-next-line(unsafe-typecast)
        return uint24(_checkBound(_x, type(uint24).max));
    }
}
