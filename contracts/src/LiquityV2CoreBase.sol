// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {LiquityV2Constants} from "./LiquityV2Constants.sol";
import {BoldToken} from "./BoldToken.sol";

/// @title Liquity V2 Core Base Engine
/// @notice Stateful Liquity V2 Trove, Batch, and ActivePool accounting engine mirroring deployed
///         BorrowerOperations, TroveManager, and ActivePool storage semantics so derived fee
///         mechanisms can be compared apples-to-apples for storage layout, gas, and security.
abstract contract LiquityV2CoreBase {
    enum Status {
        nonExistent,
        active,
        closedByOwner
    }

    struct Trove {
        Status status;
        address owner;
        uint256 debt;
        uint256 coll;
        uint256 annualInterestRate;
        uint256 lastInterestRateAdjTime;
        uint256 lastDebtUpdateTime;
        uint256 weightedRecordedDebt;
        uint256 debtShares;
    }

    struct Batch {
        bool exists;
        uint128 minInterestRate;
        uint128 maxInterestRate;
        uint128 minInterestRateChangePeriod;
        uint256 debt;
        uint256 coll;
        uint256 totalDebtShares;
        uint256 annualInterestRate;
        uint256 annualManagementFee;
        uint256 lastInterestRateAdjTime;
        uint256 lastDebtUpdateTime;
        uint256 weightedRecordedDebt;
        uint256 weightedRecordedBatchManagementFee;
        uint256 accruedManagementFee;
    }

    struct TroveChange {
        uint256 collIncrease;
        uint256 collDecrease;
        uint256 debtIncrease;
        uint256 debtDecrease;
        uint256 upfrontFee;
        uint256 oldWeightedRecordedDebt;
        uint256 newWeightedRecordedDebt;
        uint256 oldWeightedRecordedBatchManagementFee;
        uint256 newWeightedRecordedBatchManagementFee;
        uint256 batchAccruedManagementFee;
    }

    // --- Immutables (stored in bytecode, zero storage slots) ---
    BoldToken public immutable boldToken;
    uint256 public immutable CCR;
    uint256 public immutable MCR;
    uint256 public immutable BCR;
    uint256 public immutable SCR;

    // --- Core Branch & ActivePool Storage (identical base layout across all mechanisms) ---
    bool public hasBeenShutDown;
    uint256 public collPrice;
    uint256 public aggRecordedDebt;
    uint256 public aggWeightedDebtSum;
    uint256 public aggRecordedColl;
    uint256 public aggWeightedBatchManagementFeeSum;
    uint256 public lastAggUpdateTime;
    uint256 public protocolYieldAccumulated;

    mapping(uint256 => Trove) public troves;
    mapping(uint256 => address) public interestBatchManagerOf;
    mapping(address => Batch) public batches;

    // --- Custom Errors (matching Liquity V2 BorrowerOperations) ---
    error IsShutDown();
    error TroveExists();
    error TroveNotActive();
    error TroveInBatch();
    error TroveNotInBatch();
    error BatchManagerNotNew();
    error NotOwner();
    error InterestRateTooLow();
    error InterestRateTooHigh();
    error InterestRateNotNew();
    error InterestNotInRange();
    error InvalidInterestBatchManager();
    error BatchManagerExists();
    error MinGeMax();
    error AnnualManagementFeeTooHigh();
    error MinInterestRateChangePeriodTooLow();
    error BatchInterestRateChangePeriodNotPassed();
    error UpfrontFeeTooHigh();
    error DebtBelowMin();
    error ICRBelowMCR();
    error ICRBelowMCRPlusBCR();
    error TCRBelowCCR();
    error TCRNotBelowSCR();
    error TransferFailed();
    error ZeroAdjustment();

    // --- Events ---
    event ShutDown(uint256 tcr);
    event TroveOpened(uint256 indexed troveId, address indexed owner, uint256 debt, uint256 rate, uint256 upfrontFee);
    event TroveDebtRepaid(uint256 indexed troveId, address indexed owner, uint256 repaidAmount, uint256 remainingDebt);
    event TroveDebtWithdrawn(
        uint256 indexed troveId, address indexed owner, uint256 withdrawnAmount, uint256 upfrontFee, uint256 newDebt
    );
    event TroveJoinedBatch(uint256 indexed troveId, address indexed batchManager, uint256 upfrontFee, uint256 newDebt);
    event TroveRemovedFromBatch(
        uint256 indexed troveId, address indexed oldBatchManager, uint256 newRate, uint256 upfrontFee, uint256 newDebt
    );
    event BatchManagementFeeFlushed(address indexed batchManager, uint256 amount);
    event TroveClosed(uint256 indexed troveId, address indexed owner, uint256 repaidDebt);
    event TroveInterestRateAdjusted(
        uint256 indexed troveId,
        uint256 oldRate,
        uint256 newRate,
        uint256 upfrontFee,
        uint256 newDebt
    );
    event BatchInterestRateAdjusted(
        address indexed batchManager,
        uint256 oldRate,
        uint256 newRate,
        uint256 upfrontFee,
        uint256 newDebt,
        uint256 accruedManagementFee
    );

    constructor(uint256 _initialCollPrice) {
        boldToken = new BoldToken(address(this));
        CCR = LiquityV2Constants.CCR_WETH;
        MCR = LiquityV2Constants.MCR_WETH;
        BCR = LiquityV2Constants.BCR_ALL;
        SCR = LiquityV2Constants.SCR_WETH;
        collPrice = _initialCollPrice;
        lastAggUpdateTime = block.timestamp;
    }

    // --- Exact Liquity V2 Math Primitives ---

    /// @notice Verbatim LiquityBase._calcInterest (two consecutive floor divisions).
    function calcInterest(uint256 _weightedDebt, uint256 _period) public pure returns (uint256) {
        return _weightedDebt * _period / LiquityV2Constants.ONE_YEAR / LiquityV2Constants.DECIMAL_PRECISION;
    }

    /// @notice Exact overflow-safe ceiling variant of _calcInterest for zero-shortfall commitment proofs.
    function calcInterestCeil(uint256 _weightedDebt, uint256 _period) public pure returns (uint256) {
        uint256 num = _weightedDebt * _period;
        if (num == 0) return 0;
        uint256 denom = LiquityV2Constants.ONE_YEAR * LiquityV2Constants.DECIMAL_PRECISION;
        return (num - 1) / denom + 1;
    }

    /// @notice Verbatim BorrowerOperations._calcUpfrontFee.
    function calcUpfrontFee(uint256 _debt, uint256 _avgInterestRate) public pure returns (uint256) {
        return calcInterest(_debt * _avgInterestRate, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
    }

    function _computeCR(uint256 _coll, uint256 _debt, uint256 _price) internal pure returns (uint256) {
        if (_debt == 0) return type(uint256).max;
        return (_coll * _price) / _debt;
    }

    function getPendingAggInterest() public view returns (uint256) {
        uint256 dt = block.timestamp - lastAggUpdateTime;
        if (dt == 0) return 0;
        return calcInterest(aggWeightedDebtSum, dt);
    }

    function getPendingAggBatchManagementFee() public view returns (uint256) {
        uint256 dt = block.timestamp - lastAggUpdateTime;
        if (dt == 0) return 0;
        return calcInterest(aggWeightedBatchManagementFeeSum, dt);
    }

    function getEntireBranchDebt() public view returns (uint256) {
        return aggRecordedDebt + getPendingAggInterest() + getPendingAggBatchManagementFee();
    }

    /// @notice Matches ActivePool.getNewApproxAvgInterestRateFromTroveChange.
    function getNewApproxAvgInterestRateFromTroveChange(TroveChange memory _change) public view returns (uint256) {
        uint256 newWeightedDebtSum = aggWeightedDebtSum + _change.newWeightedRecordedDebt - _change.oldWeightedRecordedDebt;
        uint256 newRecordedDebt = getEntireBranchDebt() + _change.debtIncrease - _change.debtDecrease;
        if (newRecordedDebt == 0) return 0;
        return newWeightedDebtSum / newRecordedDebt;
    }

    function getLatestTroveDebt(uint256 _troveId) public view returns (uint256) {
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) return 0;
        address bm = interestBatchManagerOf[_troveId];
        if (bm != address(0)) {
            Batch storage b = batches[bm];
            if (b.totalDebtShares == 0) return 0;
            (uint256 batchEntireDebt,,,) = getLatestBatchData(bm);
            return (batchEntireDebt * t.debtShares) / b.totalDebtShares;
        }
        uint256 elapsed = block.timestamp - t.lastDebtUpdateTime;
        return t.debt + calcInterest(t.weightedRecordedDebt, elapsed);
    }

    function getLatestBatchData(address _manager)
        public
        view
        returns (uint256 entireDebt, uint256 pendingManagementFee, uint256 weightedDebt, uint256 weightedMgmtFee)
    {
        Batch storage b = batches[_manager];
        uint256 dt = block.timestamp - b.lastDebtUpdateTime;
        uint256 accruedInterest = calcInterest(b.weightedRecordedDebt, dt);
        pendingManagementFee = calcInterest(b.weightedRecordedBatchManagementFee, dt);
        entireDebt = b.debt + accruedInterest + pendingManagementFee;
        weightedDebt = b.weightedRecordedDebt;
        weightedMgmtFee = b.weightedRecordedBatchManagementFee;
    }

    function getBatchAccruedManagementFee(address _manager) external view returns (uint256) {
        return batches[_manager].accruedManagementFee;
    }

    // --- Batch Manager Registration ---

    function registerBatchManager(
        uint128 _minInterestRate,
        uint128 _maxInterestRate,
        uint128 _currentInterestRate,
        uint128 _annualManagementFee,
        uint128 _minInterestRateChangePeriod
    ) external {
        if (hasBeenShutDown) revert IsShutDown();
        if (batches[msg.sender].exists) revert BatchManagerExists();
        _requireValidAnnualInterestRate(_minInterestRate);
        _requireValidAnnualInterestRate(_maxInterestRate);
        if (_minInterestRate >= _maxInterestRate) revert MinGeMax();
        if (_currentInterestRate < _minInterestRate || _currentInterestRate > _maxInterestRate) {
            revert InterestNotInRange();
        }
        if (_annualManagementFee > LiquityV2Constants.MAX_ANNUAL_BATCH_MANAGEMENT_FEE) {
            revert AnnualManagementFeeTooHigh();
        }
        if (_minInterestRateChangePeriod < LiquityV2Constants.MIN_INTEREST_RATE_CHANGE_PERIOD) {
            revert MinInterestRateChangePeriodTooLow();
        }

        Batch storage b = batches[msg.sender];
        b.exists = true;
        b.minInterestRate = _minInterestRate;
        b.maxInterestRate = _maxInterestRate;
        b.minInterestRateChangePeriod = _minInterestRateChangePeriod;
        b.annualInterestRate = _currentInterestRate;
        b.annualManagementFee = _annualManagementFee;
        b.lastInterestRateAdjTime = block.timestamp;
        b.lastDebtUpdateTime = block.timestamp;
    }

    // --- Trove Lifecycle Operations ---

    function openTrove(
        uint256 _troveId,
        uint256 _collAmount,
        uint256 _boldAmount,
        uint256 _annualInterestRate,
        uint256 _maxUpfrontFee
    ) external returns (uint256 upfrontFee) {
        if (hasBeenShutDown) revert IsShutDown();
        _requireValidAnnualInterestRate(_annualInterestRate);
        if (troves[_troveId].status != Status.nonExistent) revert TroveExists();

        TroveChange memory change;
        change.collIncrease = _collAmount;
        change.debtIncrease = _boldAmount;
        change.newWeightedRecordedDebt = _boldAmount * _annualInterestRate;

        uint256 avgInterestRate = getNewApproxAvgInterestRateFromTroveChange(change);
        upfrontFee = calcUpfrontFee(_boldAmount, avgInterestRate);
        if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
        change.upfrontFee = upfrontFee;

        uint256 entireDebt = _boldAmount + upfrontFee;
        if (entireDebt < LiquityV2Constants.MIN_DEBT) revert DebtBelowMin();

        uint256 icr = _computeCR(_collAmount, entireDebt, collPrice);
        if (icr < MCR) revert ICRBelowMCR();

        change.newWeightedRecordedDebt = entireDebt * _annualInterestRate;
        _checkNewTCRAboveCCR(change);

        _mintAggInterestAndAccountForTroveChange(change, address(0));

        Trove storage t = troves[_troveId];
        t.status = Status.active;
        t.owner = msg.sender;
        t.debt = entireDebt;
        t.coll = _collAmount;
        t.annualInterestRate = _annualInterestRate;
        t.lastInterestRateAdjTime = block.timestamp;
        t.lastDebtUpdateTime = block.timestamp;
        t.weightedRecordedDebt = change.newWeightedRecordedDebt;

        emit TroveOpened(_troveId, msg.sender, entireDebt, _annualInterestRate, upfrontFee);
        boldToken.mint(msg.sender, _boldAmount);
        _onOpenTrove(_troveId, msg.sender, entireDebt, _annualInterestRate);
    }

    function openTroveAndJoinBatch(
        uint256 _troveId,
        uint256 _collAmount,
        uint256 _boldAmount,
        address _batchManager,
        uint256 _maxUpfrontFee
    ) external returns (uint256 upfrontFee) {
        if (hasBeenShutDown) revert IsShutDown();
        Batch storage b = batches[_batchManager];
        if (!b.exists) revert InvalidInterestBatchManager();
        if (troves[_troveId].status != Status.nonExistent) revert TroveExists();

        TroveChange memory change;
        uint256 batchEntireDebt;
        uint256 pendingMgmtFee;
        {
            uint256 oldWeightedDebt;
            uint256 oldWeightedMgmtFee;
            (batchEntireDebt, pendingMgmtFee, oldWeightedDebt, oldWeightedMgmtFee) = getLatestBatchData(_batchManager);
            change.collIncrease = _collAmount;
            change.debtIncrease = _boldAmount;
            change.batchAccruedManagementFee = pendingMgmtFee;
            change.oldWeightedRecordedDebt = oldWeightedDebt;
            change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
            change.newWeightedRecordedDebt = (batchEntireDebt + _boldAmount) * b.annualInterestRate;
        }

        upfrontFee = calcUpfrontFee(_boldAmount, getNewApproxAvgInterestRateFromTroveChange(change));
        if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
        change.upfrontFee = upfrontFee;

        uint256 entireDebt = _boldAmount + upfrontFee;
        if (entireDebt < LiquityV2Constants.MIN_DEBT) revert DebtBelowMin();
        if (_computeCR(_collAmount, entireDebt, collPrice) < MCR + BCR) revert ICRBelowMCRPlusBCR();

        uint256 newBatchDebt = batchEntireDebt + entireDebt;
        change.newWeightedRecordedDebt = newBatchDebt * b.annualInterestRate;
        change.newWeightedRecordedBatchManagementFee = newBatchDebt * b.annualManagementFee;
        _checkNewTCRAboveCCR(change);

        _mintAggInterestAndAccountForTroveChange(change, _batchManager);

        uint256 mintedShares = (b.totalDebtShares == 0 || batchEntireDebt == 0)
            ? entireDebt
            : (entireDebt * b.totalDebtShares) / batchEntireDebt;
        b.debt = newBatchDebt;
        b.coll += _collAmount;
        b.totalDebtShares += mintedShares;
        b.lastDebtUpdateTime = block.timestamp;
        b.weightedRecordedDebt = change.newWeightedRecordedDebt;
        b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
        b.accruedManagementFee += pendingMgmtFee;

        interestBatchManagerOf[_troveId] = _batchManager;

        Trove storage t = troves[_troveId];
        t.status = Status.active;
        t.owner = msg.sender;
        t.debt = entireDebt;
        t.coll = _collAmount;
        t.annualInterestRate = b.annualInterestRate;
        t.lastInterestRateAdjTime = block.timestamp;
        t.lastDebtUpdateTime = block.timestamp;
        t.weightedRecordedDebt = entireDebt * b.annualInterestRate;
        t.debtShares = mintedShares;

        emit TroveOpened(_troveId, msg.sender, entireDebt, b.annualInterestRate, upfrontFee);
        boldToken.mint(msg.sender, _boldAmount);
        _onOpenTroveInBatch(_troveId, msg.sender, _batchManager, entireDebt, newBatchDebt, b.annualInterestRate);
    }

    function closeTrove(uint256 _troveId) external {
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();

        address batchManager = interestBatchManagerOf[_troveId];
        uint256 entireColl = t.coll;
        uint256 entireDebt = getLatestTroveDebt(_troveId);

        TroveChange memory change;
        change.collDecrease = entireColl;
        change.debtDecrease = entireDebt;

        uint256 batchDebtBefore = 0;
        if (batchManager != address(0)) {
            Batch storage b = batches[batchManager];
            (uint256 batchEntireDebt, uint256 pendingMgmtFee, uint256 oldWeightedDebt, uint256 oldWeightedMgmtFee) =
                getLatestBatchData(batchManager);
            batchDebtBefore = batchEntireDebt;
            uint256 batchFutureDebt = batchEntireDebt > entireDebt ? batchEntireDebt - entireDebt : 0;

            change.batchAccruedManagementFee = pendingMgmtFee;
            change.oldWeightedRecordedDebt = oldWeightedDebt;
            change.newWeightedRecordedDebt = batchFutureDebt * b.annualInterestRate;
            change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
            change.newWeightedRecordedBatchManagementFee = batchFutureDebt * b.annualManagementFee;

            if (!hasBeenShutDown && aggRecordedDebt > entireDebt) {
                _checkNewTCRAboveCCR(change);
            }

            b.debt = batchFutureDebt;
            b.coll = b.coll > entireColl ? b.coll - entireColl : 0;
            b.totalDebtShares = b.totalDebtShares > t.debtShares ? b.totalDebtShares - t.debtShares : 0;
            b.lastDebtUpdateTime = block.timestamp;
            b.weightedRecordedDebt = change.newWeightedRecordedDebt;
            b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
            b.accruedManagementFee += pendingMgmtFee;

            interestBatchManagerOf[_troveId] = address(0);
        } else {
            change.oldWeightedRecordedDebt = t.weightedRecordedDebt;
            if (!hasBeenShutDown && aggRecordedDebt > entireDebt) {
                _checkNewTCRAboveCCR(change);
            }
        }

        _onCloseTrove(_troveId, msg.sender, batchManager, entireDebt, batchDebtBefore);

        t.status = Status.closedByOwner;
        t.debt = 0;
        t.coll = 0;
        t.weightedRecordedDebt = 0;
        t.debtShares = 0;

        _mintAggInterestAndAccountForTroveChange(change, batchManager);
        emit TroveClosed(_troveId, msg.sender, entireDebt);
        boldToken.burn(msg.sender, entireDebt);
    }

    /// @notice Mirrors WETH_BorrowerOperations.repayBold() (partial debt repayment down to MIN_DEBT).
    function repayBold(uint256 _troveId, uint256 _boldAmount) external returns (uint256 actualRepayment) {
        if (hasBeenShutDown) revert IsShutDown();
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();

        uint256 entireDebt = getLatestTroveDebt(_troveId);
        uint256 maxRepayment =
            entireDebt > LiquityV2Constants.MIN_DEBT ? entireDebt - LiquityV2Constants.MIN_DEBT : 0;
        actualRepayment = _boldAmount > maxRepayment ? maxRepayment : _boldAmount;
        if (actualRepayment == 0) revert ZeroAdjustment();

        uint256 newDebt = entireDebt - actualRepayment;
        address batchManager = interestBatchManagerOf[_troveId];

        TroveChange memory change;
        change.debtDecrease = actualRepayment;

        uint256 batchDebtBefore = 0;
        if (batchManager != address(0)) {
            Batch storage b = batches[batchManager];
            uint256 pendingMgmtFee;
            {
                uint256 oldWeightedDebt;
                uint256 oldWeightedMgmtFee;
                (batchDebtBefore, pendingMgmtFee, oldWeightedDebt, oldWeightedMgmtFee) =
                    getLatestBatchData(batchManager);
                change.batchAccruedManagementFee = pendingMgmtFee;
                change.oldWeightedRecordedDebt = oldWeightedDebt;
                change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
            }
            uint256 batchFutureDebt = batchDebtBefore > actualRepayment ? batchDebtBefore - actualRepayment : 0;
            change.newWeightedRecordedDebt = batchFutureDebt * b.annualInterestRate;
            change.newWeightedRecordedBatchManagementFee = batchFutureDebt * b.annualManagementFee;

            uint256 burnedShares =
                batchDebtBefore > 0 ? (actualRepayment * b.totalDebtShares) / batchDebtBefore : 0;
            if (burnedShares > t.debtShares) burnedShares = t.debtShares;

            b.debt = batchFutureDebt;
            b.totalDebtShares -= burnedShares;
            b.lastDebtUpdateTime = block.timestamp;
            b.weightedRecordedDebt = change.newWeightedRecordedDebt;
            b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
            b.accruedManagementFee += pendingMgmtFee;

            t.debt = newDebt;
            t.debtShares -= burnedShares;
            t.lastDebtUpdateTime = block.timestamp;
            t.weightedRecordedDebt = newDebt * b.annualInterestRate;
        } else {
            change.oldWeightedRecordedDebt = t.weightedRecordedDebt;
            change.newWeightedRecordedDebt = newDebt * t.annualInterestRate;

            t.debt = newDebt;
            t.lastDebtUpdateTime = block.timestamp;
            t.weightedRecordedDebt = change.newWeightedRecordedDebt;
        }

        _onRepayBold(_troveId, msg.sender, batchManager, actualRepayment, entireDebt, batchDebtBefore);

        _mintAggInterestAndAccountForTroveChange(change, batchManager);
        emit TroveDebtRepaid(_troveId, msg.sender, actualRepayment, newDebt);
        boldToken.burn(msg.sender, actualRepayment);
    }

    /// @notice Mirrors WETH_BorrowerOperations.withdrawBold() (expanding debt on an existing trove).
    function withdrawBold(uint256 _troveId, uint256 _boldAmount, uint256 _maxUpfrontFee)
        external
        returns (uint256 upfrontFee)
    {
        if (hasBeenShutDown) revert IsShutDown();
        if (_boldAmount == 0) revert ZeroAdjustment();
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();

        uint256 entireDebt = getLatestTroveDebt(_troveId);
        address batchManager = interestBatchManagerOf[_troveId];

        TroveChange memory change;
        change.debtIncrease = _boldAmount;

        uint256 activeRate;
        uint256 newTroveDebt;
        uint256 newBatchDebt = 0;

        if (batchManager != address(0)) {
            Batch storage b = batches[batchManager];
            activeRate = b.annualInterestRate;
            uint256 batchDebtBefore;
            uint256 pendingMgmtFee;
            {
                uint256 oldWeightedDebt;
                uint256 oldWeightedMgmtFee;
                (batchDebtBefore, pendingMgmtFee, oldWeightedDebt, oldWeightedMgmtFee) =
                    getLatestBatchData(batchManager);
                change.batchAccruedManagementFee = pendingMgmtFee;
                change.oldWeightedRecordedDebt = oldWeightedDebt;
                change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
                change.newWeightedRecordedDebt = (batchDebtBefore + _boldAmount) * activeRate;
            }
            upfrontFee = calcUpfrontFee(_boldAmount, getNewApproxAvgInterestRateFromTroveChange(change));
            if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
            change.upfrontFee = upfrontFee;

            uint256 totalAdd = _boldAmount + upfrontFee;
            newTroveDebt = entireDebt + totalAdd;
            if (_computeCR(t.coll, newTroveDebt, collPrice) < MCR + BCR) revert ICRBelowMCRPlusBCR();

            newBatchDebt = batchDebtBefore + totalAdd;
            change.newWeightedRecordedDebt = newBatchDebt * activeRate;
            change.newWeightedRecordedBatchManagementFee = newBatchDebt * b.annualManagementFee;
            _checkNewTCRAboveCCR(change);

            uint256 mintedShares =
                batchDebtBefore > 0 ? (totalAdd * b.totalDebtShares) / batchDebtBefore : totalAdd;
            b.debt = newBatchDebt;
            b.totalDebtShares += mintedShares;
            b.lastDebtUpdateTime = block.timestamp;
            b.weightedRecordedDebt = change.newWeightedRecordedDebt;
            b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
            b.accruedManagementFee += pendingMgmtFee;

            t.debt = newTroveDebt;
            t.debtShares += mintedShares;
            t.lastDebtUpdateTime = block.timestamp;
            t.weightedRecordedDebt = newTroveDebt * activeRate;
        } else {
            activeRate = t.annualInterestRate;
            change.oldWeightedRecordedDebt = t.weightedRecordedDebt;
            change.newWeightedRecordedDebt = (entireDebt + _boldAmount) * activeRate;

            upfrontFee = calcUpfrontFee(_boldAmount, getNewApproxAvgInterestRateFromTroveChange(change));
            if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
            change.upfrontFee = upfrontFee;

            newTroveDebt = entireDebt + _boldAmount + upfrontFee;
            if (_computeCR(t.coll, newTroveDebt, collPrice) < MCR) revert ICRBelowMCR();

            change.newWeightedRecordedDebt = newTroveDebt * activeRate;
            _checkNewTCRAboveCCR(change);

            t.debt = newTroveDebt;
            t.lastDebtUpdateTime = block.timestamp;
            t.weightedRecordedDebt = change.newWeightedRecordedDebt;
        }

        _mintAggInterestAndAccountForTroveChange(change, batchManager);
        emit TroveDebtWithdrawn(_troveId, msg.sender, _boldAmount, upfrontFee, newTroveDebt);
        boldToken.mint(msg.sender, _boldAmount);
        _onWithdrawBold(_troveId, msg.sender, batchManager, _boldAmount + upfrontFee, newTroveDebt, newBatchDebt, activeRate);
    }

    struct JoinBatchVars {
        uint256 oldRate;
        uint256 elapsed;
        uint256 entireDebt;
        uint256 batchEntireDebt;
        uint256 pendingMgmtFee;
        uint256 newTroveDebt;
        uint256 newBatchDebt;
    }

    /// @notice Mirrors WETH_BorrowerOperations.setInterestBatchManager() and TroveManager.sol L1761.
    function setInterestBatchManager(
        uint256 _troveId,
        address _newBatchManager,
        uint256 _maxUpfrontFee
    ) public returns (uint256 upfrontFee) {
        return
            _setInterestBatchManager(_troveId, _newBatchManager, _maxUpfrontFee, troves[_troveId].lastInterestRateAdjTime);
    }

    function _setInterestBatchManager(
        uint256 _troveId,
        address _newBatchManager,
        uint256 _maxUpfrontFee,
        uint256 _effectiveLastAdjTime
    ) internal returns (uint256 upfrontFee) {
        if (hasBeenShutDown) revert IsShutDown();
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();
        if (interestBatchManagerOf[_troveId] != address(0)) revert TroveInBatch();
        Batch storage b = batches[_newBatchManager];
        if (!b.exists) revert InvalidInterestBatchManager();

        JoinBatchVars memory v;
        v.oldRate = t.annualInterestRate;
        v.elapsed = block.timestamp - _effectiveLastAdjTime;
        v.entireDebt = getLatestTroveDebt(_troveId);

        TroveChange memory change;
        {
            uint256 oldWeightedDebt;
            uint256 oldWeightedMgmtFee;
            (v.batchEntireDebt, v.pendingMgmtFee, oldWeightedDebt, oldWeightedMgmtFee) =
                getLatestBatchData(_newBatchManager);
            change.batchAccruedManagementFee = v.pendingMgmtFee;
            change.oldWeightedRecordedDebt = oldWeightedDebt + t.weightedRecordedDebt;
            change.newWeightedRecordedDebt = (v.batchEntireDebt + v.entireDebt) * b.annualInterestRate;
            change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
        }

        upfrontFee = _computeBatchJoinFee(_troveId, v.entireDebt, v.oldRate, b.annualInterestRate, v.elapsed, change);
        if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
        change.upfrontFee = upfrontFee;

        v.newTroveDebt = v.entireDebt + upfrontFee;
        if (_computeCR(t.coll, v.newTroveDebt, collPrice) < MCR + BCR) revert ICRBelowMCRPlusBCR();

        v.newBatchDebt = v.batchEntireDebt + v.newTroveDebt;
        change.newWeightedRecordedDebt = v.newBatchDebt * b.annualInterestRate;
        change.newWeightedRecordedBatchManagementFee = v.newBatchDebt * b.annualManagementFee;
        _checkNewTCRAboveCCR(change);

        _mintAggInterestAndAccountForTroveChange(change, _newBatchManager);

        uint256 mintedShares = (b.totalDebtShares == 0 || v.batchEntireDebt == 0)
            ? v.newTroveDebt
            : (v.newTroveDebt * b.totalDebtShares) / v.batchEntireDebt;
        b.debt = v.newBatchDebt;
        b.coll += t.coll;
        b.totalDebtShares += mintedShares;
        b.lastDebtUpdateTime = block.timestamp;
        b.weightedRecordedDebt = change.newWeightedRecordedDebt;
        b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
        b.accruedManagementFee += v.pendingMgmtFee;

        interestBatchManagerOf[_troveId] = _newBatchManager;
        t.debt = v.newTroveDebt;
        t.annualInterestRate = b.annualInterestRate;
        // Mirrors upstream TroveManager.sol L1761: always stamp join time so pre-aged batches
        // cannot overwrite a freshly spiked trove's cooldown timestamp.
        t.lastInterestRateAdjTime = block.timestamp;
        t.lastDebtUpdateTime = block.timestamp;
        t.weightedRecordedDebt = v.newTroveDebt * b.annualInterestRate;
        t.debtShares = mintedShares;

        _onJoinBatch(
            _troveId, msg.sender, _newBatchManager, v.oldRate, b.annualInterestRate, v.elapsed, v.newTroveDebt, v.newBatchDebt
        );
        emit TroveJoinedBatch(_troveId, _newBatchManager, upfrontFee, v.newTroveDebt);
    }

    struct RemoveFromBatchVars {
        address batchManager;
        uint256 oldBatchRate;
        uint256 effectiveAdjTime;
        uint256 elapsed;
        uint256 entireDebt;
        uint256 batchFutureDebt;
        uint256 pendingMgmtFee;
        uint256 newTroveDebt;
    }

    /// @notice Mirrors WETH_BorrowerOperations.removeFromBatch() and TroveManager.sol L1008-1009, L1937.
    function removeFromBatch(
        uint256 _troveId,
        uint256 _newAnnualInterestRate,
        uint256 _maxUpfrontFee
    ) public returns (uint256 upfrontFee) {
        if (hasBeenShutDown) revert IsShutDown();
        _requireValidAnnualInterestRate(_newAnnualInterestRate);
        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();

        RemoveFromBatchVars memory v;
        v.batchManager = interestBatchManagerOf[_troveId];
        if (v.batchManager == address(0)) revert TroveNotInBatch();

        Batch storage b = batches[v.batchManager];
        v.oldBatchRate = b.annualInterestRate;
        // Mirrors TroveManager._getLatestTroveData L1008-1009: max(batch, trove)
        v.effectiveAdjTime =
            b.lastInterestRateAdjTime > t.lastInterestRateAdjTime ? b.lastInterestRateAdjTime : t.lastInterestRateAdjTime;
        v.elapsed = block.timestamp - v.effectiveAdjTime;
        v.entireDebt = getLatestTroveDebt(_troveId);

        TroveChange memory change;
        {
            uint256 batchEntireDebt;
            uint256 oldWeightedDebt;
            uint256 oldWeightedMgmtFee;
            (batchEntireDebt, v.pendingMgmtFee, oldWeightedDebt, oldWeightedMgmtFee) =
                getLatestBatchData(v.batchManager);
            v.batchFutureDebt = batchEntireDebt > v.entireDebt ? batchEntireDebt - v.entireDebt : 0;
            change.batchAccruedManagementFee = v.pendingMgmtFee;
            change.oldWeightedRecordedDebt = oldWeightedDebt;
            change.newWeightedRecordedDebt =
                v.batchFutureDebt * v.oldBatchRate + v.entireDebt * _newAnnualInterestRate;
            change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
            change.newWeightedRecordedBatchManagementFee = v.batchFutureDebt * b.annualManagementFee;
        }

        if (
            v.oldBatchRate != _newAnnualInterestRate
                && v.elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN
        ) {
            upfrontFee = _computeRemoveFromBatchFee(
                _troveId, v.batchManager, v.entireDebt, v.oldBatchRate, _newAnnualInterestRate, v.elapsed, change
            );
            if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
            change.upfrontFee = upfrontFee;
        }

        v.newTroveDebt = v.entireDebt + upfrontFee;
        if (upfrontFee > 0) {
            if (_computeCR(t.coll, v.newTroveDebt, collPrice) < MCR) revert ICRBelowMCR();
            change.newWeightedRecordedDebt =
                v.batchFutureDebt * v.oldBatchRate + v.newTroveDebt * _newAnnualInterestRate;
            _checkNewTCRAboveCCR(change);
        }

        b.debt = v.batchFutureDebt;
        b.coll = b.coll > t.coll ? b.coll - t.coll : 0;
        b.totalDebtShares = b.totalDebtShares > t.debtShares ? b.totalDebtShares - t.debtShares : 0;
        b.lastDebtUpdateTime = block.timestamp;
        b.weightedRecordedDebt = v.batchFutureDebt * v.oldBatchRate;
        b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
        b.accruedManagementFee += v.pendingMgmtFee;

        interestBatchManagerOf[_troveId] = address(0);
        t.debt = v.newTroveDebt;
        t.debtShares = 0;
        t.annualInterestRate = _newAnnualInterestRate;
        // Mirrors TroveManager.onRemoveFromBatch L1937 unconditionally.
        t.lastInterestRateAdjTime = block.timestamp;
        t.lastDebtUpdateTime = block.timestamp;
        t.weightedRecordedDebt = v.newTroveDebt * _newAnnualInterestRate;

        _onRemoveFromBatch(
            _troveId, msg.sender, v.batchManager, v.oldBatchRate, _newAnnualInterestRate, v.entireDebt
        );
        _mintAggInterestAndAccountForTroveChange(change, v.batchManager);
        emit TroveRemovedFromBatch(_troveId, v.batchManager, _newAnnualInterestRate, upfrontFee, v.newTroveDebt);
    }

    /// @notice Mirrors WETH_BorrowerOperations.switchBatchManager(), capturing pre-removal
    ///         max(batch, trove) cooldown timestamp before TroveManager.onRemoveFromBatch stamps now.
    function switchBatchManager(
        uint256 _troveId,
        address _newBatchManager,
        uint256 _maxUpfrontFee
    ) external returns (uint256 upfrontFee) {
        address oldBatchManager = interestBatchManagerOf[_troveId];
        if (oldBatchManager == address(0)) revert TroveNotInBatch();
        if (oldBatchManager == _newBatchManager) revert BatchManagerNotNew();

        Batch storage oldB = batches[oldBatchManager];
        Trove storage t = troves[_troveId];
        uint256 oldEffectiveAdjTime = oldB.lastInterestRateAdjTime > t.lastInterestRateAdjTime
            ? oldB.lastInterestRateAdjTime
            : t.lastInterestRateAdjTime;
        uint256 oldBatchRate = oldB.annualInterestRate;

        removeFromBatch(_troveId, oldBatchRate, 0);
        upfrontFee = _setInterestBatchManager(_troveId, _newBatchManager, _maxUpfrontFee, oldEffectiveAdjTime);
    }

    /// @notice Mirrors ActivePool.sol L292 flushing batchAccruedManagementFee to the manager.
    function flushBatchManagementFee(address _manager) external returns (uint256 flushed) {
        Batch storage b = batches[_manager];
        if (!b.exists) revert InvalidInterestBatchManager();
        (uint256 entireDebt, uint256 pendingMgmtFee, uint256 oldWeightedDebt, uint256 oldWeightedMgmtFee) =
            getLatestBatchData(_manager);
        flushed = b.accruedManagementFee + pendingMgmtFee;

        TroveChange memory change;
        change.batchAccruedManagementFee = pendingMgmtFee;
        change.oldWeightedRecordedDebt = oldWeightedDebt;
        change.newWeightedRecordedDebt = entireDebt * b.annualInterestRate;
        change.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
        change.newWeightedRecordedBatchManagementFee = entireDebt * b.annualManagementFee;

        b.debt = entireDebt;
        b.lastDebtUpdateTime = block.timestamp;
        b.weightedRecordedDebt = change.newWeightedRecordedDebt;
        b.weightedRecordedBatchManagementFee = change.newWeightedRecordedBatchManagementFee;
        b.accruedManagementFee = 0;

        _mintAggInterestAndAccountForTroveChange(change, _manager);
        if (flushed > 0) {
            emit BatchManagementFeeFlushed(_manager, flushed);
            boldToken.mint(_manager, flushed);
        }
    }

    /// @notice Mirrors WETH_BorrowerOperations.shutdown() when branch TCR drops below SCR.
    function shutdown() external {
        if (hasBeenShutDown) revert IsShutDown();
        uint256 totalDebt = getEntireBranchDebt();
        uint256 tcr = _computeCR(aggRecordedColl, totalDebt, collPrice);
        if (tcr >= SCR) revert TCRNotBelowSCR();
        hasBeenShutDown = true;
        emit ShutDown(tcr);
    }

    // --- Individual Trove Interest Rate Adjustment (matches WETH_BorrowerOperations.sol#L510-L552) ---

    function adjustTroveInterestRate(
        uint256 _troveId,
        uint256 _newAnnualInterestRate,
        uint256 _maxUpfrontFee
    ) external returns (uint256 upfrontFee) {
        if (hasBeenShutDown) revert IsShutDown();
        _requireValidAnnualInterestRate(_newAnnualInterestRate);
        if (interestBatchManagerOf[_troveId] != address(0)) revert TroveInBatch();

        Trove storage t = troves[_troveId];
        if (t.status != Status.active) revert TroveNotActive();
        if (t.owner != msg.sender) revert NotOwner();

        uint256 oldRate = t.annualInterestRate;
        if (oldRate == _newAnnualInterestRate) revert InterestRateNotNew();

        uint256 entireDebt = getLatestTroveDebt(_troveId);
        uint256 newDebt = entireDebt;

        TroveChange memory change;
        change.oldWeightedRecordedDebt = t.weightedRecordedDebt;
        change.newWeightedRecordedDebt = newDebt * _newAnnualInterestRate;

        uint256 elapsed = block.timestamp - t.lastInterestRateAdjTime;
        bool isPremature = elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN;

        upfrontFee = _onTroveRateAdjust(
            _troveId, msg.sender, newDebt, oldRate, _newAnnualInterestRate, elapsed, isPremature, change
        );

        if (upfrontFee > 0) {
            if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
            change.upfrontFee = upfrontFee;
            newDebt += upfrontFee;

            uint256 newICR = _computeCR(t.coll, newDebt, collPrice);
            if (newICR < MCR) revert ICRBelowMCR();
            _checkNewTCRAboveCCR(change);
        }

        change.newWeightedRecordedDebt = newDebt * _newAnnualInterestRate;
        _mintAggInterestAndAccountForTroveChange(change, address(0));

        t.debt = newDebt;
        t.annualInterestRate = _newAnnualInterestRate;
        t.lastInterestRateAdjTime = block.timestamp;
        t.lastDebtUpdateTime = block.timestamp;
        t.weightedRecordedDebt = change.newWeightedRecordedDebt;

        emit TroveInterestRateAdjusted(_troveId, oldRate, _newAnnualInterestRate, upfrontFee, newDebt);
    }

    // --- Batch Manager Interest Rate Adjustment (matches WETH_BorrowerOperations.sol#L905-L965) ---

    struct BatchRateAdjVars {
        uint256 oldRate;
        uint256 debtBeforeFee;
        uint256 newDebt;
        uint256 elapsed;
        bool isPremature;
        bool includeFeeInMgmtBase;
    }

    function setBatchManagerAnnualInterestRate(
        uint128 _newAnnualInterestRate,
        uint256 _maxUpfrontFee
    ) external returns (uint256 upfrontFee) {
        if (hasBeenShutDown) revert IsShutDown();
        Batch storage b = batches[msg.sender];
        if (!b.exists) revert InvalidInterestBatchManager();
        if (_newAnnualInterestRate < b.minInterestRate || _newAnnualInterestRate > b.maxInterestRate) {
            revert InterestNotInRange();
        }
        if (block.timestamp < b.lastInterestRateAdjTime + uint256(b.minInterestRateChangePeriod)) {
            revert BatchInterestRateChangePeriodNotPassed();
        }

        BatchRateAdjVars memory vars;
        TroveChange memory batchChange;
        {
            (uint256 entireDebt, uint256 pendingMgmtFee, uint256 oldWeightedDebt, uint256 oldWeightedMgmtFee) =
                getLatestBatchData(msg.sender);

            vars.oldRate = b.annualInterestRate;
            vars.debtBeforeFee = entireDebt;
            vars.newDebt = entireDebt;

            batchChange.batchAccruedManagementFee = b.accruedManagementFee + pendingMgmtFee;
            batchChange.oldWeightedRecordedDebt = oldWeightedDebt;
            batchChange.newWeightedRecordedDebt = entireDebt * _newAnnualInterestRate;
            batchChange.oldWeightedRecordedBatchManagementFee = oldWeightedMgmtFee;
            batchChange.newWeightedRecordedBatchManagementFee = entireDebt * b.annualManagementFee;

            vars.elapsed = block.timestamp - b.lastInterestRateAdjTime;
            vars.isPremature =
                vars.oldRate != _newAnnualInterestRate && vars.elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN;
        }

        (upfrontFee, vars.includeFeeInMgmtBase) = _onBatchRateAdjust(
            msg.sender, vars.newDebt, vars.oldRate, _newAnnualInterestRate, vars.elapsed, vars.isPremature, batchChange
        );

        if (upfrontFee > 0) {
            if (upfrontFee > _maxUpfrontFee) revert UpfrontFeeTooHigh();
            batchChange.upfrontFee = upfrontFee;
            vars.newDebt += upfrontFee;

            batchChange.newWeightedRecordedDebt = vars.newDebt * _newAnnualInterestRate;
            batchChange.newWeightedRecordedBatchManagementFee =
                (vars.includeFeeInMgmtBase ? vars.newDebt : vars.debtBeforeFee) * b.annualManagementFee;

            _checkNewTCRAboveCCR(batchChange);
        }

        _mintAggInterestAndAccountForTroveChange(batchChange, msg.sender);

        b.debt = vars.newDebt;
        b.annualInterestRate = _newAnnualInterestRate;
        b.lastInterestRateAdjTime = block.timestamp;
        b.lastDebtUpdateTime = block.timestamp;
        b.weightedRecordedDebt = batchChange.newWeightedRecordedDebt;
        b.weightedRecordedBatchManagementFee = batchChange.newWeightedRecordedBatchManagementFee;
        b.accruedManagementFee = batchChange.batchAccruedManagementFee;

        emit BatchInterestRateAdjusted(
            msg.sender, vars.oldRate, _newAnnualInterestRate, upfrontFee, vars.newDebt, b.accruedManagementFee
        );
    }

    // --- Mechanism Extension Hooks (overridden cleanly by concrete subclasses) ---

    function _computePrematureRateFee(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        TroveChange memory _change
    ) internal view virtual returns (uint256);

    function _onTroveRateAdjust(
        uint256,
        address,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        bool _isPremature,
        TroveChange memory _change
    ) internal virtual returns (uint256) {
        if (!_isPremature) return 0;
        return _computePrematureRateFee(_debt, _oldRate, _newRate, _elapsed, _change);
    }

    function _onBatchRateAdjust(
        address,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        bool _isPremature,
        TroveChange memory _change
    ) internal virtual returns (uint256, bool) {
        if (!_isPremature) return (0, true);
        return (_computePrematureRateFee(_debt, _oldRate, _newRate, _elapsed, _change), true);
    }

    function _computeBatchJoinFee(
        uint256,
        uint256 _debt,
        uint256,
        uint256,
        uint256,
        TroveChange memory _change
    ) internal view virtual returns (uint256) {
        return calcUpfrontFee(_debt, getNewApproxAvgInterestRateFromTroveChange(_change));
    }

    function _computeRemoveFromBatchFee(
        uint256,
        address,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        TroveChange memory _change
    ) internal view virtual returns (uint256) {
        return _computePrematureRateFee(_debt, _oldRate, _newRate, _elapsed, _change);
    }

    function _onOpenTrove(uint256, address, uint256, uint256) internal virtual {}

    function _onOpenTroveInBatch(uint256, address, address, uint256, uint256, uint256) internal virtual {}

    function _onWithdrawBold(uint256, address, address, uint256, uint256, uint256, uint256) internal virtual {}

    function _onJoinBatch(uint256, address, address, uint256, uint256, uint256, uint256, uint256) internal virtual {}

    function _onRemoveFromBatch(uint256, address, address, uint256, uint256, uint256) internal virtual {}

    function _onRepayBold(uint256, address, address, uint256, uint256, uint256) internal virtual {}

    function _onCloseTrove(uint256, address, address, uint256, uint256) internal virtual {}

    // --- Internal ActivePool & Validation Helpers ---

    function _mintAggInterestAndAccountForTroveChange(TroveChange memory _change, address _batchManager) internal {
        uint256 pendingInterest = getPendingAggInterest();
        uint256 pendingMgmtFee = getPendingAggBatchManagementFee();
        lastAggUpdateTime = block.timestamp;

        if (pendingInterest > 0) {
            protocolYieldAccumulated += pendingInterest;
        }
        if (_change.upfrontFee > 0) {
            protocolYieldAccumulated += _change.upfrontFee;
        }

        uint256 newAggDebt = aggRecordedDebt + pendingInterest + pendingMgmtFee + _change.debtIncrease
            + _change.upfrontFee;
        aggRecordedDebt = newAggDebt > _change.debtDecrease ? newAggDebt - _change.debtDecrease : 0;

        aggRecordedColl = aggRecordedColl + _change.collIncrease - _change.collDecrease;

        uint256 nextWeightedDebt = aggWeightedDebtSum + _change.newWeightedRecordedDebt;
        aggWeightedDebtSum =
            nextWeightedDebt > _change.oldWeightedRecordedDebt ? nextWeightedDebt - _change.oldWeightedRecordedDebt : 0;

        if (_batchManager != address(0)) {
            uint256 nextWeightedMgmt = aggWeightedBatchManagementFeeSum + _change.newWeightedRecordedBatchManagementFee;
            aggWeightedBatchManagementFeeSum = nextWeightedMgmt > _change.oldWeightedRecordedBatchManagementFee
                ? nextWeightedMgmt - _change.oldWeightedRecordedBatchManagementFee
                : 0;
        }
    }

    function _checkNewTCRAboveCCR(TroveChange memory _change) internal view {
        uint256 totalColl = aggRecordedColl + _change.collIncrease - _change.collDecrease;
        uint256 totalDebt = getEntireBranchDebt() + _change.debtIncrease + _change.upfrontFee;
        totalDebt = totalDebt > _change.debtDecrease ? totalDebt - _change.debtDecrease : 0;
        if (totalDebt == 0) return;
        uint256 newTCR = _computeCR(totalColl, totalDebt, collPrice);
        if (newTCR < CCR) revert TCRBelowCCR();
    }

    function _requireValidAnnualInterestRate(uint256 _rate) internal pure {
        if (_rate < LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE) revert InterestRateTooLow();
        if (_rate > LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE) revert InterestRateTooHigh();
    }
}
