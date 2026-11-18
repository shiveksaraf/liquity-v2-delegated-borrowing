// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {LiquityV2Constants} from "./LiquityV2Constants.sol";
import {LiquityV2CoreBase} from "./LiquityV2CoreBase.sol";

/// @title Co-Pay Aligned BorrowerOperations (Contractual Manager Co-Pay + Fee-Base Fix)
/// @notice Implements contractual manager co-pay beta in [0, 1e18]:
///         - Deducts manager co-pay from batchAccruedManagementFee first, and pulls/burns any
///           remaining co-pay shortfall directly from msg.sender so flushing accrued fees prior
///           to an update (ActivePool.sol L292) cannot dodge contractual co-pay.
///         - Excludes capitalized upfrontFee from newWeightedRecordedBatchManagementFee so
///           premature cooldown-breaking hikes never expand the manager's future fee base.
///         - Uses immutables only, adding ZERO extra EVM storage slots relative to StatusQuoBorrowerOps.
contract CoPayBorrowerOps is LiquityV2CoreBase {
    uint256 public immutable coPayFraction;
    bool public immutable useDesignAStar;

    error InvalidCoPayFraction();

    constructor(uint256 _initialCollPrice, uint256 _coPayFraction, bool _useDesignAStar)
        LiquityV2CoreBase(_initialCollPrice)
    {
        if (_coPayFraction > LiquityV2Constants.DECIMAL_PRECISION) revert InvalidCoPayFraction();
        coPayFraction = _coPayFraction;
        useDesignAStar = _useDesignAStar;
    }

    function _computePrematureRateFee(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        TroveChange memory _change
    ) internal view override returns (uint256) {
        if (useDesignAStar) {
            if (_elapsed >= LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN || _newRate == _oldRate) {
                return 0;
            }
            if (_newRate > _oldRate) {
                return calcInterest(_debt * (_newRate - _oldRate), LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
            }
            uint256 remaining = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _elapsed;
            return calcInterest(_debt * (_oldRate - _newRate), remaining);
        }
        uint256 avgInterestRate = getNewApproxAvgInterestRateFromTroveChange(_change);
        return calcUpfrontFee(_debt, avgInterestRate);
    }

    function _computeBatchJoinFee(
        uint256,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newBatchRate,
        uint256 _elapsed,
        TroveChange memory _change
    ) internal view override returns (uint256) {
        uint256 baseFee = calcUpfrontFee(_debt, getNewApproxAvgInterestRateFromTroveChange(_change));
        if (useDesignAStar && _newBatchRate < _oldRate && _elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN) {
            uint256 remaining = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _elapsed;
            uint256 cutFee = calcInterest(_debt * (_oldRate - _newBatchRate), remaining);
            if (cutFee > baseFee) return cutFee;
        }
        return baseFee;
    }

    function _onBatchRateAdjust(
        address,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        bool _isPremature,
        TroveChange memory _change
    ) internal override returns (uint256, bool) {
        if (!_isPremature) return (0, false);

        uint256 totalFee = _computePrematureRateFee(_debt, _oldRate, _newRate, _elapsed, _change);
        uint256 targetCoPay = (totalFee * coPayFraction) / LiquityV2Constants.DECIMAL_PRECISION;
        uint256 fromAccrued =
            targetCoPay <= _change.batchAccruedManagementFee ? targetCoPay : _change.batchAccruedManagementFee;

        if (fromAccrued > 0) {
            _change.batchAccruedManagementFee -= fromAccrued;
            protocolYieldAccumulated += fromAccrued;
        }

        uint256 directPull = targetCoPay - fromAccrued;
        if (directPull > 0) {
            if (!boldToken.transferFrom(msg.sender, address(this), directPull)) revert TransferFailed();
            boldToken.burn(address(this), directPull);
            protocolYieldAccumulated += directPull;
        }

        uint256 borrowerFee = totalFee - targetCoPay;
        // Return includeFeeInMgmtBase = false so capitalized upfrontFee never expands management-fee base
        return (borrowerFee, false);
    }
}
