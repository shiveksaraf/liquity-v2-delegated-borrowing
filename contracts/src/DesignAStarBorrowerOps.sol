// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {LiquityV2Constants} from "./LiquityV2Constants.sol";
import {LiquityV2CoreBase} from "./LiquityV2CoreBase.sol";

/// @title Design A* BorrowerOperations (Symmetric-Commitment Increment Fee)
/// @notice Unique minimal zero-extra-storage cooldown fee mechanism:
///         - Premature hike (rNew > rOld, elapsed < P):  D * (rNew - rOld) * P / Y
///         - Premature cut  (rNew < rOld, elapsed < P):  D * (rOld - rNew) * (P - elapsed) / Y
///         - Post-cooldown  (elapsed >= P) or no-op:     0
///         Adds ZERO extra EVM storage slots relative to StatusQuoBorrowerOps and eliminates
///         the branch-average rate lookup during premature rate adjustments.
contract DesignAStarBorrowerOps is LiquityV2CoreBase {
    constructor(uint256 _initialCollPrice) LiquityV2CoreBase(_initialCollPrice) {}

    /// @notice Pure Design A* fee using Liquity V2's verbatim floor division (_calcInterest).
    function quoteDesignAStarFloor(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed
    ) public pure returns (uint256) {
        if (_elapsed >= LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN || _newRate == _oldRate) {
            return 0;
        }
        if (_newRate > _oldRate) {
            return calcInterest(_debt * (_newRate - _oldRate), LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        }
        uint256 remaining = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _elapsed;
        return calcInterest(_debt * (_oldRate - _newRate), remaining);
    }

    /// @notice Pure Design A* fee using exact ceiling division (<= 1 wei total spike-and-cut
    ///         shortfall vs. floored 7d hold cost; adding +1 wei eliminates the residual 1 wei gap).
    function quoteDesignAStarCeil(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed
    ) public pure returns (uint256) {
        if (_elapsed >= LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN || _newRate == _oldRate) {
            return 0;
        }
        if (_newRate > _oldRate) {
            return calcInterestCeil(_debt * (_newRate - _oldRate), LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        }
        uint256 remaining = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _elapsed;
        return calcInterestCeil(_debt * (_oldRate - _newRate), remaining);
    }

    /// @notice Exact 0-wei floor-shortfall cut fee (`ceilDiv + 1` on positive premature cuts).
    function quoteDesignAStarCeilZeroShortfall(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed
    ) public pure returns (uint256) {
        uint256 base = quoteDesignAStarCeil(_debt, _oldRate, _newRate, _elapsed);
        if (_elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN && _newRate < _oldRate && base > 0) {
            return base + 1;
        }
        return base;
    }

    function _computePrematureRateFee(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256 _elapsed,
        TroveChange memory
    ) internal pure override returns (uint256) {
        return quoteDesignAStarFloor(_debt, _oldRate, _newRate, _elapsed);
    }

    /// @notice Closes the zero-flash-loan batch-join and switchBatchManager cut bypass (F2.2):
    ///         joining a lower-rate batch within cooldown pays max(standardBatchJoinFee, DesignA* cutFee).
    function _computeBatchJoinFee(
        uint256,
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newBatchRate,
        uint256 _elapsed,
        TroveChange memory _change
    ) internal view override returns (uint256) {
        uint256 baseFee = calcUpfrontFee(_debt, getNewApproxAvgInterestRateFromTroveChange(_change));
        if (_newBatchRate < _oldRate && _elapsed < LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN) {
            uint256 cutFee = quoteDesignAStarFloor(_debt, _oldRate, _newBatchRate, _elapsed);
            if (cutFee > baseFee) return cutFee;
        }
        return baseFee;
    }
}
