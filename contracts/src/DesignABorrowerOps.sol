// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {LiquityV2Constants} from "./LiquityV2Constants.sol";
import {LiquityV2CoreBase} from "./LiquityV2CoreBase.sol";

/// @title Design A BorrowerOperations (Incremental Hike Only)
/// @notice Implements the earlier asymmetric patch (DesignA_proposal.patch):
///         premature hikes pay 7 days of incremental rate delta D * (rNew - rOld) * P / Y,
///         while premature cuts retain Liquity V2's branch-average fee D * avgRate * P / Y.
///         Preserves identical EVM storage layout to StatusQuoBorrowerOps, closes upward
///         staircase inflation, but remains vulnerable to the spike-and-cut loophole.
contract DesignABorrowerOps is LiquityV2CoreBase {
    constructor(uint256 _initialCollPrice) LiquityV2CoreBase(_initialCollPrice) {}

    function _computePrematureRateFee(
        uint256 _debt,
        uint256 _oldRate,
        uint256 _newRate,
        uint256,
        TroveChange memory _change
    ) internal view override returns (uint256) {
        if (_newRate > _oldRate) {
            return calcInterest(_debt * (_newRate - _oldRate), LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        }
        uint256 avgInterestRate = getNewApproxAvgInterestRateFromTroveChange(_change);
        return calcUpfrontFee(_debt, avgInterestRate);
    }
}
