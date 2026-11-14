// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {LiquityV2CoreBase} from "./LiquityV2CoreBase.sol";

/// @title Status Quo Liquity V2 BorrowerOperations
/// @notice Verbatim deployed Liquity V2 premature interest-rate adjustment fee:
///         charges 7 days of branch-average interest (_calcUpfrontFee(newDebt, avgInterestRate))
///         on both premature hikes and premature cuts, capitalizes the fee onto borrower debt,
///         and includes the capitalized fee in newWeightedRecordedBatchManagementFee.
contract StatusQuoBorrowerOps is LiquityV2CoreBase {
    constructor(uint256 _initialCollPrice) LiquityV2CoreBase(_initialCollPrice) {}

    function _computePrematureRateFee(
        uint256 _debt,
        uint256,
        uint256,
        uint256,
        TroveChange memory _change
    ) internal view override returns (uint256) {
        uint256 avgInterestRate = getNewApproxAvgInterestRateFromTroveChange(_change);
        return calcUpfrontFee(_debt, avgInterestRate);
    }
}
