// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

/// @title Liquity V2 Protocol Constants
/// @notice Exact protocol parameters matching deployed Liquity V2 WETH / wstETH / rETH branches
///         (WETH_Constants.sol, Solidity 0.8.24).
library LiquityV2Constants {
    uint256 internal constant DECIMAL_PRECISION = 1e18;
    uint256 internal constant _100pct = DECIMAL_PRECISION;
    uint256 internal constant _1pct = DECIMAL_PRECISION / 100;

    // Collateral branch risk parameters (WETH defaults)
    uint256 internal constant CCR_WETH = 150 * _1pct;
    uint256 internal constant MCR_WETH = 110 * _1pct;
    uint256 internal constant SCR_WETH = 110 * _1pct;
    uint256 internal constant BCR_ALL = 10 * _1pct;

    // Minimum net BOLD debt for an active trove
    uint256 internal constant MIN_DEBT = 2000e18;

    // Annual interest rate bounds (0.5% to 250%)
    uint256 internal constant MIN_ANNUAL_INTEREST_RATE = _1pct / 2; // 5e15 = 0.5%
    uint256 internal constant MAX_ANNUAL_INTEREST_RATE = 250 * _1pct; // 250e16 = 250%

    // Batch management parameters
    uint128 internal constant MAX_ANNUAL_BATCH_MANAGEMENT_FEE = 10e16; // 10%
    uint128 internal constant MIN_INTEREST_RATE_CHANGE_PERIOD = 1 hours; // 3600s

    // Redemption fee floor (0.5%)
    uint256 internal constant REDEMPTION_FEE_FLOOR = _1pct / 2; // 5e15 = 0.5%

    // Time horizons
    uint256 internal constant ONE_YEAR = 365 days; // 31,536,000s
    uint256 internal constant UPFRONT_INTEREST_PERIOD = 7 days; // 604,800s
    uint256 internal constant INTEREST_RATE_ADJ_COOLDOWN = 7 days; // 604,800s

    // Stability Pool yield split (75% SP / 25% PIL)
    uint256 internal constant SP_YIELD_SPLIT = 75 * _1pct;
}
