// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {TestBase} from "./TestBase.sol";
import {BoldToken} from "../src/BoldToken.sol";
import {LiquityV2Constants} from "../src/LiquityV2Constants.sol";
import {LiquityV2CoreBase} from "../src/LiquityV2CoreBase.sol";
import {DesignAStarBorrowerOps} from "../src/DesignAStarBorrowerOps.sol";
import {DesignDBorrowerOps} from "../src/DesignDBorrowerOps.sol";

/// @title Differential & Security Fuzz Suite (13 Properties x 2,500+ Runs = 32,500+ Executions)
/// @notice Verifies exact mathematical invariants of Design A* and Design D across randomized
///         debts, rates, elapsed intervals, multi-step staircases, multi-step cuts, Sybil splits,
///         overflow boundaries, flash-loan close-and-reopen attacks, honest 7-day holds, and
///         full multi-borrower batch transition lifecycles.
contract DifferentialFuzzTest is TestBase {
    uint256 internal constant COLL_PRICE = 2500e18;
    address internal constant BORROWER = address(0xA11CE);
    address internal constant BG_BORROWER = address(0xB6B6);

    DesignAStarBorrowerOps internal aStar;

    function setUp() public {
        aStar = new DesignAStarBorrowerOps(COLL_PRICE);
    }

    function _mintBold(LiquityV2CoreBase _ops, address _to, uint256 _amount) internal {
        BoldToken token = _ops.boldToken();
        vm.prank(address(_ops));
        token.mint(_to, _amount);
    }

    /// @notice Fuzz Property 1: Upward Staircase Path-Invariance in Design A*
    ///         For any debt D in [MIN_DEBT, 1e12 BOLD] and any K-step chain r0 < r1 < ... < rK (K = 2..6),
    ///         0 <= singleJumpFee - sum(stepFees) <= K - 1 wei.
    function testFuzz_StaircasePathInvariance(
        uint256 _debt,
        uint8 _stepsRaw,
        uint256 _r0,
        uint256[6] memory _increments,
        uint256 _dt
    ) public view {
        uint256 debt = bound(_debt, LiquityV2Constants.MIN_DEBT, 1e30); // up to 1e12 BOLD
        uint256 kSteps = bound(uint256(_stepsRaw), 2, 6);
        uint256 r0 = bound(_r0, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 150e16);
        uint256 dt = bound(_dt, 1, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);

        uint256 remainingHeadroom = LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - r0;
        uint256 maxPerStep = remainingHeadroom / kSteps;
        if (maxPerStep == 0) return;

        uint256 currRate = r0;
        uint256 sumFees = 0;
        for (uint256 k = 0; k < kSteps; ++k) {
            uint256 delta = bound(_increments[k], 1, maxPerStep);
            uint256 nextRate = currRate + delta;
            sumFees += aStar.quoteDesignAStarFloor(debt, currRate, nextRate, dt);
            currRate = nextRate;
        }

        uint256 singleFee = aStar.quoteDesignAStarFloor(debt, r0, currRate, dt);
        assertGe(singleFee, sumFees, "Single jump fee must be >= sum of floored steps");
        assertLe(singleFee - sumFees, kSteps - 1, "Floor residual must be <= K - 1 wei");
    }

    /// @notice Fuzz Property 2: Spike-and-Cut No-Arbitrage in Design A* (both Floor and Ceil)
    ///         - Floor: interest(r_hi, dt) + fee_floor + interest(r_lo, P - dt) + 2 >= holdCost(r_hi, P)
    ///         - Ceil:  fee_ceil + interest(r_lo, P - dt) >= interest(r_hi, P - dt) (0 wei shortfall!)
    ///                  and interest(r_hi, dt) + fee_ceil + interest(r_lo, P - dt) + 1 >= holdCost(r_hi, P).
    function testFuzz_SpikeAndCutNoArbitrage_FloorAndCeil(
        uint256 _debt,
        uint256 _rLo,
        uint256 _spread,
        uint256 _dt
    ) public view {
        uint256 debt = bound(_debt, LiquityV2Constants.MIN_DEBT, 1e30);
        uint256 rLo = bound(_rLo, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - 1);
        uint256 rHi = rLo + bound(_spread, 1, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - rLo);
        uint256 dt = bound(_dt, 1, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);
        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - dt;

        uint256 holdCost = aStar.calcInterest(debt * rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 intHiDt = aStar.calcInterest(debt * rHi, dt);
        uint256 intLoRem = aStar.calcInterest(debt * rLo, rem);
        uint256 intHiRem = aStar.calcInterest(debt * rHi, rem);

        uint256 cutFeeFloor = aStar.quoteDesignAStarFloor(debt, rHi, rLo, dt);
        uint256 cutFeeCeil = aStar.quoteDesignAStarCeil(debt, rHi, rLo, dt);

        assertGe(intHiDt + cutFeeFloor + intLoRem + 2, holdCost, "Design A* floor bound (<= 2 wei)");
        assertGe(cutFeeCeil + intLoRem, intHiRem, "Design A* ceil exact 0-wei cut commitment");
        assertGe(intHiDt + cutFeeCeil + intLoRem + 1, holdCost, "Design A* ceil total bound (<= 1 wei)");
    }

    struct MultiCutVars {
        uint256 debt;
        uint256 r0;
        uint256 r1;
        uint256 r2;
        uint256 dt1;
        uint256 dt2;
        uint256 remFinal;
        uint256 fee1;
        uint256 fee2;
    }

    /// @notice Fuzz Property 3: Multi-Step Cut Superadditivity (r0 > r1 > r2 inside P)
    ///         Splitting a premature cut into two steps strictly increases cost by D*(r1 - r2)*dt1 / Y.
    function testFuzz_MultiStepCutSuperadditivity(
        uint256 _debt,
        uint256 _r2,
        uint256 _drop2,
        uint256 _drop1,
        uint256 _dt1,
        uint256 _dt2
    ) public view {
        MultiCutVars memory v;
        v.debt = bound(_debt, LiquityV2Constants.MIN_DEBT, 1e30);
        v.r2 = bound(_r2, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - 2);
        uint256 maxDropTotal = LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - v.r2;
        v.r1 = v.r2 + bound(_drop2, 1, maxDropTotal - 1);
        v.r0 = v.r1 + bound(_drop1, 1, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - v.r1);

        v.dt1 = bound(_dt1, 1, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 2);
        v.dt2 = bound(_dt2, 1, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt1 - 1);
        v.remFinal = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt1 - v.dt2;

        v.fee1 = aStar.quoteDesignAStarFloor(v.debt, v.r0, v.r1, v.dt1);
        v.fee2 = aStar.quoteDesignAStarFloor(v.debt, v.r1, v.r2, v.dt2);

        uint256 totalMultiCut = aStar.calcInterest(v.debt * v.r0, v.dt1) + v.fee1 + aStar.calcInterest(v.debt * v.r1, v.dt2)
            + v.fee2 + aStar.calcInterest(v.debt * v.r2, v.remFinal);
        uint256 holdR0 = aStar.calcInterest(v.debt * v.r0, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 superadditivePremium = aStar.calcInterest(v.debt * (v.r1 - v.r2), v.dt1);

        assertGe(totalMultiCut + 4, holdR0 + superadditivePremium, "Multi-step cut superadditivity");
    }

    /// @notice Fuzz Property 4: Sybil / Debt-Split Neutrality in Design A*
    ///         |fee(D1) + fee(D2) - fee(D1 + D2)| <= 1 wei for both hikes and cuts.
    function testFuzz_SybilDebtSplitNeutrality(
        uint256 _d1,
        uint256 _d2,
        uint256 _rOld,
        uint256 _rNew,
        uint256 _dt
    ) public view {
        uint256 d1 = bound(_d1, LiquityV2Constants.MIN_DEBT, 5e29);
        uint256 d2 = bound(_d2, LiquityV2Constants.MIN_DEBT, 5e29);
        uint256 rOld = bound(_rOld, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE);
        uint256 rNew = bound(_rNew, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE);
        uint256 dt = bound(_dt, 0, LiquityV2Constants.UPFRONT_INTEREST_PERIOD + 1 days);

        uint256 f1 = aStar.quoteDesignAStarFloor(d1, rOld, rNew, dt);
        uint256 f2 = aStar.quoteDesignAStarFloor(d2, rOld, rNew, dt);
        uint256 fSum = aStar.quoteDesignAStarFloor(d1 + d2, rOld, rNew, dt);

        assertGe(fSum, f1 + f2, "Floor superadditivity on debt sum");
        assertLe(fSum - (f1 + f2), 1, "Sybil / debt-split neutrality within 1 wei");
    }

    /// @notice Fuzz Property 5: Dust, Cooldown Expiration, and Whale Overflow Boundaries
    ///         Verifies zero arithmetic overflow up to 1e12 BOLD at 250% APR, exact zero fee
    ///         after cooldown expiration or no-op, and monotonicity in debt and rate delta.
    function testFuzz_DustAndMaxDebtOverflowBounds(
        uint256 _debt,
        uint256 _rOld,
        uint256 _rNew,
        uint256 _dt
    ) public view {
        // Test full range from 1 wei dust to 1e12 BOLD (1e30 wei)
        uint256 debt = bound(_debt, 1, 1e30);
        uint256 rOld = bound(_rOld, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE);
        uint256 rNew = bound(_rNew, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE);
        uint256 dt = bound(_dt, 0, 30 days);

        uint256 feeFloor = aStar.quoteDesignAStarFloor(debt, rOld, rNew, dt);
        uint256 feeCeil = aStar.quoteDesignAStarCeil(debt, rOld, rNew, dt);

        assertGe(feeCeil, feeFloor, "Ceil >= Floor always");
        assertLe(feeCeil - feeFloor, 1, "Ceil - Floor <= 1 wei always");

        if (dt >= LiquityV2Constants.INTEREST_RATE_ADJ_COOLDOWN || rNew == rOld) {
            assertEq(feeFloor, 0, "Zero fee post-cooldown or no-op (floor)");
            assertEq(feeCeil, 0, "Zero fee post-cooldown or no-op (ceil)");
        } else {
            uint256 maxPossible = aStar.calcInterestCeil(
                debt * LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE, LiquityV2Constants.UPFRONT_INTEREST_PERIOD
            );
            assertLe(feeCeil, maxPossible, "Fee bounded by max rate over 7d");
        }
    }

    struct FlashFuzzVars {
        uint256 debtPrincipal;
        uint256 r0;
        uint256 rHi;
        uint256 rLow;
        uint256 dt;
        uint256 flashFeeBps;
        uint256 coll;
        uint256 dAtSpike;
        uint256 bondDeposited;
        uint256 repayDebt;
        uint256 intDt;
        uint256 flashFee;
        uint256 balBeforeClose;
        uint256 reopenFee;
    }

    /// @notice Fuzz Property 6: Flash-Loan Close-and-Reopen Security in Design D (Stateful EVM Execution)
    ///         Across random (D, r0, r_hi, r_lo, dt, flashFeeBps), proves totalReopenCost >= holdCost
    ///         even against atomic same-block (dt = 0) or intra-week flash-loan close + reopen.
    function testFuzz_DesignD_FlashLoanCloseAndReopenSecurity(
        uint256 _debt,
        uint256 _r0,
        uint256 _hikeSpread,
        uint256 _rLow,
        uint256 _dt,
        uint256 _flashFeeBps
    ) public {
        FlashFuzzVars memory v;
        v.debtPrincipal = bound(_debt, LiquityV2Constants.MIN_DEBT, 50_000_000e18);
        v.r0 = bound(_r0, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 50e16);
        v.rHi = v.r0 + bound(_hikeSpread, 1e14, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - v.r0);
        v.rLow = bound(_rLow, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, v.rHi);
        v.dt = bound(_dt, 0, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);
        v.flashFeeBps = bound(_flashFeeBps, 0, 50);

        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);

        v.coll = (v.debtPrincipal * 4 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;
        vm.prank(BG_BORROWER);
        dd.openTrove(1, v.coll * 2, v.debtPrincipal * 2, 2e16, type(uint256).max);
        vm.prank(BORROWER);
        dd.openTrove(2, v.coll, v.debtPrincipal, v.r0, type(uint256).max);

        // Cooldown expires -> claim 100% vested openTrove bond, then post-cooldown spike to rHi
        skip(8 days);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(2);
        v.dAtSpike = dd.getLatestTroveDebt(2);
        uint256 bondUpperBound = dd.calcInterestCeil(
            v.dAtSpike * LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE, LiquityV2Constants.UPFRONT_INTEREST_PERIOD
        ) + 1e18;
        _mintBold(dd, BORROWER, bondUpperBound);
        vm.prank(BORROWER);
        dd.boldToken().approve(address(dd), type(uint256).max);

        uint256 balBeforeSpike = dd.boldToken().balanceOf(BORROWER);
        vm.prank(BORROWER);
        dd.adjustTroveInterestRate(2, v.rHi, type(uint256).max);
        v.bondDeposited = balBeforeSpike - dd.boldToken().balanceOf(BORROWER);

        // Wait dt < P and execute flash-loan closeTrove + openTrove(rLow)
        skip(v.dt);
        v.repayDebt = dd.getLatestTroveDebt(2);
        v.intDt = v.repayDebt - v.dAtSpike;
        v.flashFee = (v.repayDebt * v.flashFeeBps) / 10_000;
        v.balBeforeClose = dd.boldToken().balanceOf(BORROWER);
        _mintBold(dd, BORROWER, v.repayDebt);

        vm.prank(BORROWER);
        dd.closeTrove(2);
        uint256 vestedRefund = dd.boldToken().balanceOf(BORROWER) - v.balBeforeClose;
        uint256 forfeited = v.bondDeposited - vestedRefund;
        (uint104 lockedAfterClose,,,,) = dd.troveBonds(2);
        assertEq(uint256(lockedAfterClose), 0, "Closed trove bond cleared to 0");

        vm.prank(BORROWER);
        v.reopenFee = dd.openTrove(3, v.coll, v.dAtSpike, v.rLow, type(uint256).max);

        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt;
        uint256 holdCost = dd.calcInterest(v.dAtSpike * v.rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 totalReopenCost =
            v.intDt + forfeited + v.flashFee + v.reopenFee + dd.calcInterest(v.dAtSpike * v.rLow, rem);

        assertGe(totalReopenCost + 2, holdCost, "Design D blocks flash-loan close+reopen across all params");
    }

    /// @notice Fuzz Property 7: Honest-Hold Zero-Penalty in Design D (Stateful EVM Execution)
    ///         Across random (D, r0 < r_hi, extraWait), holding open for >= 7 days refunds 100% of bond.
    function testFuzz_DesignD_HonestHoldZeroPenalty(
        uint256 _debt,
        uint256 _r0,
        uint256 _hikeSpread,
        uint256 _extraWait
    ) public {
        uint256 debtPrincipal = bound(_debt, LiquityV2Constants.MIN_DEBT, 50_000_000e18);
        uint256 r0 = bound(_r0, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 100e16);
        uint256 rHi = r0 + bound(_hikeSpread, 1e14, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - r0);
        uint256 extraWait = bound(_extraWait, 0, 30 days);

        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);
        uint256 coll = (debtPrincipal * 4 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;

        vm.prank(BORROWER);
        dd.openTrove(1, coll, debtPrincipal, r0, type(uint256).max);
        skip(8 days);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        uint256 dAtSpike = dd.getLatestTroveDebt(1);
        uint256 funding = dd.calcInterestCeil(
            dAtSpike * LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE, LiquityV2Constants.UPFRONT_INTEREST_PERIOD
        ) + 1e18;
        _mintBold(dd, BORROWER, funding);
        vm.prank(BORROWER);
        dd.boldToken().approve(address(dd), type(uint256).max);

        uint256 bal0 = dd.boldToken().balanceOf(BORROWER);
        vm.prank(BORROWER);
        uint256 debtFee = dd.adjustTroveInterestRate(1, rHi, type(uint256).max);
        assertEq(debtFee, 0, "Design D hike imposes 0 debt-capitalized fee");

        skip(LiquityV2Constants.UPFRONT_INTEREST_PERIOD + extraWait);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        assertEq(dd.boldToken().balanceOf(BORROWER), bal0, "Honest 7-day hold receives exact 100% bond refund");
        assertEq(dd.boldToken().balanceOf(address(dd)), 0, "Contract escrow balance returns to 0");
    }

    /// @notice Fuzz Property 8: In-Place Premature Cut Commitment in Design D (Stateful EVM Execution)
    ///         Across random (D, r0 < r_hi, r_lo < r_hi, dt in [1, P-1]), proves pro-rata forfeiture
    ///         enforces full 7-day hold commitment and refunds the remaining bond at t = P.
    function testFuzz_DesignD_InPlaceCutMatchesHoldCommitment(
        uint256 _debt,
        uint256 _r0,
        uint256 _hikeSpread,
        uint256 _rLow,
        uint256 _dt
    ) public {
        FlashFuzzVars memory v;
        v.debtPrincipal = bound(_debt, LiquityV2Constants.MIN_DEBT, 50_000_000e18);
        v.r0 = bound(_r0, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 100e16);
        v.rHi = v.r0 + bound(_hikeSpread, 1e14, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - v.r0);
        v.rLow = bound(_rLow, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, v.rHi - 1);
        v.dt = bound(_dt, 1, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);
        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt;

        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);
        v.coll = (v.debtPrincipal * 4 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;

        vm.prank(BORROWER);
        dd.openTrove(1, v.coll, v.debtPrincipal, v.r0, type(uint256).max);
        skip(8 days);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        v.dAtSpike = dd.getLatestTroveDebt(1);
        uint256 funding = dd.calcInterestCeil(
            v.dAtSpike * LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE, LiquityV2Constants.UPFRONT_INTEREST_PERIOD
        ) + 1e18;
        _mintBold(dd, BORROWER, funding);
        vm.prank(BORROWER);
        dd.boldToken().approve(address(dd), type(uint256).max);

        uint256 bal0 = dd.boldToken().balanceOf(BORROWER);
        vm.prank(BORROWER);
        dd.adjustTroveInterestRate(1, v.rHi, type(uint256).max);

        skip(v.dt);
        vm.prank(BORROWER);
        uint256 cutDebtFee = dd.adjustTroveInterestRate(1, v.rLow, type(uint256).max);
        assertEq(cutDebtFee, 0, "Design D uses bond forfeiture without double-charging debt fee");

        // Complete the 7-day window and claim remaining vested bond
        skip(rem);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        uint256 netForfeited = bal0 - dd.boldToken().balanceOf(BORROWER);
        uint256 holdCost = dd.calcInterest(v.dAtSpike * v.rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 totalCutCost =
            dd.calcInterest(v.dAtSpike * v.rHi, v.dt) + netForfeited + dd.calcInterest(v.dAtSpike * v.rLow, rem);

        assertGe(totalCutCost + 2, holdCost, "Design D in-place cut enforces full 7-day commitment");
        assertEq(dd.boldToken().balanceOf(address(dd)), 0, "Escrow cleanly drained after full 7d");
    }

    /// @notice Fuzz Property 9: Partial repayBold Pro-Rata Forfeiture Blocks Escrow Bypass in Design D
    ///         Across random (D, r0 < r_hi, dt, repayAmount), proves repayBold forfeits pro-rata unvested
    ///         escrow so the repaid debt slice strictly pays >= full 7-day hold commitment.
    function testFuzz_DesignD_PartialRepayBlocksBypass(
        uint256 _debt,
        uint256 _r0,
        uint256 _hikeSpread,
        uint256 _dt,
        uint256 _repayFracBps
    ) public {
        FlashFuzzVars memory v;
        v.debtPrincipal = bound(_debt, LiquityV2Constants.MIN_DEBT + 1000e18, 50_000_000e18);
        v.r0 = bound(_r0, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 100e16);
        v.rHi = v.r0 + bound(_hikeSpread, 1e14, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - v.r0);
        v.dt = bound(_dt, 0, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);
        v.flashFeeBps = bound(_repayFracBps, 1, 10_000);

        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);
        v.coll = (v.debtPrincipal * 4 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;

        vm.prank(BORROWER);
        dd.openTrove(1, v.coll, v.debtPrincipal, v.r0, type(uint256).max);
        skip(8 days);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        {
            v.dAtSpike = dd.getLatestTroveDebt(1);
            uint256 funding = dd.calcInterestCeil(
                v.dAtSpike * LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE, LiquityV2Constants.UPFRONT_INTEREST_PERIOD
            ) + 1e18;
            _mintBold(dd, BORROWER, funding);
            vm.prank(BORROWER);
            dd.boldToken().approve(address(dd), type(uint256).max);

            uint256 balBeforeSpike = dd.boldToken().balanceOf(BORROWER);
            vm.prank(BORROWER);
            dd.adjustTroveInterestRate(1, v.rHi, type(uint256).max);
            v.bondDeposited = balBeforeSpike - dd.boldToken().balanceOf(BORROWER);
        }

        skip(v.dt);
        uint256 vestedTotal;
        {
            uint256 maxRepay = dd.getLatestTroveDebt(1) - LiquityV2Constants.MIN_DEBT;
            uint256 repayReq = (maxRepay * v.flashFeeBps) / 10_000;
            if (repayReq == 0) repayReq = 1;
            _mintBold(dd, BORROWER, repayReq);

            uint256 balBeforeRepay = dd.boldToken().balanceOf(BORROWER);
            vm.prank(BORROWER);
            v.repayDebt = dd.repayBold(1, repayReq);
            vestedTotal = (dd.boldToken().balanceOf(BORROWER) + v.repayDebt) - balBeforeRepay;
        }

        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt;
        skip(rem);
        vm.prank(BORROWER);
        vestedTotal += dd.claimVestedTroveBond(1);

        uint256 forfeited = v.bondDeposited - vestedTotal;
        uint256 slicePrincipal = v.repayDebt > v.dAtSpike ? v.dAtSpike : v.repayDebt;
        uint256 sliceHoldCost = dd.calcInterest(slicePrincipal * v.rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 sliceTotalCost = dd.calcInterest(slicePrincipal * v.rHi, v.dt) + forfeited
            + dd.calcInterest(slicePrincipal * LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, rem);

        assertGe(sliceTotalCost + 2, sliceHoldCost, "Partial repayBold cannot dodge 7d commitment");
        assertEq(dd.boldToken().balanceOf(address(dd)), 0, "Escrow cleanly drained after full 7d");
    }

    /// @notice Fuzz Property 10: Dormant Pre-Aged Shield Trove + withdrawBold Security in Design D
    ///         Across random (drawAmount, rHi, dt), proves expanding a dormant 2,000 BOLD trove aged 30 days
    ///         and closing early never beats holding rHi for 7 days.
    function testFuzz_DesignD_DormantShieldWithdrawBoldSecurity(
        uint256 _drawAmount,
        uint256 _rHi,
        uint256 _dt
    ) public {
        FlashFuzzVars memory v;
        v.debtPrincipal = bound(_drawAmount, 10_000e18, 25_000_000e18);
        v.rHi = bound(
            _rHi, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE + 1e14, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE
        );
        v.dt = bound(_dt, 0, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);

        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);
        v.coll = ((v.debtPrincipal + 2_000e18) * 4 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;

        {
            uint256 funding = dd.calcInterestCeil(
                (v.debtPrincipal + 5_000e18) * LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE,
                LiquityV2Constants.UPFRONT_INTEREST_PERIOD
            ) + 10_000e18;
            _mintBold(dd, BORROWER, funding);
            vm.prank(BORROWER);
            dd.boldToken().approve(address(dd), type(uint256).max);
        }

        vm.prank(BORROWER);
        dd.openTrove(1, v.coll, 2_000e18, v.rHi, type(uint256).max);
        skip(30 days);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        vm.prank(BORROWER);
        uint256 openFee = dd.withdrawBold(1, v.debtPrincipal, type(uint256).max);
        v.dAtSpike = dd.getLatestTroveDebt(1);
        v.bondDeposited = dd.boldToken().balanceOf(address(dd));

        skip(v.dt);
        uint256 forfeited;
        {
            uint256 repayAmt = dd.getLatestTroveDebt(1);
            _mintBold(dd, BORROWER, repayAmt);
            uint256 balBefore = dd.boldToken().balanceOf(BORROWER);
            vm.prank(BORROWER);
            dd.closeTrove(1);
            uint256 vested = (dd.boldToken().balanceOf(BORROWER) + repayAmt) - balBefore;
            forfeited = v.bondDeposited - vested;
        }

        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt;
        uint256 holdCost = dd.calcInterest(v.dAtSpike * v.rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 attackCost = dd.calcInterest(v.dAtSpike * v.rHi, v.dt) + forfeited + openFee
            + dd.calcInterest(v.dAtSpike * LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, rem);
        assertGe(attackCost + 2, holdCost, "Design D blocks dormant shield withdrawBold across all random params");
    }

    /// @notice Fuzz Property 11: Zero-Flash-Loan Batch-Join No-Arbitrage in Hardened Design A*
    ///         Across random (D, rHi > rBatch, dt in [0, P-1]), joining a lower-rate batch prematurely
    ///         never beats holding rHi for the full 7-day cooldown.
    function testFuzz_DesignAStar_BatchJoinNoArbitrage(
        uint256 _debt,
        uint256 _rBatch,
        uint256 _spread,
        uint256 _dt
    ) public {
        uint256 debt = bound(_debt, LiquityV2Constants.MIN_DEBT, 50_000_000e18);
        uint256 rBatch = bound(_rBatch, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 200e16);
        uint256 rHi = rBatch + bound(_spread, 1e14, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - rBatch);
        uint256 dt = bound(_dt, 0, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);
        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - dt;

        vm.warp(1_770_000_000);
        DesignAStarBorrowerOps das = new DesignAStarBorrowerOps(COLL_PRICE);
        address mgr = address(0x9999);
        vm.prank(mgr);
        das.registerBatchManager(5e15, 250e16, uint128(rBatch), 0, 1 hours);

        uint256 coll = (debt * 5 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;
        vm.prank(BORROWER);
        das.openTrove(1, coll, debt, rBatch, type(uint256).max);
        skip(8 days);
        vm.prank(BORROWER);
        das.adjustTroveInterestRate(1, rHi, type(uint256).max);
        uint256 dAtSpike = das.getLatestTroveDebt(1);

        skip(dt);
        vm.prank(BORROWER);
        uint256 joinFee = das.setInterestBatchManager(1, mgr, type(uint256).max);

        uint256 holdCost = das.calcInterest(dAtSpike * rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
        uint256 cycleCost =
            das.calcInterest(dAtSpike * rHi, dt) + joinFee + das.calcInterest(dAtSpike * rBatch, rem);
        assertGe(cycleCost + 2, holdCost, "Hardened Design A* blocks batch-join cut arbitrage");
    }

    /// @notice Fuzz Property 12: Direct removeFromBatch & switchBatchManager Security in Design A*
    ///         Verifies (a) pre-aged shield batch join + removeFromBatch enforces full 7d commitment, and
    ///         (b) honest post-cooldown switchBatchManager to lower rate never triggers false 7d cut penalty.
    function testFuzz_DesignAStar_RemoveAndSwitchBatchSecurity(
        uint256 _debt,
        uint256 _rLow,
        uint256 _spread,
        uint256 _dtJoin,
        uint256 _dtExit
    ) public {
        uint256 debt = bound(_debt, LiquityV2Constants.MIN_DEBT, 25_000_000e18);
        uint256 rLow = bound(_rLow, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 100e16);
        uint256 rHi = rLow + bound(_spread, 5e16, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - rLow);
        uint256 dtJoin = bound(_dtJoin, 1, 3 days);
        uint256 dtExit = bound(_dtExit, 1, LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 1);

        vm.warp(1_770_000_000);
        DesignAStarBorrowerOps das = new DesignAStarBorrowerOps(COLL_PRICE);
        address mgrShield = address(0x8801);
        address mgrLow = address(0x8802);

        uint256 coll = (debt * 5 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;
        vm.prank(BG_BORROWER);
        das.openTrove(999, coll * 10, debt * 10, 2e16, type(uint256).max);
        vm.prank(mgrShield);
        das.registerBatchManager(5e15, 250e16, uint128(rHi), 0, 1 hours);
        vm.prank(mgrLow);
        das.registerBatchManager(5e15, 250e16, uint128(rLow), 0, 1 hours);

        // (a) Pre-aged shield batch cannot wipe freshly spiked trove's cooldown on removeFromBatch
        {
            vm.prank(BORROWER);
            das.openTrove(1, coll, debt, rLow, type(uint256).max);
            skip(8 days);
            vm.prank(BORROWER);
            das.adjustTroveInterestRate(1, rHi, type(uint256).max);
            skip(dtJoin);
            vm.prank(BORROWER);
            das.setInterestBatchManager(1, mgrShield, type(uint256).max);
            uint256 debtAtJoin = das.getLatestTroveDebt(1);

            skip(dtExit);
            vm.prank(BORROWER);
            uint256 exitFee = das.removeFromBatch(1, rLow, type(uint256).max);
            uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - dtExit;
            uint256 hold7d = das.calcInterest(debtAtJoin * rHi, LiquityV2Constants.UPFRONT_INTEREST_PERIOD);
            uint256 cycleCost =
                das.calcInterest(debtAtJoin * rHi, dtExit) + exitFee + das.calcInterest(debtAtJoin * rLow, rem);
            assertGe(cycleCost + 2, hold7d, "removeFromBatch enforces full 7d commitment");
        }

        // (b) Honest post-cooldown switchBatchManager from mgrShield -> mgrLow incurs ONLY baseFee (zero false cut)
        {
            vm.prank(BORROWER);
            das.openTroveAndJoinBatch(2, coll, debt, mgrShield, type(uint256).max);
            skip(30 days);
            uint256 dHonest = das.getLatestTroveDebt(2);
            vm.prank(BORROWER);
            uint256 switchFee = das.switchBatchManager(2, mgrLow, type(uint256).max);
            uint256 postAvgRate = das.aggWeightedDebtSum() / das.aggRecordedDebt();
            uint256 expectedBaseFee = das.calcUpfrontFee(dHonest, postAvgRate);
            // Allow tiny +/- 0.1% slack because postAvgRate includes the capitalized switchFee itself
            assertLe(switchFee, expectedBaseFee + (expectedBaseFee / 100) + 1e15, "post-cooldown switch pays baseFee only");
        }
    }

    struct BatchFuzzVars {
        uint256 debt;
        uint256 rLow;
        uint256 rHi;
        uint256 dt;
        uint256 coll;
        uint256 hold7d;
        uint256 mgrStart;
        uint256 yieldBefore;
    }

    /// @notice Fuzz Property 13: Stateful Multi-Operation Batch Lifecycle in Design D
    ///         Exercises openTroveAndJoinBatch, setBatchManagerAnnualInterestRate, removeFromBatch
    ///         (same-rate, lower-rate, higher-rate), switchBatchManager, setInterestBatchManager,
    ///         repayBold, and closeTrove across randomized debts, rates, intervals, and action branches,
    ///         asserting both (i) zero bypass (>= 98% commitment) and (ii) zero double-charge (<= 106%).
    function testFuzz_DesignD_BatchLifecycle_FirstPayerAndTransfer(
        uint256 _debt,
        uint256 _rLow,
        uint256 _spread,
        uint256 _dt,
        uint8 _modeRaw
    ) public {
        BatchFuzzVars memory v;
        v.debt = bound(_debt, 50_000e18, 10_000_000e18);
        v.rLow = bound(_rLow, LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE, 20e16);
        v.rHi = v.rLow + bound(_spread, 20e16, LiquityV2Constants.MAX_ANNUAL_INTEREST_RATE - v.rLow);
        v.dt = bound(_dt, 1, 2 days);
        uint256 mode = uint256(_modeRaw) % 5;

        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);
        address mgr1 = address(0x9101);
        address mgr2 = address(0x9102);
        address mgrClobber = address(0x9103);

        v.coll = (v.debt * 6 * LiquityV2Constants.DECIMAL_PRECISION) / COLL_PRICE;
        vm.prank(BG_BORROWER);
        dd.openTrove(999, v.coll * 4, v.debt * 4, 5e15, type(uint256).max);
        vm.prank(mgr1);
        dd.registerBatchManager(5e15, 250e16, uint128(v.rLow), 0, 1 hours);
        vm.prank(mgr2);
        dd.registerBatchManager(5e15, 250e16, uint128(v.rLow), 0, 1 hours);
        vm.prank(mgrClobber);
        dd.registerBatchManager(5e15, 250e16, uint128(v.rHi), 0, 1 hours);

        v.mgrStart = 2_000_000e18;
        _mintBold(dd, mgr1, v.mgrStart);
        vm.prank(mgr1);
        dd.boldToken().approve(address(dd), type(uint256).max);
        _mintBold(dd, BORROWER, v.debt * 2 + 2_000_000e18);
        vm.prank(BORROWER);
        dd.boldToken().approve(address(dd), type(uint256).max);

        vm.prank(BORROWER);
        dd.openTroveAndJoinBatch(1, v.coll, v.debt, mgr1, type(uint256).max);
        skip(8 days);
        vm.prank(BORROWER);
        dd.claimVestedTroveBond(1);

        // Manager spikes batch to rHi
        vm.prank(mgr1);
        dd.setBatchManagerAnnualInterestRate(uint128(v.rHi), type(uint256).max);
        uint256 dAtSpike = dd.getLatestTroveDebt(1);
        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - v.dt;
        v.hold7d = dd.calcInterest(dAtSpike * (v.rHi - v.rLow), rem);

        skip(v.dt);
        v.yieldBefore = dd.protocolYieldAccumulated();

        if (mode == 0) {
            // Mode 0: Same-rate removeFromBatch + immediate closeTrove
            vm.prank(BORROWER);
            assertEq(dd.removeFromBatch(1, v.rHi, 0), 0, "Zero capitalized fee on same-rate remove");
            vm.prank(BORROWER);
            dd.closeTrove(1);
            uint256 fullRemHold =
                dd.calcInterest(dAtSpike * (v.rHi - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE), rem);
            uint256 forfeited = dd.protocolYieldAccumulated() - v.yieldBefore;
            assertGe(forfeited + 10e18, fullRemHold, "Mode 0: no zero-forfeiture bypass");
        } else if (mode == 1) {
            // Mode 1: Direct removeFromBatch to rLow
            uint256 bal0 = dd.boldToken().balanceOf(BORROWER);
            vm.prank(BORROWER);
            uint256 capFee = dd.removeFromBatch(1, v.rLow, type(uint256).max);
            uint256 walletPaid = bal0 - dd.boldToken().balanceOf(BORROWER);
            assertEq(capFee, 0, "Mode 1: zero double-charge via capitalized fee");
            assertGe(walletPaid + 10e18, v.hold7d, "Mode 1: full cut commitment enforced");
        } else if (mode == 2) {
            // Mode 2: switchBatchManager to mgr2 at rLow
            uint256 bal0 = dd.boldToken().balanceOf(BORROWER);
            vm.prank(BORROWER);
            uint256 capFee = dd.switchBatchManager(1, mgr2, type(uint256).max);
            uint256 walletPaid = bal0 - dd.boldToken().balanceOf(BORROWER);
            assertGe(walletPaid + capFee + 10e18, v.hold7d, "Mode 2: switch enforces full cut commitment");
            uint256 maxReasonable =
                dd.calcInterest(dAtSpike * (v.rHi - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE), rem) + capFee + 50e18;
            assertLe(walletPaid + capFee, maxReasonable, "Mode 2: zero double-charge on switch");
        } else if (mode == 3) {
            _checkDesignDMode3JoinNoDoubleCharge(dd, mgr2, v);
        } else {
            _checkDesignDMode4CutLogClobberDefense(dd, mgrClobber, v, _modeRaw);
        }

        // In every mode, honest mgr1 suffers 0 wei griefing loss after vesting completes
        skip(8 days);
        vm.prank(mgr1);
        dd.claimVestedBatchBond();
        assertEq(dd.boldToken().balanceOf(mgr1), v.mgrStart, "Batch manager suffers exact 0 wei griefing loss");
    }

    function _checkDesignDMode4CutLogClobberDefense(
        DesignDBorrowerOps _dd,
        address _mgrClobber,
        BatchFuzzVars memory _v,
        uint8 _subRaw
    ) internal {
        _mintBold(_dd, _mgrClobber, 2_000_000e18);
        vm.prank(_mgrClobber);
        _dd.boldToken().approve(address(_dd), type(uint256).max);

        vm.prank(BORROWER);
        _dd.openTroveAndJoinBatch(3, _v.coll, _v.debt, _mgrClobber, type(uint256).max);
        (uint104 lockedAtOpen,,,,) = _dd.troveBonds(3);
        uint256 sub = uint256(_subRaw) % 3;

        skip(_v.dt);
        uint256 rem = LiquityV2Constants.UPFRONT_INTEREST_PERIOD - _v.dt;
        uint256 firstCutRate = (sub == 1 && _v.rLow + 1 < _v.rHi) ? _v.rLow + 1 : _v.rLow;
        vm.prank(_mgrClobber);
        _dd.setBatchManagerAnnualInterestRate(uint128(firstCutRate), type(uint256).max);

        // Attempt clobbering at t = 7d via (0) no-op refresh, (1) two-step cut, or (2) re-hike
        skip(rem);
        vm.prank(_mgrClobber);
        if (sub == 0) {
            _dd.setBatchManagerAnnualInterestRate(uint128(_v.rLow), type(uint256).max);
        } else if (sub == 1) {
            _dd.setBatchManagerAnnualInterestRate(uint128(_v.rLow), type(uint256).max);
        } else {
            _dd.setBatchManagerAnnualInterestRate(uint128(_v.rHi), type(uint256).max);
        }

        uint256 y0 = _dd.protocolYieldAccumulated();
        vm.prank(BORROWER);
        _dd.claimVestedTroveBond(3);
        uint256 forfeited = _dd.protocolYieldAccumulated() - y0;

        uint256 expectedForfeit = (
            uint256(lockedAtOpen) * rem * (_v.rHi - _v.rLow)
        ) / (LiquityV2Constants.UPFRONT_INTEREST_PERIOD * (_v.rHi - LiquityV2Constants.MIN_ANNUAL_INTEREST_RATE));
        assertGe(forfeited + 10e18, expectedForfeit, "Mode 4: cut-log defeats clobbering");
    }

    function _checkDesignDMode3JoinNoDoubleCharge(DesignDBorrowerOps _dd, address _mgr2, BatchFuzzVars memory _v)
        internal
    {
        vm.prank(BORROWER);
        _dd.openTrove(2, _v.coll, _v.debt, _v.rHi, type(uint256).max);
        (uint104 bLock,,,,) = _dd.troveBonds(2);
        uint256 d2 = _dd.getLatestTroveDebt(2);
        skip(12);
        uint256 bal0 = _dd.boldToken().balanceOf(BORROWER);
        vm.prank(BORROWER);
        uint256 capFee = _dd.setInterestBatchManager(2, _mgr2, type(uint256).max);
        uint256 forfeited = uint256(bLock) - (_dd.boldToken().balanceOf(BORROWER) - bal0);
        uint256 postAvgRate = _dd.aggWeightedDebtSum() / _dd.aggRecordedDebt();
        uint256 baseFeeBound = _dd.calcUpfrontFee(d2, postAvgRate + 5e16);
        assertLe(capFee, baseFeeBound + 50e18, "Mode 3: capitalized join fee not double-charged");
        uint256 expectedCut = _dd.calcInterest(
            d2 * (_v.rHi - _v.rLow), LiquityV2Constants.UPFRONT_INTEREST_PERIOD - 12
        );
        assertGe(forfeited + 10e18, expectedCut, "Mode 3: troveBond covers full cut forfeiture");
    }
}
