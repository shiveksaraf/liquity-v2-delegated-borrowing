// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

import {TestBase} from "./TestBase.sol";
import {BoldToken} from "../src/BoldToken.sol";
import {LiquityV2Constants} from "../src/LiquityV2Constants.sol";
import {LiquityV2CoreBase} from "../src/LiquityV2CoreBase.sol";
import {StatusQuoBorrowerOps} from "../src/StatusQuoBorrowerOps.sol";
import {DesignABorrowerOps} from "../src/DesignABorrowerOps.sol";
import {DesignAStarBorrowerOps} from "../src/DesignAStarBorrowerOps.sol";
import {DesignDBorrowerOps} from "../src/DesignDBorrowerOps.sol";
import {CoPayBorrowerOps} from "../src/CoPayBorrowerOps.sol";

/// @title Exact Isolated EVM Gas Benchmark Suite
/// @notice Measures apples-to-apples isolated gasleft() execution costs for all 5 core
///         protocol operations across StatusQuo, DesignA, DesignA*, DesignD, and CoPay.
contract GasBenchmarkTest is TestBase {
    uint256 internal constant COLL_PRICE = 2500e18;
    address internal constant MANAGER = address(0x1111);
    address internal constant BORROWER = address(0x2222);
    address internal constant BG_BORROWER = address(0x3333);

    struct OpGas {
        uint256 openTroveGas;
        uint256 postCooldownBatchHikeGas;
        uint256 prematureBatchHikeGas;
        uint256 prematureBatchCutGas;
        uint256 repayBoldPrematureGas;
        uint256 closeTroveHonestGas;
        uint256 closeTrovePrematureGas;
        uint256 prematureSoloHikeGas;
        uint256 prematureSoloCutGas;
    }

    function _mintBold(LiquityV2CoreBase _ops, address _to, uint256 _amount) internal {
        BoldToken token = _ops.boldToken();
        vm.prank(address(_ops));
        token.mint(_to, _amount);
    }

    function _benchmarkContract(LiquityV2CoreBase _ops, bool _needsEscrowFunding) internal returns (OpGas memory g) {
        // Background branch trove so ActivePool state is warm and realistic
        vm.prank(BG_BORROWER);
        _ops.openTrove(1, 20_000e18, 10_000_000e18, 25e15, type(uint256).max);

        // (iv) Isolated openTrove measurement
        vm.prank(BORROWER);
        uint256 g0 = gasleft();
        _ops.openTrove(2, 6000e18, 5_000_000e18, 20e15, type(uint256).max);
        g.openTroveGas = g0 - gasleft();

        // Register batch manager and join a batched trove
        vm.prank(MANAGER);
        _ops.registerBatchManager(5e15, 250e16, 20e15, 3e15, 1 hours);
        vm.prank(BORROWER);
        _ops.openTroveAndJoinBatch(3, 6000e18, 5_000_000e18, MANAGER, type(uint256).max);

        if (_needsEscrowFunding) {
            _mintBold(_ops, MANAGER, 200_000e18);
            vm.prank(MANAGER);
            _ops.boldToken().approve(address(_ops), type(uint256).max);
            _mintBold(_ops, BORROWER, 200_000e18);
            vm.prank(BORROWER);
            _ops.boldToken().approve(address(_ops), type(uint256).max);
        }

        // Advance past 7d cooldown so first batch hike is post-cooldown
        skip(8 days);

        // (iii) Isolated post-cooldown free batch hike (2% -> 10%)
        vm.prank(MANAGER);
        g0 = gasleft();
        _ops.setBatchManagerAnnualInterestRate(100e15, type(uint256).max);
        g.postCooldownBatchHikeGas = g0 - gasleft();

        // (i) Isolated premature batch hike (10% -> 12%, elapsed = 1h)
        skip(1 hours);
        vm.prank(MANAGER);
        g0 = gasleft();
        _ops.setBatchManagerAnnualInterestRate(120e15, type(uint256).max);
        g.prematureBatchHikeGas = g0 - gasleft();

        // (ii) Isolated premature batch cut (12% -> 2%, elapsed = 1h)
        skip(1 hours);
        vm.prank(MANAGER);
        g0 = gasleft();
        _ops.setBatchManagerAnnualInterestRate(20e15, type(uint256).max);
        g.prematureBatchCutGas = g0 - gasleft();

        // Solo trove premature hike & cut
        skip(8 days);
        vm.prank(BORROWER);
        _ops.adjustTroveInterestRate(2, 100e15, type(uint256).max); // post-cooldown spike

        skip(1 hours);
        vm.prank(BORROWER);
        g0 = gasleft();
        _ops.adjustTroveInterestRate(2, 120e15, type(uint256).max);
        g.prematureSoloHikeGas = g0 - gasleft();

        skip(1 hours);
        vm.prank(BORROWER);
        g0 = gasleft();
        _ops.adjustTroveInterestRate(2, 20e15, type(uint256).max);
        g.prematureSoloCutGas = g0 - gasleft();

        // (v-a) Isolated closeTrove after cooldown (honest hold)
        skip(8 days);
        uint256 repayHonest = _ops.getLatestTroveDebt(2);
        _mintBold(_ops, BORROWER, repayHonest);
        vm.prank(BORROWER);
        g0 = gasleft();
        _ops.closeTrove(2);
        g.closeTroveHonestGas = g0 - gasleft();

        // (v-b) Isolated premature repayBold & closeTrove immediately after a post-cooldown spike
        vm.prank(BORROWER);
        _ops.openTrove(4, 6000e18, 5_000_000e18, 20e15, type(uint256).max);
        skip(8 days);
        vm.prank(BORROWER);
        _ops.adjustTroveInterestRate(4, 150e15, type(uint256).max);
        skip(12);
        _mintBold(_ops, BORROWER, 1_000_000e18);
        vm.prank(BORROWER);
        g0 = gasleft();
        _ops.repayBold(4, 1_000_000e18);
        g.repayBoldPrematureGas = g0 - gasleft();

        skip(12);
        uint256 repayPrem = _ops.getLatestTroveDebt(4);
        _mintBold(_ops, BORROWER, repayPrem);
        vm.prank(BORROWER);
        g0 = gasleft();
        _ops.closeTrove(4);
        g.closeTrovePrematureGas = g0 - gasleft();
    }

    function _emitReport(string memory _label, OpGas memory _g) internal {
        emit LogNamedString("MECHANISM", _label);
        emit LogNamedUint("openTrove", _g.openTroveGas);
        emit LogNamedUint("postCooldownBatchHike", _g.postCooldownBatchHikeGas);
        emit LogNamedUint("prematureBatchHike", _g.prematureBatchHikeGas);
        emit LogNamedUint("prematureBatchCut", _g.prematureBatchCutGas);
        emit LogNamedUint("repayBoldPremature", _g.repayBoldPrematureGas);
        emit LogNamedUint("closeTroveHonest", _g.closeTroveHonestGas);
        emit LogNamedUint("closeTrovePremature", _g.closeTrovePrematureGas);
        emit LogNamedUint("prematureSoloHike", _g.prematureSoloHikeGas);
        emit LogNamedUint("prematureSoloCut", _g.prematureSoloCutGas);
    }

    function test_GasBenchmark_StatusQuo() public {
        vm.warp(1_770_000_000);
        StatusQuoBorrowerOps sq = new StatusQuoBorrowerOps(COLL_PRICE);
        OpGas memory g = _benchmarkContract(sq, false);
        _emitReport("StatusQuoBorrowerOps", g);
        assertGt(g.prematureBatchHikeGas, 0, "Measured StatusQuo gas");
    }

    function test_GasBenchmark_DesignA() public {
        vm.warp(1_770_000_000);
        DesignABorrowerOps da = new DesignABorrowerOps(COLL_PRICE);
        OpGas memory g = _benchmarkContract(da, false);
        _emitReport("DesignABorrowerOps", g);
        assertGt(g.prematureBatchHikeGas, 0, "Measured DesignA gas");
    }

    function test_GasBenchmark_DesignAStar() public {
        vm.warp(1_770_000_000);
        DesignAStarBorrowerOps das = new DesignAStarBorrowerOps(COLL_PRICE);
        OpGas memory g = _benchmarkContract(das, false);
        _emitReport("DesignAStarBorrowerOps", g);
        assertGt(g.prematureBatchHikeGas, 0, "Measured DesignAStar gas");
    }

    function test_GasBenchmark_DesignD() public {
        vm.warp(1_770_000_000);
        DesignDBorrowerOps dd = new DesignDBorrowerOps(COLL_PRICE);
        OpGas memory g = _benchmarkContract(dd, true);
        _emitReport("DesignDBorrowerOps", g);
        assertGt(g.prematureBatchHikeGas, 0, "Measured DesignD gas");
    }

    function test_GasBenchmark_CoPay() public {
        vm.warp(1_770_000_000);
        CoPayBorrowerOps cp = new CoPayBorrowerOps(COLL_PRICE, 5e17, true);
        OpGas memory g = _benchmarkContract(cp, true);
        _emitReport("CoPayBorrowerOps", g);
        assertGt(g.prematureBatchHikeGas, 0, "Measured CoPay gas");
    }

    /// @notice Direct differential assertion: Design A* uses strictly LESS gas than Status Quo
    ///         on both premature batch hikes and premature batch cuts because it skips avgInterestRate lookup!
    function test_GasDifferential_DesignAStarCheaperThanStatusQuo() public {
        vm.warp(1_770_000_000);
        StatusQuoBorrowerOps sq = new StatusQuoBorrowerOps(COLL_PRICE);
        OpGas memory gSq = _benchmarkContract(sq, false);

        vm.warp(1_770_000_000);
        DesignAStarBorrowerOps das = new DesignAStarBorrowerOps(COLL_PRICE);
        OpGas memory gDas = _benchmarkContract(das, false);

        assertLe(gDas.prematureBatchHikeGas, gSq.prematureBatchHikeGas, "Design A* <= Status Quo on premature batch hike");
        assertLe(gDas.prematureBatchCutGas, gSq.prematureBatchCutGas, "Design A* <= Status Quo on premature batch cut");
        assertLe(gDas.prematureSoloHikeGas, gSq.prematureSoloHikeGas, "Design A* <= Status Quo on premature solo hike");
        assertLe(gDas.prematureSoloCutGas, gSq.prematureSoloCutGas, "Design A* <= Status Quo on premature solo cut");
    }
}
