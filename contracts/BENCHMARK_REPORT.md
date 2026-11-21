# Liquity V2 Solidity 0.8.24 Storage, Gas, and Security Benchmark Report

## Toolchain and Build Verification

All contracts and test suites compile under Foundry (`forge Version: 1.10.0`) with pinned Solidity `0.8.24`, EVM target `shanghai`, optimizer enabled (`200` runs), and `forge build --deny warnings` exiting `0` with zero compiler errors and zero warnings. The upstream patch `src/LiquityV2FeePatch.diff` applies cleanly (`patch --dry-run` exit `0`) against deployed `WETH_BorrowerOperations.sol` across `adjustTroveInterestRate`, `setBatchManagerAnnualInterestRate`, `setInterestBatchManager`, `switchBatchManager`, and `_removeFromBatch`.

## EVM Storage-Layout Verification

Each mechanism inherits the identical 11-slot `LiquityV2CoreBase` storage state (`slots 0..10`), allowing exact compiler-level diffing via `forge inspect <Contract> storage-layout --json`.

| Contract | Total Slots | Delta vs. StatusQuo | Byte-for-Byte Identical | Runtime Size (B, EIP-170 <= 24,576) | Initcode Size (B) | Deployment Gas |
|---|---:|---:|---|---:|---:|---:|
| `StatusQuoBorrowerOps` | 11 | 0 | Yes | 14,523 | 17,114 | 3,658,237 |
| `DesignABorrowerOps` | 11 | 0 | Yes | 14,561 | 17,152 | 3,666,451 |
| `DesignAStarBorrowerOps` | 11 | 0 | Yes | 15,009 | 17,600 | 3,763,380 |
| `DesignDBorrowerOps` | 14 | +3 | No (+3 mapping slots) | 22,767 | 25,379 | 5,440,260 |
| `CoPayBorrowerOps` | 11 | 0 | Yes | 15,463 | 18,264 | 3,861,764 |

`DesignAStarBorrowerOps`, `DesignABorrowerOps`, and `CoPayBorrowerOps` add exactly 0 storage slots relative to `StatusQuoBorrowerOps`. `DesignDBorrowerOps` adds exactly 3 mapping base slots (`troveBonds` at slot 11, `batchBonds` at slot 12, and `batchCuts` at slot 13). Its `RateBond` struct packs five fields (`uint104 lockedBond` at byte 0, `uint64 highWaterRate` at byte 13, `uint40 lastUpdateTime` at byte 21, `uint24 remainingTime` at byte 26, `uint24 startCutIdx` at byte 29) into exactly 32 bytes (1 single 256-bit EVM slot per active trove or batch, zero padding waste). Its append-only `CutEvent` record packs three fields (`uint64 newRate`, `uint40 cutTime`, `uint40 coveredBefore`) into 32 bytes (1 slot per downward batch cut), closing lazy-sync timestamp clobbering across no-op refreshes, multi-step cuts, re-hikes, and same-block atomic opens.

## Isolated EVM Gas Benchmarks

The table below reports isolated `gasleft()` execution costs measured on identical warm branch state (`10M BOLD` background trove plus `5M BOLD` target trove and batch, `$2,500` collateral price).

| Operation | StatusQuo | DesignA | DesignA* | DesignD | CoPay (50%, A*) | Delta (A* vs. SQ) | Delta (D vs. SQ) |
|---|---:|---:|---:|---:|---:|---:|---:|
| openTrove (solo, 2.0% APR) | 245,792 | 245,792 | 245,792 | 282,301 | 245,792 | 0 | +36,509 |
| setBatchManagerAnnualInterestRate (post-cooldown hike 2% -> 10%) | 118,617 | 118,617 | 118,595 | 164,933 | 121,120 | -22 | +46,316 |
| setBatchManagerAnnualInterestRate (premature hike 10% -> 12%, 1h) | 109,403 | 107,377 | 107,466 | 129,483 | 149,509 | -1,937 | +20,080 |
| setBatchManagerAnnualInterestRate (premature cut 12% -> 2%, 1h) | 109,391 | 109,416 | 107,528 | 183,953 | 146,782 | -1,863 | +74,562 |
| adjustTroveInterestRate (premature solo hike 10% -> 12%, 1h) | 95,183 | 93,157 | 93,356 | 113,225 | 93,232 | -1,827 | +18,042 |
| adjustTroveInterestRate (premature solo cut 12% -> 2%, 1h) | 95,170 | 95,195 | 93,417 | 122,626 | 93,305 | -1,753 | +27,456 |
| repayBold (partial repayment 12s after hike) | 91,546 | 91,546 | 91,546 | 116,256 | 91,546 | 0 | +24,710 |
| closeTrove (post-cooldown honest exit) | 103,382 | 103,382 | 103,382 | 120,421 | 103,382 | 0 | +17,039 |
| closeTrove (premature exit 24s after hike) | 103,382 | 103,382 | 103,382 | 126,292 | 103,382 | 0 | +22,910 |

`DesignAStarBorrowerOps` reduces gas on every premature adjustment (-1,937 gas on premature batch hikes, -1,827 gas on premature solo hikes, -1,863 gas on premature batch cuts, -1,753 gas on premature solo cuts, and -22 gas on post-cooldown batch hikes) while adding 0 gas on `openTrove`, `repayBold`, and `closeTrove`. The savings come from removing the `getNewApproxAvgInterestRateFromTroveChange` aggregate branch-rate lookup; on mainnet where `ActivePool` is a separate contract, skipping that external `STATICCALL` yields further savings. `DesignDBorrowerOps` quantifies the on-chain cost of blocking flash-loan close-and-reopen exits: +36,509 gas on `openTrove` above `MIN_ANNUAL_INTEREST_RATE`, +46,316 gas on post-cooldown hikes (cold escrow slot write plus ERC20 deposit), +20,080 to +74,562 gas on premature batch adjustments, +24,710 gas on premature `repayBold`, and +17,039 to +22,910 gas on `closeTrove`. Every contract in this self-contained benchmark sits below the 24,576-byte EIP-170 runtime bytecode ceiling, including `DesignDBorrowerOps` at `22,767` runtime bytes (1,809 bytes of EIP-170 headroom; `25,379` initcode bytes vs. 49,152-byte EIP-3860 limit).

## Mainnet Integration Notes (Rounding and Yield Routing)

1. Rounding semantics (`floor` vs. overflow-safe `ceilDiv`): `src/LiquityV2FeePatch.diff` uses Liquity V2's verbatim floored `_calcInterest` primitive (exact worst-case 7-day spike-and-cut floor residual of at most 2 wei), whereas `calcInterestCeil` in `LiquityV2CoreBase` and escrow forfeitures in `DesignDBorrowerOps` use overflow-safe `(num - 1) / denom + 1` ceiling division (0 wei cut-numerator shortfall and at most 1 wei total 7-day hold residual; `quoteDesignAStarCeilZeroShortfall` adds +1 wei on positive premature cuts for 0 wei total hold residual). 2. Cooldown clock parity: `LiquityV2CoreBase` and `src/LiquityV2FeePatch.diff` match deployed Liquity V2 `TroveManager.sol` verbatim (`onSetInterestBatchManager` and `onRemoveFromBatch` stamp `block.timestamp`, and `_getLatestTroveData` returns `max(batch.lastInterestRateAdjTime, trove.lastInterestRateAdjTime)`), while `switchBatchManager` captures pre-removal `oldTrove.lastInterestRateAdjTime` before invoking `removeFromBatch` so honest post-cooldown batch switches incur zero false cut penalties. 3. Yield routing vs. standalone burn accounting: in the isolated single-contract benchmark, direct co-pay pulls in `CoPayBorrowerOps` and forfeited rate-bond escrow in `DesignDBorrowerOps` call `boldToken.burn(address(this), ...)` while incrementing `protocolYieldAccumulated`. In production Liquity V2 (`ActivePool.sol` L253-261), those BOLD inflows route directly to `stabilityPool` and `interestRouter` instead of burning without reducing `aggRecordedDebt`, preserving the protocol-wide invariant `BOLD.totalSupply == totalSystemDebt`.

## Deterministic Mainnet Exploit and Defense Reproductions

All 25 deterministic tests in `test/ExploitReproductions.t.sol` pass. Mainnet spike-and-cut traces reproduce the 2026-03-06 `wstETH` (`D = 7,981,691 BOLD`, 0.70% -> 10.50% -> 0.70%, `dt = 3,636s`, `rbar = 1.507%`) and `WETH` (`D = 1,786,273 BOLD`, 3.10% -> 13.10% -> 3.30%, `dt = 3,636s`, `rbar = 3.767%`) episodes.

| Scenario | StatusQuo | DesignA | DesignA* | DesignD | Key Finding |
|---|---:|---:|---:|---:|---|
| Mainnet 2026-03-06 wstETH spike-and-cut (cut cost, BOLD) | 2,306.64 | 2,306.64 | 14,917.16 | 14,916.98 | SQ and DesignA give 84.62% discount vs. 15,007.20 BOLD 7d hold; A* and D enforce 0% arbitrage |
| Mainnet 2026-03-06 WETH spike-and-cut (cut cost, BOLD) | 1,290.60 | 1,290.60 | 3,341.96 | 3,341.90 | SQ and DesignA give 61.61% discount vs. 3,362.12 BOLD 7d hold; A* and D enforce 0% arbitrage |
| 5-step +20 bp premature staircase (5M BOLD, total fees) | 13,284.87 | 959.47 | 959.47 | 0.00 (honest 7d) | SQ inflates fees by 13.85x; A* stays within <= 4 wei of single jump |
| Flash-loan close+reopen (5M BOLD, 1% -> 15%, 12s, 5 bps) | Bypassed | Bypassed | 5,219.47 (bypassed) | 19,131.24 (blocked) | A* bypassed by 63.73% vs. 14,391.77 BOLD hold; D forfeits 13,911.77 BOLD and refunds 13,912.05 BOLD (100%) on honest 7d hold |
| Zero-flash-loan batch-join / switch bypass (5M BOLD, 250% -> 0.5%, 12s) | 1,787.16 (bypassed) | 1,787.16 (bypassed) | 239,353.79 (blocked) | Blocked | Hardened Design A* closes setInterestBatchManager and switchBatchManager (>98% bypass in SQ) |
| Dormant 2,000 BOLD shield at 250% (30d) + withdrawBold(+10M) + close(1h) | Bypassed | Bypassed | Bypassed | 479,706.69 forfeited | Design D locks 482,579.19 BOLD on withdrawBold at any elapsed time |
| Partial repayBold (99.96% to MIN_DEBT, 12s after 20% hike) | No escrow | No escrow | No escrow | 18,701.46 forfeited | Zero-dilution pro-rata forfeiture blocks partial debt reduction bypass |
| Fresh openTrove(250%) + closeTrove after 1h (5M BOLD) | Bypassed | Bypassed | Bypassed | 239,798.31 forfeited | Initial rate-bond lock closes high-rate fresh-open escrow dodge; 100% refund on honest 7d hold |

Additional deterministic security tests in `test/ExploitReproductions.t.sol` verify six protocol invariants: (1) rogue borrower exits from a hiked batch pay their own early-exit forfeiture while the honest batch manager recovers 100% of their locked slice with 0 wei griefing loss; (2) a 10M BOLD trove at 250% APR cut to 249% after 3.5 days incurs zero underflow under scale-invariant pure-cut forfeiture; (3) `CoPayBorrowerOps` excludes upfront fees from the management-fee base and pulls any co-pay shortfall directly from the manager even after flushing `batchAccruedManagementFee` to 0; (4) pre-aged shield batches cannot reset a freshly spiked trove's cooldown clock under `DesignAStarBorrowerOps`, while honest post-cooldown batch switches incur zero false cut penalty; (5) First-Payer Netting and same-rate/partial-cut bond transfer in `DesignDBorrowerOps` enforce exact 100% single forfeiture across `setInterestBatchManager`, `removeFromBatch`, `switchBatchManager`, and cross-borrower exits with zero bypass, zero double-charge, zero batch-bond drain, and zero manager griefing; and (6) immutable `batchCuts` replay in `DesignDBorrowerOps` defeats no-op refreshes, two-step downward cuts, re-hikes at t=30d, and same-block atomic open-and-cut or post-hike sandwich joins while preserving 100% honest late refunds (t=30d after an 8d cut) and zero pre-hike double-forfeiture.

## Randomized Differential Fuzzing Summary

13 independent fuzz invariants in `test/DifferentialFuzz.t.sol` execute under both the default profile (`32,500` total runs, 2,500 per property) and the intense profile (`130,000` total runs, 10,000 per property) with 0 failures and fixed seed `0x4c6971756974795632`.

| Fuzz Property | Default Runs | Intense Runs | Intense Mean Gas | Result |
|---|---:|---:|---:|---|
| `testFuzz_DesignAStar_BatchJoinNoArbitrage` | 2,500 | 10,000 | 4,633,666 | PASS |
| `testFuzz_DesignAStar_RemoveAndSwitchBatchSecurity` | 2,500 | 10,000 | 5,802,427 | PASS |
| `testFuzz_DesignD_BatchLifecycle_FirstPayerAndTransfer` | 2,500 | 10,000 | 7,531,564 | PASS |
| `testFuzz_DesignD_DormantShieldWithdrawBoldSecurity` | 2,500 | 10,000 | 6,360,134 | PASS |
| `testFuzz_DesignD_FlashLoanCloseAndReopenSecurity` | 2,500 | 10,000 | 6,907,919 | PASS |
| `testFuzz_DesignD_HonestHoldZeroPenalty` | 2,500 | 10,000 | 6,226,208 | PASS |
| `testFuzz_DesignD_InPlaceCutMatchesHoldCommitment` | 2,500 | 10,000 | 6,362,140 | PASS |
| `testFuzz_DesignD_PartialRepayBlocksBypass` | 2,500 | 10,000 | 6,435,964 | PASS |
| `testFuzz_DustAndMaxDebtOverflowBounds` | 2,500 | 10,000 | 17,303 | PASS |
| `testFuzz_MultiStepCutSuperadditivity` | 2,500 | 10,000 | 45,897 | PASS |
| `testFuzz_SpikeAndCutNoArbitrage_FloorAndCeil` | 2,500 | 10,000 | 38,776 | PASS |
| `testFuzz_StaircasePathInvariance` | 2,500 | 10,000 | 31,391 | PASS |
| `testFuzz_SybilDebtSplitNeutrality` | 2,500 | 10,000 | 21,683 | PASS |

During stateful fuzzing of `testFuzz_DesignD_PartialRepayBlocksBypass`, the fuzzer identified a subtle high-APR compounding dilution in naive ratio-based forfeiture (`unvested * repayAmount / debtBefore`) when `debtBefore` includes accrued interest at up to 250% APR. Replacing that ratio with `min(unvested, calcInterestCeil(repayAmount * (highWaterRate - MIN_ANNUAL_INTEREST_RATE), remainingTime))` using the fields already packed inside the 1-slot `RateBond` struct eliminated the dilution across all 10,000 randomized fuzz runs.
