# Liquity V2 empirical finance and structural econometrics master summary

Generated UTC: `2026-11-23T17:16:30Z`. Master JSON SHA-256: `ee72b28247f0a7d6`.
Every observation originates from verified canonical Ethereum mainnet logs (44,907 events across 11,444 transactions from 2025-05-19 through 2026-09-15), live Ethereum RPC `eth_call` queries, and public DefiLlama and Curve API snapshots archived with SHA-256 receipts under `empirical/data_external/SHA256_RECEIPTS.json` (20 raw files plus 2 derived CSVs). All empirical modules preserve Development (`408` days, `2025-05-19` to `2026-06-30`), Confirmation (`77` days, `2026-07-01` to `2026-09-15`), and Pooled (`485` days) splits with zero forward boundary leakage.

## 1. Live external data augmentation and on-chain permissions (Module 0)

Live `eth_call` queries to `getInterestBatchManager(address)` across the three canonical `BorrowerOperations` contracts at block `26478046` recovered all `37` immutable `(minInterestRate, maxInterestRate, minInterestRateChangePeriod)` tuples across all 23 observed batch manager addresses. Twelve manager-branch registrations hardcode the 7-day cooldown (`604,800` seconds) as their minimum change period and incurred `$0.00` (`0` premature hikes across `395` changed updates). Sixteen registrations at the 1-hour floor (`3,600` or `3,601` seconds) generated `$402,069.42` BOLD (`95.3%` of all `$421,986.60` borrower repricing fees across `724` changed updates), while nine registrations at 24 hours (`86,400` seconds) generated `$19,917.18` BOLD (`4.7%` across `521` changed updates).

Market prices from DefiLlama cover `485/485` sample days for `WETH`, `wstETH`, `rETH`, `LUSD`, `DAI`, `USDS`, `crvUSD`, and `GHO`, and `477/485` days for `BOLD` (beginning 2025-05-27). Mainnet archive `eth_call` queries achieved `497/497` (`71/71` complete weekly blocks, zero missing observations) across Sky/MakerDAO (`ETH-A` mean APY `7.880%`, `WSTETH-A` mean APY `8.880%`, `Jug.base = 0`), Aave V3 (`GHO` base borrow APR `4.538%` prior to `stkAAVE`/Merit discounts, `USDC` variable borrow APR `5.295%`), and Liquity V1 (`0.000%` recurring APR plus `0.526%` mean one-time minting fee). Official Curve daily snapshots (`485` days) recovered `crvUSD` nominal borrow APRs (`WETH` `5.684%`, `wstETH` `6.364%`). Across DefiLlama, `9` verified Liquity V2 and licensed friendly-fork deployments (`Liquity V2`, `Felix CDP`, `Asymmetry USDaf`, `Enosys Loans`, `Nerite`, `Orki Finance`, `Ebisu V2`, `DeFi Dollar`, `Quill Finance`) reached a simultaneous cross-protocol peak TVL of `$425.06M` on `2025-07-14` (`$524.57M` cumulative sum of non-simultaneous individual peaks; `$81.86M` current TVL).

## 2. Cooldown notch bunching at 168 hours and dominated-region agency analysis (Module 1)

Conditioning on live RPC manager permissions reveals that `260/321` (`81.0%`) of the raw zero-debt `[168h,169h)` spike originates from managers hardcoded to `minInterestRateChangePeriod = 604,800` seconds (smart-contract revert walls rather than fee avoidance). Restricting the primary economic-notch sample strictly to `minInterestRateChangePeriod < 604,800` seconds (`1h` and `24h` managers facing the fee notch) preserves strong cut bunching and hike-vs-cut asymmetry.

| Group and permission subsample | Sample | N | Premature (%) | [120h,168h) | [168h,169h) (%) | b_post_1h (95% boot CI) | KW poly b_4h (p=3) |
|---|---|---:|---:|---:|---:|---:|---:|
| Delegated cuts (debt > 0, minP < 7d) | Development | 73 | 8.2% | 0 | 15 (20.5%) | 90.6 ([42.5, 173.3]) | 201.9 |
| Delegated cuts (debt > 0, minP < 7d) | Confirmation | 17 | 5.9% | 0 | 5 (29.4%) | 95.7 | 108.9 |
| Delegated cuts (debt > 0, minP < 7d) | Pooled | 90 | 7.8% | 0 | 20 (22.2%) | 91.8 ([45.4, 153.7]) | 177.1 |
| Delegated hikes (debt > 0, minP < 7d) | Pooled | 526 | 65.6% | 46 | 41 (7.8%) | 72.2 ([40.3, 117.8]) | 58.7 |
| Delegated cuts (1h-only, minP <= 3,601s) | Pooled | 59 | 11.9% | 0 | 7 (11.9%) | 46.8 | 138.9 |
| Delegated hikes (1h-only, minP <= 3,601s) | Pooled | 347 | 65.4% | 30 | 16 (4.6%) | 38.5 | 30.2 |
| Zero-debt 1h-only keeper baseline | Pooled | 318 | 80.5% | 13 | 10 (3.1%) | 49.4 | 68.2 |
| Hardcoded 604,800s revert wall (zero debt) | Pooled | 384 | 0.0% | 0 | 260 (67.7%) | 537.6 | 731.8 |
| Self-managed individual cuts | Pooled | 156 | 6.4% | 1 | 2 (1.3%) | 5.4 | 19.5 |
| Self-managed individual hikes | Pooled | 666 | 29.3% | 25 | 26 (3.9%) | 21.2 | 21.0 |

Within `minInterestRateChangePeriod < 604,800` seconds, delegated positive-debt hikes break the 7-day cooldown `+57.8` percentage points more frequently than delegated positive-debt cuts (Fisher exact `p = 2.00e-26`) and `+36.3` percentage points more frequently than self-managed individual hikes (`p = 2.92e-36`). Inside `[164h, 168h)`, managers executed `8` paid premature hikes costing `11,979.39` BOLD (`0/8` constrained by `maxInterestRate`; `4/8` accounting for `$10,567.89` had zero pre-hike redemptions in `[-6h, 0]`, including `M05` on `wstETH` paying `1,332.0` BOLD `3.2` minutes before free inside the `[0.8%, 71.7%]` tied queue block with zero pre-6h redemptions, `M04` on `wstETH` paying `1,387.3` BOLD for a `+1` bp step `179.6` minutes before free at buffered queue interval `[62.5%, 67.6%]`, and `M01` on `wstETH` paying `9,207.2` BOLD `220.4` minutes before free at `[14.5%, 47.5%]` with zero pre-6h redemptions). Capitalizing upfront fees into `newDebt` mechanically expanded manager annual fee bases by `+1,159.82` BOLD per year from premature hikes alone (`+1,191.72` BOLD per year across all paid batch updates including premature cuts).

## 3. Mainnet spike-and-cut forensics and mechanism comparison (Module 2)

Scanning all 1,712 batch updates identifies `5` premature spike-and-cut episodes (`2` profitable under Status Quo, `3` profitable under prior baseline Design A, and `0` profitable under both `Design A*` and hardened 1-slot `Design D`). On `2026-03-06` (`15:50:47` to `16:51:23` UTC, elapsed `1.01` hours), `M01` on `wstETH` (`7.98M` BOLD) spiked from `0.70%` to `10.50%` and reversed back to `0.70%` at a `84.02%` total-excess discount (`84.53%` cut-fee vs remaining hold; `84.62%` cut-fee vs 7-day hold), while `M03` on `WETH` (`1.79M` BOLD) reversed `3.10%` to `13.10%` to `3.30%` at a `60.96%` total-excess discount (`61.33%` vs remaining hold; `61.56%` vs 7-day hold). Both `Design A*` and hardened `Design D` reduce the arbitrage discount to `0.000%`. Replay of hardened 1-slot `Design D` incurs `0` escrow underflows across all 1,712 mainnet updates (versus `3` underflows under the deprecated high-water rule). Replaying pre-operation trove snapshots (`rep.pending`) plus `BatchUpdated` hikes across all `op in {7, 8, 9}` transitions identifies `64` rate-lowering batch transitions and `17` within 7 days of a prior hike (`2` post-`op=3`, `7` post-`op=0`, `8` post-`BatchUpdated`), with `0` profitable bypasses observed (closest at `-0.58%`).

| Sample | Status Quo (BOLD) | Baseline Design A (BOLD) | Design A* (BOLD, % saved) | Hardened Design D Forfeit + 5% Opp (BOLD, % saved) |
|---|---:|---:|---:|---:|
| Development (408d) | 318,054.00 | 34,837.53 | 50,218.68 (-84.2%) | 21,377.67 (-93.3%) |
| Confirmation (77d) | 103,932.60 | 17,023.85 | 18,208.60 (-82.5%) | 5,949.23 (-94.3%) |
| Pooled (485d) | 421,986.60 | 51,861.37 | 68,427.29 (-83.8%) | 27,326.90 (-93.5%) |

Across all `308` paid staircase hikes, the median step is `20.0` bp (IQR `[10.0, 30.0]` bp) at median elapsed time `41.22` hours, yielding a median Status Quo to `Design A*` overcharge ratio of `20.79x` (`10.99x` dollar-weighted).

## 4. Causal identification via CollateralRegistry mechanical routing (Module 3)

Of `1709` canonical redemption transactions, `1708` (`1223` across all three branches and `485` across two) expose exact unbacked-debt routing shares offline. All forward shifts and leads are computed strictly inside each sample after splitting Development and Confirmation.

In the loan-day panel with `Trove FE + Branch x Day FE`, delegated troves hike differentially with branch routing share in Development (`+95.87` bp, `SE = 27.90`, `p = 0.0006`, `N = 72,070`) and Pooled (`+60.45` bp, `p = 0.0978`, `N = 85,677`), while the 77-day Confirmation holdout has limited cross-branch routing variation and wide standard errors (`+34.84` bp, `SE = 166.04`, `p = 0.8338`; equal-weighted `-106.65` bp, `p = 0.1536`). Using predetermined lagged 7-day routing share (`Delegated x s_lag7`) strengthens identification against contemporaneous endogeneity (`+110.04` bp, `p = 0.0004` Dev; `+64.61` bp, `p = 0.6494` Conf; `+73.06` bp, `p = 0.0378` Pooled).

In Panel A (`Branch FE + Day FE`, exact FE degrees-of-freedom adjusted 2SLS), predetermined Bartik shift-share instruments deliver strong first stages (`F = 150.0` Dev, `F = 41.1` Conf, `F = 197.7` Pooled). Dollar-weighted 48-hour upfront fee responses are `+10.53` (`SE = 6.96`, `p = 0.1303`) in Development, `+20.34` (`SE = 12.19`, `p = 0.0954`) in Confirmation, and `+13.53` Pooled (`FE-DOF day-cl SE = 6.41`, `p = 0.0347`; `Driscoll-Kraay L=2 SE = 7.74`, `p = 0.0810`; `14d block-bootstrap 95% CI = [+2.78, +35.02]`). Matched Wald-scaled future placebo leads (`t+7d`: `+3.58`, `p = 0.664`) are null. Non-overlapping 24-hour `fee_mdd` (`+4.76`, `p = 0.231`), unweighted count 2SLS outcomes, and external shock IVs (`z_depeg` `F = 9.4`, `z_vol` `F = 0.76`) lack statistical power; causal fee effects therefore operate primarily through heavy-debt multi-day bursts. In Panel B (`All-21 Positive-Debt Managers`, `Manager x Branch FE + Day FE`, `N = 5,061`, `F = 241.1`), FE-DOF 2SLS yields `+23.11` Dev (`p_t = 0.148`), `+24.44` Conf (`p_norm = 0.0369`, `p_t = 0.0522`), and `+29.71` Pooled (`p_norm = 0.0522`, `p_t = 0.0616`). An exploratory positive-debt-only `Manager x Day FE` check (`N = 1,041`, only `M08` and `M10` active across all three branches) finds positive OLS (`+2.45` pp, `p = 0.154`) and null Bartik 2SLS (`+1.39` pp, `p = 0.400`).

## 5. Multivariate Hawkes cross-manager leapfrogging (Module 4)

Across pooled genuine batch updates, `2188` cross-manager pairs occur within two hours in the same branch (`93.8%` moving in the same direction; `1742` simultaneous hikes) alongside `4472` seven-day cross-manager leapfrog reversals (`385,840.3` BOLD in retaliation hike fees). Exact analytical Ogata time-rescaling integrals and an unrestricted free-`kappa_red` joint MLE (allowing exogenous redemption shocks to decay as fast as `0.5` to `10.7` minutes) confirm that cross-manager mutual excitation survives across all `6/6` positive-debt branch-samples.

| Branch | Dev alpha_cross (t1/2 min) | Dev Exact Ogata KS (p) | Conf alpha_cross (Exact KS p) | Free-kappa Dev alpha_cross (LRT p) | Free-kappa Conf alpha_cross (LRT p) |
|---|---:|---:|---:|---:|---:|
| WETH | 0.252 (11.04m) | 0.109 (p=0.260) | 0.167 (p=0.590) | 0.251 (2.3e-23) | 0.176 (2.9e-04) |
| wstETH | 0.411 (19.09m) | 0.056 (p=0.486) | 0.647 (p=0.003) | 0.408 (7.3e-70) | 0.643 (3.4e-61) |
| rETH | 0.451 (37.61m) | 0.152 (p=0.004) | 0.460 (p=0.963) | 0.445 (3.0e-37) | 0.386 (2.5e-09) |

Because `MIN_INTEREST_RATE_CHANGE_PERIOD = 3,600` seconds enforces zero same-manager gaps below 1 hour, `alpha_self` is mechanically constrained at sub-hour half-lives (`WETH` and `wstETH` have only `3/98` and `6/266` post-1h same-manager gaps in `[1h,2h)`, whereas `rETH` exhibits `19/145` = `13.1%` and nonzero `alpha_self = 0.091`).

## 6. Gas accounting, within-day GPV structural estimation, and equilibrium counterfactuals (Module 5)

Transaction-level gas matching covers `11,421/11,421` (`100.00%`) of all borrower and batch-manager transactions (`11,423/11,444` = `99.82%` overall; all 21 unmatched Development hashes are deployment/admin setup events), totaling `$31,566.77` (`10.7107` ETH). Delegated gas equals `1.074` BOLD per million debt-days versus `2.149` for unbatched debt.

Matching `5,005/5,026` (`99.58%`) on-chain trove redemption hits onto pre-redemption queue ranks and inverting the debt-weighted average within-(branch, day) cross-sectional quantile curve (eliminating the `3.18x` upward macro-drift bias from naive time pooling) identifies absorber share `p0 = 3.87%` and economically realistic median borrower disruption cost `362.0` bp (`3.62%`; IQR `[94.6, 1983.5]` bp; 14-day block-bootstrap 95% CI `[264.7, 526.5]` bp), with in-sample quantile RMSE `2.8` bp (`2.4` bp Dev) and priority-queue disruption `C_PQ = 74.2` bp/yr. Anchoring transfers to the empirical queue floor `r_front = 293.9` bp yields spread `T_PQ_spread = 52.8` bp/yr and `E_PQ_minus_r_front = 127.0` bp/yr (`PoA_spread = 1.713x`), whereas measuring total interest above `r_min = 50.0` bp gives `T_PQ_total = 301.4` bp/yr and `E_PQ_total = 375.6` bp/yr (`PoA_total = 5.065x`). Out-of-sample Dev-to-Conf validation evaluates queue spreads above Confirmation's empirical front rate `r_front_conf`: overall `ALL_BRANCHES` (`r_front_conf = 283.7` bp) observes `107.0` bp spread vs `64.9` bp predicted (`-42.1` bp mean error, RMSE `42.2` bp); `wstETH` (`r_front_conf = 339.4` bp) fits tightly (`66.5` vs `56.2` bp, `-10.3` bp error, RMSE `10.8` bp); and `WETH` (`r_front_conf = 155.6` bp) shows small mean spread error (`131.9` vs `133.8` bp, `+1.9` bp) due to cross-quantile cancellation (quantile RMSE `90.8` bp), even as realized Confirmation redemption turnover fell `3.72x` (`2.771` to `0.745/yr`) while posted rates rose `+45.2` bp, which reflects forward-looking tail-risk pricing.

Equilibrium counterfactuals strip all ad hoc mis-sorting floors (`mis_sort = 0.0` bp; raw within-day staleness correlation `-0.0031`), hold `Design A/A*/D` update frequency conservatively at `1.00x`, derive Co-Pay frequency scaling strictly from Theorem 3.1's cubic-root HJB, calibrate `Design A` spike-and-cut leakage directly to observed `2026-03-06` mainnet events (`7.85` bp/yr pooled), and include the full equilibrium redemption-disruption term `m* C_PQ` inside net social deadweight loss.

| Counterfactual regime (Pooled GE, eps_SP = 0.50) | Eq. base r* (bp) | Borrower upf (bp) | Observed financial cost (bp) | PQ disruption C (bp) | Structural all-in welfare (bp) | Delta welfare vs SQ (bp) | Net social DWL saved (bp) | Eq. SP APR (%) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Status Quo | 318.0 | 226.2 | 576.0 | 74.2 | 653.5 | +0.0 | +0.0 | 4.97% |
| Design A (baseline) | 328.5 | 29.7 | 390.1 | 79.2 | 469.4 | -184.1 | -1.9 | 4.35% |
| Design A* (Optimal Zero-Storage) | 334.7 | 39.0 | 405.6 | 78.8 | 484.4 | -169.1 | -1.5 | 4.40% |
| Design D (Rate-Bond Escrow) | 337.0 | 15.6 | 384.5 | 79.4 | 463.9 | -189.5 | -2.1 | 4.34% |
| Co-Pay beta=0.10 (on SQ) | 321.0 | 171.6 | 524.2 | 75.0 | 601.1 | -52.4 | +0.7 | 4.86% |
| Co-Pay beta=0.25 (on SQ) | 323.9 | 130.1 | 485.4 | 75.8 | 562.3 | -91.2 | +0.9 | 4.76% |
| Co-Pay beta=0.50 (on SQ) | 326.7 | 98.0 | 456.0 | 76.5 | 533.2 | -120.3 | +0.7 | 4.66% |
| Design A* + Co-Pay beta=0.25 | 335.9 | 20.1 | 387.5 | 79.1 | 466.6 | -186.9 | -1.4 | 4.37% |

Parametric GE sensitivity for `Design A*` across `eps_SP in {0.00, 0.25, 0.50, 1.00, 2.00}` (unique fixed point at every point):

| eps_SP | Redemption mult m* | Eq. base r* (bp) | Observed financial cost (bp) | Delta financial vs SQ (bp) | Net social DWL saved (bp) | Eq. SP APR (%) |
|---:|---:|---:|---:|---:|---:|---:|
| 0.00 | 1.0000 | 318.0 | 386.5 | -189.5 | +3.2 | 4.18% |
| 0.25 | 1.0363 | 327.8 | 397.6 | -178.4 | +0.5 | 4.31% |
| 0.50 | 1.0623 | 334.7 | 405.6 | -170.5 | -1.5 | 4.40% |
| 1.00 | 1.0971 | 344.1 | 416.2 | -159.8 | -4.1 | 4.53% |
| 2.00 | 1.1346 | 354.1 | 427.6 | -148.4 | -6.9 | 4.67% |

## 7. Apples-to-apples cross-protocol financial borrowing cost benchmark (485d, 2025-05-19 to 2026-09-15)

All Liquity V2 rows use exact debt-day weighted APRs (`3.46%` delegated, `3.72%` unbatched) and Replay-computed upfront fees. Primary rows compare ongoing repricing-only fees (`2.262%` delegated `BatchUpdated` vs `0.176%` unbatched `op=3`); including origination/draw/join fees for both groups (`+0.253%` delegated vs `+0.320%` unbatched) yields `6.01%` Delegated SQ, `4.29%` Unbatched, `4.31%` `Design A*` GE, and `4.10%` `Design D` GE. Counterfactual rows display Status Quo BOLD peg RMSE (`22.93*` bp) and rate SD (`1.18%`) strictly as ceteris paribus reference values. Liquity V1 `0.53%` reflects a one-time minting fee annualized at a 1-year horizon (`2.10%/yr` at 3 months; `0.26%/yr` at 2 years); Curve `crvUSD` excludes unobserved path-dependent LLAMMA rebalancing losses; Sky rates are exact compounded APY (`Jug.base = 0`), Aave rates are nominal APR (`GHO` base rate prior to `stkAAVE`/Merit discounts), and non-BOLD rows omit wallet gas.

| Protocol (Repricing-only scope for BOLD) | Quoted APR (%) | Episodic/upfront fee (%) | Observed financial cost (%) | Rate SD (%) | Peg RMSE (bp) | Min USD price |
|---|---:|---:|---:|---:|---:|---:|
| Liquity V2 (BOLD): Delegated (Status Quo) | 3.46 | 2.262 | 5.76 | 1.18 | 22.93 | $0.99247 |
| Liquity V2 (BOLD): Unbatched (Self-Managed) | 3.72 | 0.176 | 3.97 | 0.94 | 22.93 | $0.99247 |
| Liquity V2 (BOLD): Delegated (Design A* GE) | 3.63 | 0.390 | 4.06 | 1.18 | 22.93* | $0.99247 |
| Liquity V2 (BOLD): Delegated (Design D GE) | 3.65 | 0.157 | 3.85 | 1.18 | 22.93* | $0.99247 |
| Liquity V1 (LUSD) | 0.00 | 0.526 | 0.53 | 0.08 | 59.33 | $0.99307 |
| Sky / MakerDAO (DAI/USDS: ETH-A) | 7.88 | 0.000 | 7.88 | 0.93 | 4.10 | $0.99533 |
| Sky / MakerDAO (DAI/USDS: WSTETH-A) | 8.88 | 0.000 | 8.88 | 0.93 | 4.27 | $0.99818 |
| Curve (crvUSD: WETH) | 5.68 | n/a | 5.68 | 4.72 | 15.25 | $0.98642 |
| Curve (crvUSD: wstETH) | 6.36 | n/a | 6.36 | 4.71 | 15.25 | $0.98642 |
| Aave V3 (GHO) | 4.54 | 0.000 | 4.54 | 0.96 | 9.78 | $0.99767 |
| Aave V3 (USDC Variable Borrow) | 5.29 | 0.000 | 5.29 | 2.20 | n/a | n/a |

## 8. Vector figures produced (`empirical/figures/`)

- `figures/fig1_notch_bunching_agency.pdf` (`28,140` bytes, SHA-256 `46ff7f8639b05e66`)
- `figures/fig2_spike_cut_and_mechanisms.pdf` (`35,820` bytes, SHA-256 `0850c742bd9ca612`)
- `figures/fig3_causal_routing_did.pdf` (`25,870` bytes, SHA-256 `bf25a7657175c5ed`)
- `figures/fig4_hawkes_leapfrogging.pdf` (`39,487` bytes, SHA-256 `b59a9aa2d5ea09df`)
- `figures/fig5_gpv_structural_welfare.pdf` (`46,820` bytes, SHA-256 `9c63a1937fd23a97`)
- `figures/fig6_cross_protocol_benchmark.pdf` (`50,223` bytes, SHA-256 `c2c9d7a7d3a06b5a`)
