# Reverse priority queues and delegated borrowing in Liquity V2

This repository holds the two papers, Lean 4 formalization, Solidity reference contracts, empirical datasets, and replication scripts by Shivek Saraf and Ayush Sankar (co-first authors) on user-set-rate stablecoins and delegated rate management in Liquity V2.

Liquity V2 defends the BOLD stablecoin peg without discretionary rate governance. Borrowers against WETH, wstETH, and rETH pick their own annual interest rates, and par redemptions execute in ascending rate order. Higher rates push a loan toward the back of a reverse priority queue. To deter borrowers from sitting at the 0.5% floor and jumping up right before a redemption wave, the contract charges any rate adjustment within a 168-hour cooldown an upfront fee equal to seven days of the branch's entire average borrowing rate on total debt, capitalized onto borrower principal.

Across 485 days of canonical Ethereum mainnet activity (44,907 events across 11,444 transactions, 964 troves, and 23 batch managers), delegated batch managers expanded from 8.59% to 59.06% of managed debt while quoting 40.15 bp lower base APR in our 408-day Development sample and 55.44 bp lower in our 77-day frozen Confirmation holdout. Yet exact accrued-liability accounting reverses that gap: delegated debt incurs +38.04 BOLD per million debt-days higher total financing liability (5.76% versus 3.97% annualized pooled financial cost) because batch managers triggered 421,986.60 BOLD in premature repricing fees, 93.73% from consecutive premature upward adjustments. The same fixed branch-average cut fee also permitted live spike-and-cut arbitrage on March 6, 2026 at 84.62% (wstETH) and 61.56% (WETH) cut-fee discounts.

We analyze this market in two companion papers. The theoretical and security paper solves the continuous-time reverse priority queue equilibrium, proves pointwise-minimal uniqueness of a zero-extra-storage symmetric incremental fee rule (`Design A*`), establishes a flash-loan close-and-reopen impossibility ceiling addressed by a one-slot principal-escrow rule (`Design D`), models delegated agency and atomic leapfrogging, and certifies the theory in Lean 4 alongside compiled Solidity `0.8.24` benchmarks. The empirical paper separates 604,800-second smart-contract revert walls from economic fee notches using 37 live on-chain manager permission tuples, identifies causal fee responses via mechanical `CollateralRegistry` routing shift-share instruments and multivariate Hawkes point processes, inverts borrower disruption costs within branch-days, and evaluates equilibrium welfare against Aave, Curve, Sky, and Liquity V1.

## Quick verification

Each layer runs independently on a clean machine. [BUILD.md](BUILD.md) lists pinned tool versions, step-by-step commands, and expected outputs.

To verify the Lean 4 formalization (3,752 lines across 7 modules plus root `LiquityV2.lean`, 113 public theorems and lemmas; requires `elan` and downloads prebuilt Mathlib caches so you do not compile Mathlib from source):

```sh
cd lean
lake exe cache get
lake build
```

To compile the Solidity `0.8.24` contracts, run all 44 tests (`25` deterministic exploit and invariant tests, `13` fuzz properties, `6` gas suites), and run the `130,000`-run intense fuzz profile (requires Foundry `forge`):

```sh
cd contracts
forge build --deny warnings
forge test
FOUNDRY_PROFILE=intense forge test
```

To reproduce the empirical results, JSON master ledger, and all 6 vector PDF figures offline from the bundled canonical mainnet inputs and SHA-256 archived external snapshots (requires Python 3.12 with `numpy`, `scipy`, `pandas`, `matplotlib`, and `requests`):

```sh
cd empirical
python3 run_all.py
```

The Lean build prints zero warnings and every theorem uses only the standard axioms `[propext, Classical.choice, Quot.sound]`. The Foundry suite passes 44/44 tests with 0 failures across 130,000 intense fuzz runs. `DesignAStarBorrowerOps` adds `+0` storage slots and saves `1,937` gas on premature batch hikes (`1,863` gas on premature cuts), while `DesignDBorrowerOps` compiles to `22,767` runtime bytes (1,809 bytes below the 24,576-byte EIP-170 limit). The Python pipeline verifies all 22 SHA-256 external data receipts (`20` raw JSON files plus `2` derived CSVs) and writes all 6 vector figures cleanly.

## Papers

Both papers live under `papers/`, each with unblinded (`main.tex`, `main.pdf`) and double-blind (`blinded.tex`, `blinded.pdf`) builds plus bibliographies.

| Directory | Title | Pages | Main results |
| --- | --- | ---: | --- |
| `papers/reverse_queue_theory/` | Reverse Priority Queues, Cooldown Fee Mechanisms, and Delegated Agency in User-Set-Rate Stablecoins | 32 | Reverse priority queue equilibrium and GPV inversion; pointwise-minimal uniqueness of zero-storage `Design A*`; cooldown trilemma and flash-loan impossibility; one-slot `Design D` escrow with append-only cut log; delegated `(S, s)` agency, atomic LIFO leapfrogging, and contractual co-pay; Lean 4 certification (3,752 lines, 113 theorems) and Foundry `solc 0.8.24` storage and gas benchmarks (3 TikZ figures, 30 references) |
| `papers/delegated_borrowing_empirics/` | Delegated Interest-Rate Management, Cooldown Friction, and Equilibrium Welfare in User-Set-Rate Stablecoins | 29 | 485-day canonical mainnet study (44,907 events, 37 RPC permissions); 168-hour cut bunching (`b = 91.8`) and near-notch dominated hikes; live March 6, 2026 spike-and-cut forensics and fee-rule replays (`-83.8%` `Design A*`, `-93.5%` `Design D`); mechanical routing Bartik 2SLS (`+13.53` BOLD/M debt-days) and Hawkes cross-manager leapfrogging (`21.77%` of hike fees); within-day GPV structural welfare (`362.0` bp median cost; `4.06%` `Design A*` and `3.85%` `Design D` GE cost) and cross-protocol benchmark (6 vector figures, 38 references) |

Both papers compile to identical page counts across unblinded (`main.pdf`) and anonymized (`blinded.pdf`) builds (`32` pages for theory; `29` pages for empirics).

## What is here

- `papers/` holds both manuscripts (`reverse_queue_theory/` and `delegated_borrowing_empirics/`), their shared bodies, bibliographies, vector figures, and compiled `main.pdf` and `blinded.pdf` files.
- `lean/` holds the Lean `v4.34.0-rc2` / Mathlib `v4.34.0-rc2` formalization across 7 modules (`Defs`, `ReverseQueue`, `CooldownFees`, `DesignAStar`, `FlashLoanEscrow`, `DelegationAgency`, `Main`) and the root `LiquityV2.lean` entrypoint (3,752 lines, 113 public theorems and lemmas, zero `sorry`, zero `native_decide`, zero custom axioms).
- `contracts/` holds the self-contained Solidity `0.8.24` Foundry implementation of `StatusQuoBorrowerOps`, `DesignABorrowerOps`, `DesignAStarBorrowerOps`, `DesignDBorrowerOps`, and `CoPayBorrowerOps`, the 5-entry-point upstream patch `src/LiquityV2FeePatch.diff`, the deterministic exploit and `130,000`-run differential fuzzing suites, and `BENCHMARK_REPORT.{json,md}`.
- `empirical/` holds the frozen canonical Ethereum mainnet inputs (`inputs/`, 44,907 events across 485 days, 9 deployed Solidity contract sources, and exact-integer EVM replay core), the `22` SHA-256 archived external data files (`data_external/`), the Python estimation scripts (`notch_and_agency.py`, `spike_and_cut.py`, `causal_routing_did.py`, `hawkes_leapfrogging.py`, `gpv_structural_welfare.py`, `build_master_ledger.py`, `make_figures.py`, `run_all.py`), frozen JSON outputs, `EMPIRICAL_MASTER_RESULTS.json`, `EMPIRICAL_SUMMARY.md`, and all `6` vector PDF figures.
- [BUILD.md](BUILD.md) walks through reproducing every layer from a fresh machine.

## Building the papers

Each paper compiles with standard TeX Live (`pdflatex` and `bibtex`). Run builds in a subshell so your working directory stays unchanged:

```sh
(cd papers/reverse_queue_theory && pdflatex main && bibtex main && pdflatex main && pdflatex main)
(cd papers/delegated_borrowing_empirics && pdflatex main && bibtex main && pdflatex main && pdflatex main)
```

Replace `main` with `blinded` to rebuild the double-blind PDFs. Both `main.tex` and `blinded.tex` include the same `body.tex` file, so every theorem, table, and numerical figure stays identical across the two versions.

## License and citation

Project-authored code, Lean proofs, Solidity contracts, and documentation are released under the [MIT License](LICENSE). [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) states how upstream Liquity V2 Solidity sources, Lean 4, Mathlib, Foundry, Python libraries, external market snapshots, and TeX distributions are handled.

Use [CITATION.cff](CITATION.cff) when citing a release.
