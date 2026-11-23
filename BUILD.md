# Build and verification instructions

This guide walks from a clean macOS or Linux machine through verifying every layer of this repository: the Lean 4 formalization, the Foundry Solidity `0.8.24` contracts and fuzz suite, the offline empirical replication pipeline, and the LaTeX builds for both papers. Each layer is independent, so run only the steps you need.

## Before you start

Clone the repository:

```sh
git clone https://github.com/shiveksaraf/liquity-v2-delegated-borrowing.git
cd liquity-v2-delegated-borrowing
```

Everything was verified with the tool versions below. Nearby releases of Python, Foundry, and TeX Live work fine. Lean 4 and Mathlib are pinned by `lean/lean-toolchain` and `lean/lake-manifest.json`, so `elan` and `lake` select the exact release automatically.

| Tool | Tested version | Needed for |
| --- | --- | --- |
| OS | macOS arm64 (also compatible with Linux) | All steps |
| Lean 4 / Mathlib | `leanprover/lean4:v4.34.0-rc2` | Step 1 |
| Foundry (`forge`) | `1.10.0` (with pinned `solc 0.8.24`) | Step 2 |
| Python | `3.12.3` | Step 2 (report script) and Step 3 |
| `numpy` / `scipy` | `2.0.2` / `1.14.1` | Step 3 |
| `pandas` / `matplotlib` | `2.2.3` / `3.9.2` | Step 3 |
| `requests` | `2.32+` | Step 3 (only for optional live re-fetch) |
| TeX Live | `2024` (`pdfTeX 3.141592653-2.6-1.40.26`) | Step 4 |

No GPU, paid RPC key, or proprietary data feed is required. Every empirical step runs offline against the canonical mainnet inputs and SHA-256 archived external snapshots included in `empirical/`.

## Step 1: build the Lean 4 formalization and check axioms

Install `elan` (the Lean version manager) if you do not already have it:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Enter `lean/`, download the prebuilt Mathlib cache, and build `LiquityV2`:

```sh
cd lean
lake exe cache get
lake build
```

Do not skip `lake exe cache get`. Without the cache, `lake build` compiles Mathlib from source, which takes over an hour. With the cache, all 7 modules under `LiquityV2/` plus the root `LiquityV2.lean` entrypoint (3,752 lines total, 113 public theorems and lemmas) build in a few minutes with zero errors and zero warnings:

- `LiquityV2/Defs.lean` (260 lines): deployed Liquity V2 constants, integer interest floor and ceiling arithmetic, and `uint256` non-overflow bounds (`debt <= 7.658 x 10^52` wei at 250% APR).
- `LiquityV2/ReverseQueue.lean` (744 lines): absorber strict optimality (`tau <= phi`), single-crossing monotonicity, Milgrom-Segal envelope bounds, closed-form discrete incentive compatibility, weighted Chebyshev sorting efficiency, unique general-equilibrium fixed point, two-sided Stability Pool yield-recycling deadweight loss, and continuous GPV identification.
- `LiquityV2/CooldownFees.lean` (310 lines): cooldown convention and Axioms `(A1)-(A5)`, status-quo `K`-step staircase inflation, spike-and-cut arbitrage in both Status Quo and baseline Design A, and the March 6, 2026 wstETH mainnet witness.
- `LiquityV2/DesignAStar.lean` (976 lines): pointwise-minimal uniqueness of zero-storage `Design A*` from strictly increasing micro-hikes, multi-step cut superadditivity, and exact `uint256` rounding bounds (`<= K - 1` wei staircase, `<= 2` wei floor / `<= 1` wei `ceilDiv` / `0` wei `ceilDiv + 1` hold residual, `<= 1` wei Sybil split).
- `LiquityV2/FlashLoanEscrow.lean` (734 lines): flash-loan close-and-reopen impossibility for pure in-place rules and complete `Design D` principal-escrow security, including accrued-interest-safe pure-cut zero-underflow and zero-dilution partial repayment.
- `LiquityV2/DelegationAgency.lean` (493 lines): fee-base capitalization expansion, 168-hour cut-bunching threshold, existence of borrower-dominated near-notch hikes, contractual co-pay alignment threshold `beta*`, and discrete LIFO leapfrogging non-existence and fee collapse.
- `LiquityV2/Main.lean` (228 lines) and `LiquityV2.lean` (7 lines): top-level exports of the 8 flagship theorems.

Confirm that zero forbidden tokens appear in Lean declarations or proofs:

```sh
grep -rnE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^[[:space:]]*(partial|axiom)[[:space:]]' LiquityV2.lean LiquityV2/
```

That command should print nothing (exit status 1). To inspect the exact Lean kernel axioms of all 8 top-level exports from inside `lean/`:

```sh
lake env lean --stdin <<'EOF'
import LiquityV2
#print axioms LiquityV2.main_reverse_queue_ic_and_absorber
#print axioms LiquityV2.main_reverse_queue_equilibrium_and_ge
#print axioms LiquityV2.main_gpv_identification
#print axioms LiquityV2.main_prior_mechanisms_failure
#print axioms LiquityV2.main_designAStar_security_and_uniqueness
#print axioms LiquityV2.main_designAStar_evm_uint256_bounds
#print axioms LiquityV2.main_flash_loan_impossibility_and_designD
#print axioms LiquityV2.main_delegation_agency_alignment
EOF
```

Every theorem prints strictly a subset of `[propext, Classical.choice, Quot.sound]`, with zero custom axioms and zero `sorryAx`. Return to the repository root:

```sh
cd ..
```

## Step 2: compile Solidity contracts, run fuzzing, and verify the upstream patch

Install Foundry (`forge`) via Homebrew or the official `foundry-rs/foundry` release installer if you do not already have it:

```sh
brew install foundry
```

On Linux, install `foundryup` from `https://github.com/foundry-rs/foundry` and run `foundryup`.

The Solidity suite under `contracts/` has zero external library submodules; `test/TestBase.sol` is self-contained. Compile with warnings denied and run both the default profile (`32,500` fuzz runs) and the intense profile (`130,000` fuzz runs, fixed seed `0x4c6971756974795632`):

```sh
cd contracts
forge build --deny warnings --sizes
forge test --summary
FOUNDRY_PROFILE=intense forge test --summary
```

Expected results:
- `forge build --deny warnings --sizes` exits `0` with 0 warnings. Runtime bytecode sizes are all below the 24,576-byte EIP-170 limit: `StatusQuoBorrowerOps` `14,523` B, `DesignABorrowerOps` `14,561` B, `DesignAStarBorrowerOps` `15,009` B, `CoPayBorrowerOps` `15,463` B, and `DesignDBorrowerOps` `22,767` B (1,809 bytes of headroom).
- Both `forge test` runs pass `44/44` tests (`25` deterministic exploit and invariant tests in `ExploitReproductions.t.sol`, `13` fuzz invariants in `DifferentialFuzz.t.sol`, and `6` gas benchmark suites in `GasBenchmark.t.sol`) with 0 failures.

To regenerate `BENCHMARK_REPORT.json` and `BENCHMARK_REPORT.md` directly from compiler storage layouts, isolated `gasleft()` measurements, and both fuzz profiles:

```sh
python3 generate_benchmark_report.py
```

Look for these key metrics in `BENCHMARK_REPORT.md`:
- Storage slots: `11` slots (`+0`, slot-for-slot identical) for `StatusQuoBorrowerOps`, `DesignABorrowerOps`, `DesignAStarBorrowerOps`, and `CoPayBorrowerOps`; `14` slots (`+3` mapping slots: `troveBonds`, `batchBonds`, `batchCuts`) for `DesignDBorrowerOps`.
- Isolated warm-state gas deltas for `DesignAStarBorrowerOps` versus `StatusQuoBorrowerOps`: `-1,937` gas on premature batch hikes (`107,466` vs `109,403`), `-1,863` gas on premature batch cuts (`107,528` vs `109,391`), `-1,827` gas on premature solo hikes, `-1,753` gas on premature solo cuts, and `0` gas on `openTrove`, `repayBold`, and `closeTrove`.

To verify that the 5-entry-point upstream patch applies cleanly against the verified mainnet `WETH_BorrowerOperations.sol` source bundled under `empirical/inputs/contract_sources/`:

```sh
cd ..
patch --dry-run -p1 -d empirical/inputs/contract_sources < contracts/src/LiquityV2FeePatch.diff
```

That dry run should report clean hunks and exit `0` without modifying any file.

## Step 3: reproduce the empirical pipeline and vector figures

Install the Python dependencies:

```sh
python3 -m pip install -r empirical/requirements.txt
```

Run the complete offline empirical pipeline from `empirical/`:

```sh
cd empirical
python3 run_all.py
```

`run_all.py` checks SHA-256 digests across the bundled canonical inputs and all `22` archived external data receipts (`20` raw JSON files plus `2` derived CSVs in `data_external/SHA256_RECEIPTS.json`), executes all five econometric and structural modules in order (`notch_and_agency.py`, `spike_and_cut.py`, `causal_routing_did.py`, `hawkes_leapfrogging.py`, `gpv_structural_welfare.py`), rebuilds `EMPIRICAL_MASTER_RESULTS.json` and `EMPIRICAL_SUMMARY.md` via `build_master_ledger.py`, and regenerates all `6` TrueType vector PDF figures under `figures/` via `make_figures.py`.

Expected headline numbers reproduced from the 485-day canonical sample (`44,907` events across `11,444` transactions):
- Permission-screened (`minInterestRateChangePeriod < 604,800` s) delegated cut bunching at 168 hours: `b = 91.8` (`95%` bootstrap CI `[45.4, 153.7]`, `22.2%` in `[168h, 169h)`, `0` cuts in `[120h, 168h)`), and `+57.8` pp hike-versus-cut premature asymmetry (`p = 2.00e-26`).
- Pooled repricing fees across 485 days: 421,986.60 BOLD under Status Quo, reduced by `-83.8%` to 68,427.29 BOLD under `Design A*` and by `-93.5%` to 27,326.90 BOLD (including 5% opportunity cost, 0 underflows) under `Design D`, with March 6, 2026 spike-and-cut arbitrage discounts reduced from `84.02%` (`wstETH`) and `60.96%` (`WETH`) to `0.000%`.
- Predetermined Bartik shift-share 2SLS on mechanical `CollateralRegistry` routing (`F = 197.7` pooled): `+13.53` BOLD per million debt-days 48-hour fee response (`p = 0.0347` FE-DOF, 14-day block-bootstrap `95%` CI `[+2.78, +35.02]`), null `t+7d` placebo (`+3.58`, `p = 0.664`).
- Multivariate Hawkes MLE: positive cross-manager excitation across all `6/6` positive-debt branch-samples (`alpha_cross` in `[0.17, 0.65]`, `p <= 2.89e-4` with free exogenous decay), attributing `21.77%` (89,543.95 BOLD) of pooled hike penalties to cross-manager leapfrogging.
- Within-(branch, day) GPV inversion (`5,005/5,026` hits): `3.87%` absorber share, `362.0` bp median borrower disruption cost (`2.8` bp in-sample RMSE); at baseline `eps_SP = 0.50`, equilibrium delegated financial borrowing cost drops from `5.76%` to `4.06%` (`Design A*`) and `3.85%` (`Design D`), below Aave GHO (`4.54%`), Aave USDC (`5.30%`), Curve crvUSD (`5.68%`--`6.36%`), and Sky (`7.88%`--`8.88%`).

You do not need to run `fetch_external_data.py` to reproduce the papers, because all 22 external data receipts are already frozen under `data_external/`. Running `python3 fetch_external_data.py` queries public Ethereum RPC endpoints, DefiLlama, and Curve directly; note that live fork TVL snapshots change over time while historical price and archive RPC block queries remain immutable. Return to the repository root:

```sh
cd ..
```

## Step 4: rebuild both papers (unblinded and double-blind)

Install TeX Live with `amsmath`, `amsthm`, `booktabs`, `natbib`, `tikz`, and `bibtex` (on Debian or Ubuntu, `texlive-latex-recommended`, `texlive-latex-extra`, `texlive-pictures`, and `texlive-fonts-recommended`).

If you regenerated the empirical figures in Step 3, copy them into the empirical paper directory first:

```sh
cp empirical/figures/fig*.pdf papers/delegated_borrowing_empirics/figures/
```

Rebuild both `main.pdf` and `blinded.pdf` for both papers in subshells:

```sh
for dir in papers/reverse_queue_theory papers/delegated_borrowing_empirics; do
  (cd "$dir" && pdflatex -interaction=nonstopmode main && bibtex main && pdflatex -interaction=nonstopmode main && pdflatex -interaction=nonstopmode main)
  (cd "$dir" && pdflatex -interaction=nonstopmode blinded && bibtex blinded && pdflatex -interaction=nonstopmode blinded && pdflatex -interaction=nonstopmode blinded)
done
```

Expected outputs after the four-pass builds:

| Directory | Output PDFs | Pages |
| --- | --- | ---: |
| `papers/reverse_queue_theory/` | `main.pdf`, `blinded.pdf` | 32 |
| `papers/delegated_borrowing_empirics/` | `main.pdf`, `blinded.pdf` | 29 |

Reference SHA-256 prefixes: `empirical/EMPIRICAL_MASTER_RESULTS.json` (`ee72b28247f0a7d6`), `empirical/figures/fig2_spike_cut_and_mechanisms.pdf` (`0850c742bd9ca612`), and `empirical/figures/fig3_causal_routing_did.pdf` (`bf25a7657175c5ed`). Both builds finish with zero errors, zero undefined citations, and zero overfull boxes. Auxiliary files (`*.aux`, `*.bbl`, `*.blg`, `*.log`, `*.out`) are listed in `.gitignore`.

## What each command produces

| Command | Files written | What it verifies |
| --- | --- | --- |
| `cd lean && lake build` | Build cache in `lean/.lake/` | Full Lean 4 kernel check of all 113 theorems and lemmas under standard axioms |
| `cd contracts && forge test` | Artifacts in `contracts/out/` and `contracts/cache/` | 44 Solidity tests (25 deterministic exploit/invariant tests, 13 fuzz properties, 6 gas suites) |
| `cd contracts && python3 generate_benchmark_report.py` | `contracts/BENCHMARK_REPORT.{json,md}` | Compiler storage layouts, EIP-170 runtime byte sizes, isolated gas deltas, and 130,000 intense fuzz runs |
| `cd empirical && python3 run_all.py` | `empirical/results/*.json`, `EMPIRICAL_MASTER_RESULTS.json`, `EMPIRICAL_SUMMARY.md`, `empirical/figures/fig1..fig6_*.pdf` | SHA-256 input verification, notch bunching, spike-and-cut replays, Bartik 2SLS, Hawkes MLE, GPV structural welfare, and 6 vector PDFs |
| `pdflatex` + `bibtex` | `main.pdf`, `blinded.pdf` | Compiles unblinded and anonymized manuscripts from source |

## If the build fails

If `lean --version` reports no configured toolchain, make sure you are inside `lean/` before running `lake` or `lean`. The `lean/lean-toolchain` file selects `leanprover/lean4:v4.34.0-rc2` automatically from inside that directory.

If `lake build` begins compiling Mathlib from scratch, stop it, run `lake exe cache get` inside `lean/`, and then re-run `lake build`.

If `forge` is not found after installing Foundry, add `$HOME/.foundry/bin` to `PATH` or open a new shell. If `forge build` attempts to download `solc 0.8.24` on an offline machine, install `solc 0.8.24` locally and pass `--use /path/to/solc`.

If Python raises an `ImportError` on macOS Apple Silicon (for example, `mach-o file, but is an incompatible architecture`), you invoked the system Xcode `python3` (3.9) instead of arm64 Python 3.12. Invoke your arm64 Python 3.12 binary or create a fresh virtual environment (`python3.12 -m venv .venv && source .venv/bin/activate && pip install -r empirical/requirements.txt`).

If `pdflatex` stops on missing `tikz.sty`, `booktabs.sty`, or `threeparttable.sty`, install `texlive-pictures` and `texlive-latex-extra` (or the equivalent `tlmgr` packages on macOS).
