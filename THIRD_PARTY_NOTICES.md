# Third-party materials and dependencies

The root [MIT License](LICENSE) covers material authored for this project by Shivek Saraf and Ayush Sankar, except where a file or this notice states otherwise. It does not relicense external source files, upstream protocols, or public market datasets included for offline verification.

## Upstream Liquity V2 Solidity sources

The nine verified Ethereum mainnet contract files under `empirical/inputs/contract_sources/` (`*_BorrowerOperations.sol`, `*_Constants.sol`, `*_LiquityBase.sol` for WETH, wstETH, and rETH) are archived verbatim from deployed Liquity V2 contracts solely for exact accounting verification and `patch --dry-run` validation of `contracts/src/LiquityV2FeePatch.diff`. They remain governed by their upstream Liquity AG license terms.

## External market and on-chain data snapshots

Public Ethereum mainnet event logs, live and archive RPC `eth_call` responses, DefiLlama price and TVL snapshots, and Curve Finance `crvUSD` daily controller snapshots under `empirical/inputs/` and `empirical/data_external/` are archived with SHA-256 receipts solely for deterministic academic replication. No proprietary or paid data feeds are included.

## Software toolchains and libraries

No third-party software libraries or build caches are vendored in this repository. Each verification layer installs its own dependencies under their respective licenses:

- `lean/`: Lean 4 (`leanprover/lean4:v4.34.0-rc2`, Apache-2.0) and Mathlib4 (Apache-2.0), fetched by Lake according to `lean/lakefile.toml` and `lean/lake-manifest.json`.
- `contracts/`: Foundry (`forge`, Apache-2.0 / MIT) and `solc 0.8.24` (GPL-3.0). `contracts/test/TestBase.sol` is self-contained with zero external submodules.
- `empirical/`: Python 3 with `numpy` (BSD-3-Clause), `scipy` (BSD-3-Clause), `pandas` (BSD-3-Clause), `matplotlib` (PSF-based), and `requests` (Apache-2.0).
- `papers/`: standard TeX Live distribution (`pdflatex`, `bibtex`, `amsmath`, `amsthm`, `booktabs`, `natbib`, `tikz`).
