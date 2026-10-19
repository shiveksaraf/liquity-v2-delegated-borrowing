"""Shared canonical loaders, constants, exact integer math, and econometric utilities
for the Liquity V2 empirical finance and structural econometrics replication suite.

All paths resolve relative to this directory so the pipeline runs offline from a clean clone.
"""
from __future__ import annotations

import gzip
import hashlib
import json
import math
import os
import sys

sys.dont_write_bytecode = True
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np
import pandas as pd

EMP_ROOT = Path(__file__).resolve().parent
INPUTS_DIR = EMP_ROOT / "inputs"
EVENTS_DIR = INPUTS_DIR / "events"
GAS_LEDGER_PATH = INPUTS_DIR / "gas_ledger.json"
BATCH_RATE_LEDGER_PATH = INPUTS_DIR / "batch_rate_ledger.json"
HOLDOUT_LOGS_DIR = INPUTS_DIR / "holdout_logs"
DAILY_CONC_PATH = INPUTS_DIR / "daily_concentration.json"
EXT_DIR = EMP_ROOT / "data_external"
RES_DIR = EMP_ROOT / "results"
FIG_DIR = EMP_ROOT / "figures"

# Protocol exact integer constants (verified against WETH_Constants.sol)
WAD = 10**18
YEAR_SECONDS = 365 * 86400  # 31,536,000
COOLDOWN_SECONDS = 7 * 86400  # 604,800 (168 hours)
COOLDOWN_HOURS = 168.0
MIN_ANNUAL_INTEREST_RATE = 5 * 10**15  # 0.5%
MAX_ANNUAL_INTEREST_RATE = 250 * 10**16  # 250%
MIN_CHANGE_PERIOD = 3600  # 1 hour
REDEMPTION_FEE_FLOOR = 0.005  # 0.5%
SP_YIELD_SPLIT = 0.75  # 75% of borrow interest routed to Stability Pool

# Exact Dev / Confirmation sample boundaries (UTC)
DEV_START_DATE = "2025-05-19"
DEV_END_DATE = "2026-06-30"
CONF_START_DATE = "2026-07-01"
CONF_END_DATE = "2026-09-15"
DEV_END_TS = int(datetime(2026, 7, 1, 0, 0, 0, tzinfo=timezone.utc).timestamp())  # exclusive upper bound for Dev

BRANCHES = ("WETH", "wstETH", "rETH")

CONTRACTS = {
    "WETH": {
        "troveManager": "0x7bcb64b2c9206a5b699ed43363f6f98d4776cf5a",
        "borrowerOperations": "0x372abd1810eaf23cb9d941bbe7596dfb2c46bc65",
    },
    "wstETH": {
        "troveManager": "0xa2895d6a3bf110561dfe4b71ca539d84e1928b22",
        "borrowerOperations": "0xa741a32f9dcfe6adba088fd0f97e90742d7d5da3",
    },
    "rETH": {
        "troveManager": "0xb2b2abeb5c357a234363ff5d180912d319e3e19e",
        "borrowerOperations": "0xe8119fc02953b27a1b48d2573855738485a17329",
    },
}

# Exact M01-M19 mapping from manager_supplement.md (positive-debt managers ranked by Dev BOLD-days)
MANAGER_LABELS: Dict[str, str] = {
    "0x000000000017d2a7b863e9ebbe6f9ab7255eb7c5": "M01",
    "0x0000000000704f94ce2fe636dab92677a9745dc3": "M02",
    "0x00000000001991cee928c561e37725816cbf73ba": "M03",
    "0x8869a6fb59a8df330f90d9fbf46ebfaff6d4bc14": "M04",
    "0x25bc0272217fb0fd7a2ff0d62cebe1aba15e4d91": "M05",
    "0xe507e4d0763851a6287238aadd243948d18ab60a": "M06",
    "0x1578ed833d986c1188d1a998aa5fecd418bef5da": "M07",
    "0x50bc02c6c7124e6e1b8333b80a0416e504e2d044": "M08",
    "0x000000000036abd8fe2238a541ec72f91ceebefa": "M09",
    "0xe707784292289be3aa0fb6f9d33d420291f98695": "M10",
    "0x0000000000cbed6433d0777552ee00f9c8e40f76": "M11",
    "0x50bc019abdb9951602bc4fe92947d3c15d5e45df": "M12",
    "0x75bc02022344159b7ef50a3ff5291dd2bc6918c7": "M13",
    "0x00000000003b24f6895911d5e7ba18d6caa1da2b": "M14",
    "0x25bc01fd5a01b1864a7dbaddb05bfed642340da2": "M15",
    "0x7700b2d305f47ae82e9598bab6d7ccb57299a82b": "M16",
    "0x75bc01bf1e21ed33915777c131b62bb13b5f2552": "M17",
    "0x00000000006c021d70549b7ee216f7ca8d7b6263": "M18",
    "0x8069d9cc7ab443a06f7e639d703eb0819cf0a2b9": "M19",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def keccak256_hex(data: bytes) -> str:
    """Compute Ethereum Keccak-256 hex digest without 0x prefix using pure-Python helper."""
    from liquity_rate_io import keccak256

    h = keccak256(data)
    return h[2:] if h.startswith("0x") else h


def fn_selector(signature: str) -> str:
    return "0x" + keccak256_hex(signature.encode("utf-8"))[:8]


def manager_label(addr: str) -> str:
    a = addr.lower()
    if a in MANAGER_LABELS:
        return MANAGER_LABELS[a]
    return f"Z_{a[2:8]}"


def ts_to_date(ts: int) -> str:
    return datetime.fromtimestamp(int(ts), tz=timezone.utc).strftime("%Y-%m-%d")


def sample_label(ts: int) -> str:
    return "development" if int(ts) < DEV_END_TS else "confirmation"


def calc_interest_wei(debt_wei: int, rate_wad: int, period_seconds: int) -> int:
    """Exact Solidity integer floor: (debt * rate * period) // (WAD * YEAR_SECONDS)."""
    if debt_wei <= 0 or rate_wad <= 0 or period_seconds <= 0:
        return 0
    return (int(debt_wei) * int(rate_wad) * int(period_seconds)) // (WAD * YEAR_SECONDS)


def load_batch_rate_ledger() -> Dict[str, Any]:
    with open(BATCH_RATE_LEDGER_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def load_canonical_events(sample: str = "pooled") -> Dict[str, List[Dict[str, Any]]]:
    """Load decoded canonical events per branch.
    sample in {'development', 'confirmation', 'pooled'}.
    """
    out: Dict[str, List[Dict[str, Any]]] = {b: [] for b in BRANCHES}
    prefixes = (
        ["development"]
        if sample == "development"
        else ["confirmation"]
        if sample == "confirmation"
        else ["development", "confirmation"]
    )
    for b in BRANCHES:
        evs: List[Dict[str, Any]] = []
        for pref in prefixes:
            p = EVENTS_DIR / f"{pref}_{b}.json.gz"
            with gzip.open(p, "rt", encoding="utf-8") as f:
                chunk = json.load(f)
            for e in chunk:
                e_copy = dict(e)
                e_copy["_sample"] = pref
                e_copy["_branch"] = b
                evs.append(e_copy)
        evs.sort(key=lambda x: (int(x["block"]), int(x["index"])))
        out[b] = evs
    return out


def load_daily_panels(sample: str = "pooled") -> pd.DataFrame:
    dfs = []
    if sample in ("development", "pooled"):
        d = pd.read_csv(INPUTS_DIR / "development_panel.csv.gz")
        d["sample"] = "development"
        dfs.append(d)
    if sample in ("confirmation", "pooled"):
        c = pd.read_csv(INPUTS_DIR / "confirmation_panel.csv.gz")
        c["sample"] = "confirmation"
        dfs.append(c)
    df = pd.concat(dfs, ignore_index=True)
    df["debt_bold"] = df["debt_wei"].astype(float) / 1e18
    df["coll_eth"] = df["coll_wei"].astype(float) / 1e18
    df["base_apr_bps"] = df["base_APR_WAD"].astype(float) / 1e14
    df["mgmt_apr_bps"] = df["management_APR_WAD"].astype(float) / 1e14
    df["allin_apr_bps"] = df["base_apr_bps"] + df["mgmt_apr_bps"]
    df["manager"] = df["manager"].fillna("").astype(str).str.lower()
    return df


def circular_block_bootstrap(
    dates: Sequence[str],
    stat_fn: Callable[[Sequence[str]], float],
    block_len: int = 14,
    n_boot: int = 999,
    seed: int = 20261123,
) -> Dict[str, Any]:
    """Circular moving-block bootstrap over sorted unique calendar dates."""
    uniq = list(dates)
    T = len(uniq)
    if T == 0:
        return {"estimate": float("nan"), "se": float("nan"), "ci_low": float("nan"), "ci_high": float("nan"), "n_valid": 0}
    point = float(stat_fn(uniq))
    rng = np.random.default_rng(seed)
    b = min(block_len, T)
    n_blocks = int(math.ceil(T / b))
    draws = []
    for _ in range(n_boot):
        starts = rng.integers(0, T, size=n_blocks)
        idx = np.concatenate([(s + np.arange(b)) % T for s in starts])[:T]
        sampled = [uniq[i] for i in idx]
        val = stat_fn(sampled)
        if val is not None and np.isfinite(val):
            draws.append(float(val))
    arr = np.asarray(draws, dtype=float)
    if len(arr) < 20:
        return {"estimate": point, "se": float("nan"), "ci_low": float("nan"), "ci_high": float("nan"), "n_valid": int(len(arr))}
    return {
        "estimate": point,
        "se": float(np.std(arr, ddof=1)),
        "ci_low": float(np.percentile(arr, 2.5)),
        "ci_high": float(np.percentile(arr, 97.5)),
        "n_valid": int(len(arr)),
    }


def ols_fe_twoway_cluster(
    y: np.ndarray,
    X: np.ndarray,
    fe_groups: Sequence[np.ndarray],
    cluster1: np.ndarray,
    cluster2: Optional[np.ndarray] = None,
    weights: Optional[np.ndarray] = None,
    max_iter: int = 200,
    tol: float = 1e-10,
) -> Dict[str, Any]:
    """Exact alternating-projection (FWL / Correia) multi-way FE WLS/OLS with
    one-way or Cameron-Gelbach-Miller (2011) two-way cluster-robust covariance.

    Returns beta, se, t_stat, p_val (normal two-sided), r2_within, n_obs, dof_fe.
    """
    from scipy import stats

    y = np.asarray(y, dtype=float).reshape(-1)
    X = np.asarray(X, dtype=float)
    if X.ndim == 1:
        X = X.reshape(-1, 1)
    n, k = X.shape
    w = np.ones(n, dtype=float) if weights is None else np.asarray(weights, dtype=float).reshape(-1)
    w = w / np.mean(w)

    # Encode FE group indices
    fe_codes = []
    fe_nlevels = []
    for g in fe_groups:
        _, inv = np.unique(g, return_inverse=True)
        fe_codes.append(inv)
        fe_nlevels.append(int(inv.max()) + 1)

    # Demean y and X via weighted alternating projections
    M = np.column_stack([y, X])
    for _ in range(max_iter):
        max_diff = 0.0
        for inv, nlev in zip(fe_codes, fe_nlevels):
            w_sum = np.bincount(inv, weights=w, minlength=nlev)
            w_sum_safe = np.where(w_sum > 0, w_sum, 1.0)
            for j in range(M.shape[1]):
                num = np.bincount(inv, weights=w * M[:, j], minlength=nlev)
                means = num / w_sum_safe
                delta = means[inv]
                M[:, j] -= delta
                d = float(np.max(np.abs(delta)))
                if d > max_diff:
                    max_diff = d
        if max_diff < tol:
            break

    yd = M[:, 0]
    Xd = M[:, 1:]

    # Weighted OLS on demeaned system
    sw = np.sqrt(w)
    Xw = Xd * sw[:, None]
    yw = yd * sw

    # Solve via SVD/pseudoinverse for numerical stability
    XtX = Xw.T @ Xw
    XtX_inv = np.linalg.pinv(XtX)
    beta = XtX_inv @ (Xw.T @ yw)
    resid = yd - Xd @ beta

    # Within R^2
    tss = float(np.sum(w * yd**2))
    rss = float(np.sum(w * resid**2))
    r2_within = 1.0 - rss / tss if tss > 0 else 0.0

    # Effective FE dof (exact for 1 FE; conservative sum - (G-1) for multi-FE)
    dof_fe = sum(fe_nlevels) - max(0, len(fe_nlevels) - 1) if fe_nlevels else 0
    dof_resid = max(1, n - k - dof_fe)

    # Scores: s_i = w_i * Xd_i * resid_i
    scores = (w * resid)[:, None] * Xd

    def meat_cluster(cl: np.ndarray) -> Tuple[np.ndarray, int]:
        _, cl_inv = np.unique(cl, return_inverse=True)
        G = int(cl_inv.max()) + 1
        S = np.zeros((G, k), dtype=float)
        for j in range(k):
            S[:, j] = np.bincount(cl_inv, weights=scores[:, j], minlength=G)
        # Small-sample cluster adjustment G/(G-1) * (n-1)/dof_resid
        adj = (G / max(1, G - 1)) * ((n - 1) / dof_resid)
        return adj * (S.T @ S), G

    V1, G1 = meat_cluster(cluster1)
    if cluster2 is not None:
        V2, G2 = meat_cluster(cluster2)
        c12 = np.array([f"{a}___{b}" for a, b in zip(cluster1, cluster2)], dtype=object)
        V12, G12 = meat_cluster(c12)
        meat = V1 + V2 - V12
        # Cameron-Gelbach-Miller PSD eigenvalue truncation safeguard
        cov = XtX_inv @ meat @ XtX_inv
        eigvals, eigvecs = np.linalg.eigh(cov)
        eigvals_pos = np.maximum(eigvals, 0.0)
        cov = (eigvecs * eigvals_pos) @ eigvecs.T
        n_clusters = (G1, G2, G12)
    else:
        cov = XtX_inv @ V1 @ XtX_inv
        n_clusters = (G1,)

    se = np.sqrt(np.maximum(np.diag(cov), 1e-30))
    t_stat = beta / se
    # Use conservative t-df = min(G)-1 if few clusters, else normal
    df_t = max(1, min(n_clusters[:2]) - 1) if len(n_clusters) >= 2 else max(1, n_clusters[0] - 1)
    p_val_t = 2.0 * stats.t.sf(np.abs(t_stat), df=df_t)
    p_val_norm = 2.0 * stats.norm.sf(np.abs(t_stat))

    return {
        "beta": beta.tolist(),
        "se": se.tolist(),
        "t_stat": t_stat.tolist(),
        "p_val_t": p_val_t.tolist(),
        "p_val_norm": p_val_norm.tolist(),
        "df_t": int(df_t),
        "r2_within": float(r2_within),
        "n_obs": int(n),
        "dof_fe": int(dof_fe),
        "n_clusters": [int(g) for g in n_clusters],
    }


def save_json(path: Path, obj: Any) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(obj, indent=2, sort_keys=False).encode("utf-8")
    path.write_bytes(raw)
    return sha256_bytes(raw)
