"""Module 1: 168-Hour Cooldown Notch Bunching & Dominated-Region Agency Audit.

Implements:
  1. Kleven-Waseem (2013) notch-bunching estimator & McCrary-style density jump test
     at elapsed time = 168 hours (604,800 s), separately for:
       - Positive-debt delegated batch rate CUTS vs. HIKES
       - Zero-debt delegated batch updates (Placebo 1: statutory fee == 0 everywhere)
       - Self-managed individual trove CUTS vs. HIKES (Control / Placebo 2: alpha_i == 1)
     Reported strictly across Development (408d), Confirmation (77d), and Pooled (485d)
     with 14-day circular block-bootstrap 95% CIs (n_boot = 999).
  2. Complete transaction-level audit of ALL dominated premature hikes in [160h, 168h)
     and [164h, 168h): exact tx hash, minutes before free, BOLD fees paid, contemporaneous
     branch redemptions (+/-1h, +/-6h, +/-24h), break-even remaining-window redemption
     probability vs. empirical hazard, and manager fee-base expansion under newDebt += upfrontFee.
  3. Revealed-preference implied agency wedge bounds alpha_m.
  4. Total upfront fee burden decomposed by manager (M01..M19), branch, and live immutable
     on-chain RPC permission tuple (minInterestRate, maxInterestRate, minInterestRateChangePeriod),
     conditioning on immutable on-chain manager permissions.
"""
from __future__ import annotations

import json
import math
import sys
import warnings
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np
import pandas as pd
from scipy import stats

warnings.filterwarnings("ignore", category=RuntimeWarning)

from common import (
    BRANCHES,
    COOLDOWN_HOURS,
    COOLDOWN_SECONDS,
    CONF_END_DATE,
    CONF_START_DATE,
    DEV_END_DATE,
    DEV_END_TS,
    DEV_START_DATE,
    EXT_DIR,
    RES_DIR,
    WAD,
    YEAR_SECONDS,
    calc_interest_wei,
    circular_block_bootstrap,
    load_canonical_events,
    load_daily_panels,
    load_batch_rate_ledger,
    manager_label,
    sample_label,
    save_json,
    ts_to_date,
)

# Import read-only canonical Replay machine for exact individual-trove cooldown tracking
from offline_core import Replay  # type: ignore


def extract_individual_rate_moves() -> List[Dict[str, Any]]:
    """Run exact canonical Replay on each branch to extract all individual trove op=3 rate updates
    with exact Solidity-verified elapsed time since last cooldown reset (op in {0,3,7,8,9})."""
    events = load_canonical_events("pooled")
    out: List[Dict[str, Any]] = []
    for b in BRANCHES:
        rep = Replay()
        for e in events[b]:
            rep.apply(e)
        for mv in rep.rate_moves:
            if mv["kind"] != "individual":
                continue
            old_r = int(mv["old_rate"])
            new_r = int(mv["new_rate"])
            if old_r == new_r:
                continue
            ts = int(mv["timestamp"])
            out.append({
                "branch": b,
                "trove": str(mv["controller"]),
                "timestamp": ts,
                "date": ts_to_date(ts),
                "sample": sample_label(ts),
                "block": int(mv["block"]),
                "tx": mv["tx"],
                "old_rate": old_r,
                "new_rate": new_r,
                "direction": "hike" if new_r > old_r else "cut",
                "delta_bps": (new_r - old_r) / 1e14,
                "elapsed_s": int(mv["elapsed"]),
                "elapsed_h": float(mv["elapsed"]) / 3600.0,
                "premature": int(mv["elapsed"]) < COOLDOWN_SECONDS,
                "debt_wei": int(mv["debt_wei"]),
                "debt_bold": float(mv["debt_wei"]) / 1e18,
                "fee_wei": int(mv["upfront_fee_wei"]),
                "fee_bold": float(mv["upfront_fee_wei"]) / 1e18,
            })
    return out


def extract_batch_rate_moves() -> List[Dict[str, Any]]:
    """Load exact canonical batch-rate ledger of all 1,712 canonical batch-manager rate updates,
    enriched with live immutable RPC permission tuples (min/max rate, minPeriod)."""
    batch_ledger = load_batch_rate_ledger()
    perm_path = EXT_DIR / "manager_permissions_rpc.json"
    perms = json.loads(perm_path.read_text(encoding="utf-8")) if perm_path.exists() else {"managers": {}}

    out: List[Dict[str, Any]] = []
    for r in batch_ledger["records"]:
        if not r["changed"]:
            continue
        ts = int(r["timestamp"])
        old_r = int(r["old_rate"])
        new_r = int(r["new_rate"])
        elap = int(r["elapsed"])
        basis = int(r["basis_wei"])
        fee = int(r["fee_wei"])
        mgmt = int(r["management_rate"])
        mgr = str(r["manager"]).lower()
        br = r["branch"]
        p_info = perms.get("managers", {}).get(mgr, {}).get("branches", {}).get(br, {})
        min_p = p_info.get("min_change_period_seconds")
        min_r_pct = p_info.get("min_interest_rate_pct")
        max_r_pct = p_info.get("max_interest_rate_pct")

        out.append({
            "branch": br,
            "manager": mgr,
            "manager_label": manager_label(mgr),
            "timestamp": ts,
            "date": ts_to_date(ts),
            "sample": sample_label(ts),
            "block": int(r["block"]),
            "index": int(r["index"]),
            "tx": r["tx"],
            "old_rate": old_r,
            "new_rate": new_r,
            "management_rate": mgmt,
            "direction": "hike" if new_r > old_r else "cut",
            "delta_bps": (new_r - old_r) / 1e14,
            "elapsed_s": elap,
            "elapsed_h": float(elap) / 3600.0,
            "premature": elap < COOLDOWN_SECONDS,
            "basis_wei": basis,
            "debt_bold": float(basis) / 1e18,
            "fee_wei": fee,
            "fee_bold": float(fee) / 1e18,
            "category": r["category"],
            "avg_rate_lower": int(r["average_rate_lower"]) if r.get("average_rate_lower") is not None else None,
            "avg_rate_upper": int(r["average_rate_upper"]) if r.get("average_rate_upper") is not None else None,
            "min_period_s": int(min_p) if min_p is not None else None,
            "min_rate_pct": float(min_r_pct) if min_r_pct is not None else None,
            "max_rate_pct": float(max_r_pct) if max_r_pct is not None else None,
        })
    return out


def kleven_waseem_bunching(
    elapsed_hours: np.ndarray,
    t_notch: float = 168.0,
    bin_width: float = 1.0,
    max_hour: float = 336.0,
    left_excl: float = 120.0,
    right_excl: float = 172.0,
    poly_order: int = 3,
) -> Dict[str, Any]:
    """Exact Kleven-Waseem (2013) notch-bunching estimator & McCrary-style density jump test.

    Bins elapsed times on [0, max_hour) in bins of width `bin_width`, fits polynomial
    counterfactual C_j outside the excluded region [left_excl, right_excl), computes:
      - Excess bunching mass B in [t_notch, right_excl) and exact 1-hour spike [168, 169)
      - Normalized excess mass b_hat = B / C(168) (units: hours of counterfactual density)
      - Missing mass M in [left_excl, t_notch) and missing-mass share m_share = M / sum(C_left)
      - Hourly density jump ratio: rate in [168,169) vs mean hourly rate in [120,168) and [169,240)
      - Exact binomial/Poisson one-sided test of [168,169) spike vs exterior [169,240) and vs [120,168)
      - McCrary-style local-linear log-density jump at 168h (bandwidth = 48h on left and right)
    """
    eh = np.asarray(elapsed_hours, dtype=float)
    n_total = int(len(eh))
    n_premature = int(np.sum(eh < t_notch))
    n_post = int(np.sum(eh >= t_notch))
    frac_premature = float(n_premature / n_total) if n_total > 0 else float("nan")

    # Exact counts in diagnostic windows
    n_160_168 = int(np.sum((eh >= 160.0) & (eh < 168.0)))
    n_164_168 = int(np.sum((eh >= 164.0) & (eh < 168.0)))
    n_120_168 = int(np.sum((eh >= 120.0) & (eh < 168.0)))
    n_168_169 = int(np.sum((eh >= 168.0) & (eh < 169.0)))
    n_168_172 = int(np.sum((eh >= 168.0) & (eh < 172.0)))
    n_169_240 = int(np.sum((eh >= 169.0) & (eh < 240.0)))
    n_172_240 = int(np.sum((eh >= 172.0) & (eh < 240.0)))

    # Exact hourly densities
    dens_120_168 = n_120_168 / 48.0
    dens_168_169 = float(n_168_169) / 1.0
    dens_169_240 = n_169_240 / 71.0
    dens_172_240 = n_172_240 / 68.0

    # Density jump ratio at notch: [168,169) vs [120,168) (with Laplace +0.5/48 lower bound when 0)
    if n_120_168 > 0:
        jump_ratio_vs_left = dens_168_169 / dens_120_168
    else:
        jump_ratio_vs_left = float("inf") if n_168_169 > 0 else 1.0
    # Conservative Poisson 95% upper bound for 0 observations in 48h is 3.0/48h -> exact lower bound on jump ratio
    jump_ratio_vs_left_lower95 = (
        dens_168_169 / (2.99573 / 48.0) if (n_120_168 == 0 and n_168_169 > 0) else jump_ratio_vs_left
    )
    jump_ratio_vs_right = dens_168_169 / dens_169_240 if dens_169_240 > 0 else (float("inf") if n_168_169 > 0 else 1.0)

    # Exact binomial test comparing 1-hour spike [168,169) against [120,169) (null p = 1/49)
    n_120_169 = n_120_168 + n_168_169
    p_binom_left = float(stats.binomtest(n_168_169, n_120_169, p=1.0 / 49.0, alternative="greater").pvalue) if n_120_169 > 0 else 1.0
    # Exact binomial test comparing [168,169) against [168,240) (null p = 1/72)
    n_168_240 = n_168_169 + n_169_240
    p_binom_right = float(stats.binomtest(n_168_169, n_168_240, p=1.0 / 72.0, alternative="greater").pvalue) if n_168_240 > 0 else 1.0

    # Histogram on [0, max_hour)
    edges = np.arange(0.0, max_hour + bin_width, bin_width)
    counts, _ = np.histogram(eh, bins=edges)
    centers = 0.5 * (edges[:-1] + edges[1:])

    # Fit polynomial on exterior bins (excluding [left_excl, right_excl) and initial [0, 12h) transient if needed)
    # Use [12h, left_excl) U [right_excl, max_hour) so immediate post-event clustering at <12h doesn't distort notch fit
    fit_mask = ((centers >= 12.0) & (centers < left_excl)) | ((centers >= right_excl) & (centers < max_hour))
    x_fit = (centers[fit_mask] - t_notch) / 100.0
    y_fit = counts[fit_mask].astype(float)

    if len(x_fit) > poly_order + 2 and np.sum(y_fit) > 0:
        V = np.vander(x_fit, N=poly_order + 1, increasing=True)
        coef, *_ = np.linalg.lstsq(V, y_fit, rcond=None)
        V_all = np.vander((centers - t_notch) / 100.0, N=poly_order + 1, increasing=True)
        c_hat = np.maximum(V_all @ coef, 1e-6)
    else:
        mean_ext = max(float(np.mean(y_fit)) if len(y_fit) else 1e-6, 1e-6)
        c_hat = np.full_like(centers, mean_ext)

    # Also compute a strictly post-notch counterfactual from [right_excl, max_hour) for clean comparison
    # (critical for cuts where left density is near-zero and global polynomial can extrapolate low)
    right_mask = (centers >= right_excl) & (centers < min(max_hour, 288.0))
    c_right_avg = max(float(np.mean(counts[right_mask])) if np.any(right_mask) else 1e-6, 1e-6)

    bunch_mask_4h = (centers >= t_notch) & (centers < right_excl)
    bunch_mask_1h = (centers >= t_notch) & (centers < t_notch + 1.0)
    miss_mask = (centers >= left_excl) & (centers < t_notch)

    c_at_notch = float(np.mean(c_hat[bunch_mask_1h]))
    B_4h = float(np.sum(counts[bunch_mask_4h] - c_hat[bunch_mask_4h]))
    B_1h = float(np.sum(counts[bunch_mask_1h] - c_hat[bunch_mask_1h]))
    b_kw_4h = float(B_4h / c_at_notch) if c_at_notch > 0 else float("nan")
    b_kw_1h = float(B_1h / c_at_notch) if c_at_notch > 0 else float("nan")
    # Post-notch benchmark b_hat using right-side average density (most conservative / transparent!)
    b_post_1h = float((n_168_169 - c_right_avg) / c_right_avg) if c_right_avg > 0 else float("nan")
    b_post_4h = float((n_168_172 - 4.0 * c_right_avg) / c_right_avg) if c_right_avg > 0 else float("nan")

    M_left = float(np.sum(c_hat[miss_mask] - counts[miss_mask]))
    C_left_sum = float(np.sum(c_hat[miss_mask]))
    miss_share = float(M_left / C_left_sum) if C_left_sum > 0 else float("nan")

    # McCrary-style local linear log-density discontinuity at 168h (bw = 24h on left/right, triangular kernel)
    bw = 24.0
    def local_linear_boundary(side: str) -> Tuple[float, float]:
        if side == "left":
            m = (centers >= t_notch - bw) & (centers < t_notch)
            u = (t_notch - centers[m]) / bw
        else:
            m = (centers >= t_notch) & (centers < t_notch + bw)
            u = (centers[m] - t_notch) / bw
        w = np.maximum(1.0 - u, 0.0)
        y = counts[m].astype(float)
        if np.sum(w) <= 0:
            return 0.0, 0.0
        X = np.column_stack([np.ones_like(u), u])
        W = np.diag(w)
        beta = np.linalg.pinv(X.T @ W @ X) @ (X.T @ W @ y)
        f_hat = max(float(beta[0]), 0.0)
        # Poisson variance of local linear estimator at boundary
        A = np.linalg.pinv(X.T @ W @ X)
        V_p = A @ (X.T @ np.diag((w**2) * np.maximum(y, 0.25)) @ X) @ A
        se_f = math.sqrt(max(float(V_p[0, 0]), 1e-12))
        return f_hat, se_f

    f_left, se_left = local_linear_boundary("left")
    f_right, se_right = local_linear_boundary("right")
    eps_smooth = 0.02
    theta_mccrary = math.log(f_right + eps_smooth) - math.log(f_left + eps_smooth)
    se_theta = math.sqrt((se_right / (f_right + eps_smooth)) ** 2 + (se_left / (f_left + eps_smooth)) ** 2)
    z_mccrary = theta_mccrary / se_theta if se_theta > 0 else 0.0
    p_mccrary = float(2.0 * stats.norm.sf(abs(z_mccrary)))

    return {
        "n_total": n_total,
        "n_premature": n_premature,
        "n_post_cooldown": n_post,
        "frac_premature": frac_premature,
        "n_in_120_168": n_120_168,
        "n_in_160_168": n_160_168,
        "n_in_164_168": n_164_168,
        "n_in_168_169": n_168_169,
        "n_in_168_172": n_168_172,
        "n_in_169_240": n_169_240,
        "share_in_first_free_hour": float(n_168_169 / n_total) if n_total > 0 else float("nan"),
        "hourly_dens_120_168": dens_120_168,
        "hourly_dens_168_169": dens_168_169,
        "hourly_dens_169_240": dens_169_240,
        "jump_ratio_vs_120_168": jump_ratio_vs_left if np.isfinite(jump_ratio_vs_left) else None,
        "jump_ratio_vs_120_168_lower95": jump_ratio_vs_left_lower95,
        "jump_ratio_vs_169_240": jump_ratio_vs_right if np.isfinite(jump_ratio_vs_right) else None,
        "p_binom_vs_left": p_binom_left,
        "p_binom_vs_right": p_binom_right,
        "kw_poly_order": poly_order,
        "kw_c_at_168": c_at_notch,
        "kw_c_right_avg": c_right_avg,
        "kw_B_1h": B_1h,
        "kw_B_4h": B_4h,
        "kw_b_1h": b_kw_1h,
        "kw_b_4h": b_kw_4h,
        "kw_b_post_1h": b_post_1h,
        "kw_b_post_4h": b_post_4h,
        "kw_missing_mass_120_168": M_left,
        "kw_missing_share": miss_share,
        "mccrary_f_left": f_left,
        "mccrary_f_right": f_right,
        "mccrary_log_jump": theta_mccrary,
        "mccrary_se": se_theta,
        "mccrary_z": z_mccrary,
        "mccrary_p": p_mccrary,
        "hist_1h_counts_0_336": counts.tolist(),
    }


def bootstrap_notch_group(rows: List[Dict[str, Any]], all_dates: Sequence[str], poly_order: int = 3) -> Dict[str, Any]:
    """Compute point estimates + 14d circular block-bootstrap 95% CIs for a notch subgroup."""
    by_date: Dict[str, List[float]] = defaultdict(list)
    for r in rows:
        by_date[r["date"]].append(float(r["elapsed_h"]))

    eh_all = np.array([r["elapsed_h"] for r in rows], dtype=float)
    point = kleven_waseem_bunching(eh_all, poly_order=poly_order)

    # Also compute p=5 polynomial robustness point estimate
    point_p5 = kleven_waseem_bunching(eh_all, poly_order=5)
    point["kw_b_4h_poly5"] = point_p5["kw_b_4h"]
    point["kw_b_1h_poly5"] = point_p5["kw_b_1h"]

    # 14d circular block bootstrap on key scalar metrics
    def sample_eh(dlist: Sequence[str]) -> np.ndarray:
        vals: List[float] = []
        for d in dlist:
            vals.extend(by_date.get(d, ()))
        return np.asarray(vals, dtype=float)

    def stat_frac_prem(dlist: Sequence[str]) -> float:
        a = sample_eh(dlist)
        return float(np.mean(a < 168.0)) if len(a) else float("nan")

    def stat_share_168_169(dlist: Sequence[str]) -> float:
        a = sample_eh(dlist)
        return float(np.mean((a >= 168.0) & (a < 169.0))) if len(a) else float("nan")

    def stat_b_post_1h(dlist: Sequence[str]) -> float:
        a = sample_eh(dlist)
        if len(a) < 5:
            return float("nan")
        n_168 = np.sum((a >= 168.0) & (a < 169.0))
        n_right = np.sum((a >= 172.0) & (a < 288.0))
        c_r = n_right / 116.0
        if c_r <= 0:
            return float("nan")
        return float((n_168 - c_r) / c_r)

    def stat_kw_b_1h(dlist: Sequence[str]) -> float:
        a = sample_eh(dlist)
        if len(a) < 10:
            return float("nan")
        res = kleven_waseem_bunching(a, poly_order=poly_order)
        return float(res["kw_b_1h"])

    def stat_kw_b_4h(dlist: Sequence[str]) -> float:
        a = sample_eh(dlist)
        if len(a) < 10:
            return float("nan")
        res = kleven_waseem_bunching(a, poly_order=poly_order)
        return float(res["kw_b_4h"])

    point["boot_frac_premature"] = circular_block_bootstrap(all_dates, stat_frac_prem, block_len=14, n_boot=999, seed=20261123)
    point["boot_share_first_free_hour"] = circular_block_bootstrap(all_dates, stat_share_168_169, block_len=14, n_boot=999, seed=20261124)
    point["boot_b_post_1h"] = circular_block_bootstrap(all_dates, stat_b_post_1h, block_len=14, n_boot=999, seed=20261125)
    point["boot_kw_b_1h"] = circular_block_bootstrap(all_dates, stat_kw_b_1h, block_len=14, n_boot=999, seed=20261127)
    point["boot_kw_b_4h"] = circular_block_bootstrap(all_dates, stat_kw_b_4h, block_len=14, n_boot=999, seed=20261126)
    return point


def audit_dominated_premature_hikes(batch_moves: List[Dict[str, Any]], events: Dict[str, List[Dict[str, Any]]]) -> Dict[str, Any]:
    """Full transaction-level audit of ALL dominated premature hikes in [160h, 168h) and [164h, 168h).

    Strict causal and tie-aware accounting:
      - Strictly separates PRE-hike redemptions [-w, 0] (known to manager) from POST-hike (0, +w]
      - Computes exact pre-hike queue quantile `pre_q` from daily active trove debt distribution
      - Checks `maxInterestRate` ceiling constraint on every near-notch hike
      - Computes sample-specific unconditional redemption hazards (Dev 408d / Conf 77d) with zero leakage
      - Reports fee-base expansion separately for premature hikes only AND all paid batch updates (incl. cuts)
    """
    # Collect all branch redemption timestamps, sample labels & BOLD amounts
    red_by_branch: Dict[str, List[Tuple[int, float, str]]] = {b: [] for b in BRANCHES}
    for b in BRANCHES:
        for e in events[b]:
            if e["name"] == "Redemption":
                ts_r = int(e["timestamp"])
                red_by_branch[b].append((ts_r, float(e["fields"]["actualBoldAmount"]) / 1e18, sample_label(ts_r)))
        red_by_branch[b].sort(key=lambda x: x[0])

    # Strictly sample-specific unconditional hourly redemption arrival rates (zero Dev/Conf leakage!)
    sample_hours = {"development": 408.0 * 24.0, "confirmation": 77.0 * 24.0, "pooled": 485.0 * 24.0}
    uncond_hourly_red_by_sample: Dict[str, Dict[str, float]] = {}
    for samp, hrs in sample_hours.items():
        uncond_hourly_red_by_sample[samp] = {
            b: sum(1 for _, _, s in red_by_branch[b] if samp == "pooled" or s == samp) / hrs
            for b in BRANCHES
        }

    # Pre-hike queue quantile lookup from canonical daily panel (active debt distribution per branch-day)
    panel = load_daily_panels("pooled")
    panel_pos = panel[panel["debt_bold"] > 0][["branch", "date", "base_apr_bps", "debt_bold"]]
    bd_queue_cache: Dict[Tuple[str, str], Tuple[np.ndarray, np.ndarray]] = {}
    for (b_k, d_k), grp in panel_pos.groupby(["branch", "date"]):
        bd_queue_cache[(str(b_k), str(d_k))] = (
            grp["base_apr_bps"].to_numpy(dtype=float),
            grp["debt_bold"].to_numpy(dtype=float),
        )

    def pre_hike_queue_interval(branch: str, ts: int, old_rate_bps: float) -> Tuple[Optional[float], Optional[float], Optional[float]]:
        """Strictly pre-hike tied-block queue interval [q_lo, q_hi] using previous-day 23:59:59 UTC
        snapshot (fallback same-day if day 0), matching offline_core.py's [debt_below, debt_at_or_below]."""
        d_prev = ts_to_date(ts - 86400)
        arr = bd_queue_cache.get((branch, d_prev)) or bd_queue_cache.get((branch, ts_to_date(ts)))
        if arr is None:
            return None, None, None
        rates, debts = arr
        tot = float(np.sum(debts))
        if tot <= 0:
            return None, None, None
        q_lo = float(np.sum(debts[rates < old_rate_bps - 1e-4]) / tot)
        q_hi = float(np.sum(debts[rates <= old_rate_bps + 1e-4]) / tot)
        return q_lo, q_hi, 0.5 * (q_lo + q_hi)

    def redemptions_directed(branch: str, ts: int, win_s: int, direction: str) -> Tuple[int, float]:
        """direction='pre': [ts - win_s, ts]; 'post': (ts, ts + win_s]; 'both': [ts - win_s, ts + win_s]."""
        cnt = 0
        vol = 0.0
        for rts, rvol, _ in red_by_branch[branch]:
            dt = rts - ts
            if direction == "pre" and (-win_s <= dt <= 0):
                cnt += 1
                vol += rvol
            elif direction == "post" and (0 < dt <= win_s):
                cnt += 1
                vol += rvol
            elif direction == "both" and (-win_s <= dt <= win_s):
                cnt += 1
                vol += rvol
        return cnt, vol

    # Positive-debt premature hikes & all paid updates (incl. cuts)
    pos_prem_hikes = [
        r for r in batch_moves
        if r["direction"] == "hike" and r["basis_wei"] > 0 and r["premature"] and r["fee_wei"] > 0
    ]
    all_paid_updates = [r for r in batch_moves if r["basis_wei"] > 0 and r["fee_wei"] > 0]

    near_160: List[Dict[str, Any]] = []
    near_164: List[Dict[str, Any]] = []
    total_fee_base_expansion_hikes_bold_yr = 0.0
    total_fee_base_expansion_all_paid_bold_yr = sum(
        r["fee_bold"] * (r["management_rate"] / 1e18) for r in all_paid_updates
    )
    total_prem_hike_fees_bold = 0.0

    for r in pos_prem_hikes:
        fee_bold = r["fee_bold"]
        total_prem_hike_fees_bold += fee_bold
        mgmt_rate = r["management_rate"] / 1e18
        # Contract line WETH_BorrowerOperations.sol: newDebt += upfrontFee; newWeightedMgmtFee = newDebt * annualManagementFee
        annual_mgmt_gain = fee_bold * mgmt_rate
        total_fee_base_expansion_hikes_bold_yr += annual_mgmt_gain

        if r["elapsed_h"] >= 160.0:
            mins_before_free = (COOLDOWN_SECONDS - r["elapsed_s"]) / 60.0
            rem_hours = mins_before_free / 60.0
            inc_7d_wei = calc_interest_wei(r["basis_wei"], r["new_rate"] - r["old_rate"], COOLDOWN_SECONDS)
            inc_7d_bold = inc_7d_wei / 1e18
            overcharge_ratio = fee_bold / inc_7d_bold if inc_7d_bold > 0 else float("inf")
            fee_bps = (fee_bold / r["debt_bold"]) * 10000.0 if r["debt_bold"] > 0 else 0.0

            pre1_c, pre1_v = redemptions_directed(r["branch"], r["timestamp"], 3600, "pre")
            post1_c, post1_v = redemptions_directed(r["branch"], r["timestamp"], 3600, "post")
            pre6_c, pre6_v = redemptions_directed(r["branch"], r["timestamp"], 6 * 3600, "pre")
            post6_c, post6_v = redemptions_directed(r["branch"], r["timestamp"], 6 * 3600, "post")
            pre24_c, pre24_v = redemptions_directed(r["branch"], r["timestamp"], 24 * 3600, "pre")
            post24_c, post24_v = redemptions_directed(r["branch"], r["timestamp"], 24 * 3600, "post")

            c1, v1 = pre1_c + post1_c, pre1_v + post1_v
            c6, v6 = pre6_c + post6_c, pre6_v + post6_v
            c24, v24 = pre24_c + post24_c, pre24_v + post24_v

            pre_q_lo, pre_q_hi, pre_q_mid = pre_hike_queue_interval(r["branch"], r["timestamp"], r["old_rate"] / 1e14)
            new_r_pct = r["new_rate"] / 1e16
            max_r_pct = r.get("max_rate_pct")
            ceiling_constrained = bool(max_r_pct is not None and new_r_pct >= max_r_pct - 0.01)

            # Break-even probability at benchmark net disruption cost c_net = 2.0% (200 bps)
            p_be_2pct = (fee_bps / 200.0)
            req_annual_red_rate = p_be_2pct / max(rem_hours / 8760.0, 1e-9)
            # Sample-specific unconditional branch hazard (zero Dev/Conf leakage)
            lam_hr_samp = uncond_hourly_red_by_sample[r["sample"]][r["branch"]]
            p_branch_uncond = 1.0 - math.exp(-lam_hr_samp * rem_hours)
            alpha_upper_if_uncond = (p_branch_uncond * 200.0) / fee_bps if fee_bps > 0 else 1.0

            row = {
                "tx": r["tx"],
                "utc": datetime.fromtimestamp(r["timestamp"], tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
                "sample": r["sample"],
                "branch": r["branch"],
                "manager_label": r["manager_label"],
                "manager": r["manager"],
                "min_period_s": r.get("min_period_s"),
                "max_rate_pct": max_r_pct,
                "max_rate_ceiling_constrained": ceiling_constrained,
                "pre_hike_queue_lo": round(pre_q_lo, 4) if pre_q_lo is not None else None,
                "pre_hike_queue_hi": round(pre_q_hi, 4) if pre_q_hi is not None else None,
                "pre_hike_queue_mid": round(pre_q_mid, 4) if pre_q_mid is not None else None,
                "pre_hike_queue_interval": [round(pre_q_lo, 4), round(pre_q_hi, 4)] if pre_q_lo is not None else None,
                "elapsed_h": round(r["elapsed_h"], 4),
                "minutes_before_free": round(mins_before_free, 2),
                "old_rate_pct": round(r["old_rate"] / 1e16, 4),
                "new_rate_pct": round(new_r_pct, 4),
                "delta_bps": round(r["delta_bps"], 2),
                "debt_bold": round(r["debt_bold"], 2),
                "fee_bold": round(fee_bold, 2),
                "fee_bps": round(fee_bps, 4),
                "inc_7d_interest_bold": round(inc_7d_bold, 2),
                "overcharge_ratio": round(overcharge_ratio, 2),
                "pre_1h_red_count": pre1_c,
                "pre_1h_red_bold": round(pre1_v, 2),
                "post_1h_red_count": post1_c,
                "post_1h_red_bold": round(post1_v, 2),
                "pre_6h_red_count": pre6_c,
                "pre_6h_red_bold": round(pre6_v, 2),
                "post_6h_red_count": post6_c,
                "post_6h_red_bold": round(post6_v, 2),
                "pre_24h_red_count": pre24_c,
                "pre_24h_red_bold": round(pre24_v, 2),
                "post_24h_red_count": post24_c,
                "post_24h_red_bold": round(post24_v, 2),
                "redemptions_pm_1h_count": c1,
                "redemptions_pm_1h_bold": round(v1, 2),
                "redemptions_pm_6h_count": c6,
                "redemptions_pm_6h_bold": round(v6, 2),
                "redemptions_pm_24h_count": c24,
                "redemptions_pm_24h_bold": round(v24, 2),
                "breakeven_prob_at_2pct_cost": round(p_be_2pct, 4),
                "required_annual_hit_rate_at_2pct": round(req_annual_red_rate, 1),
                "uncond_branch_red_prob_rem_window_in_sample": round(p_branch_uncond, 4),
                "implied_alpha_upper_bound": round(min(1.0, alpha_upper_if_uncond), 4),
                "manager_mgmt_rate_pct": round(mgmt_rate * 100.0, 4),
                "manager_annual_fee_base_gain_bold": round(annual_mgmt_gain, 4),
            }
            near_160.append(row)
            if r["elapsed_h"] >= 164.0:
                near_164.append(row)

    near_160.sort(key=lambda x: x["minutes_before_free"])
    near_164.sort(key=lambda x: x["minutes_before_free"])

    # Also audit ALL 7 premature positive-debt cuts to verify revealed-preference rationality on cuts!
    prem_cuts_audit = []
    for r in batch_moves:
        if r["direction"] == "cut" and r["basis_wei"] > 0 and r["premature"]:
            rem_s = COOLDOWN_SECONDS - r["elapsed_s"]
            saved_interest_bold = calc_interest_wei(r["basis_wei"], r["old_rate"] - r["new_rate"], rem_s) / 1e18
            net_gain_bold = saved_interest_bold - r["fee_bold"]
            prem_cuts_audit.append({
                "tx": r["tx"],
                "utc": datetime.fromtimestamp(r["timestamp"], tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
                "sample": r["sample"],
                "branch": r["branch"],
                "manager_label": r["manager_label"],
                "elapsed_h": round(r["elapsed_h"], 3),
                "old_rate_pct": round(r["old_rate"] / 1e16, 4),
                "new_rate_pct": round(r["new_rate"] / 1e16, 4),
                "cut_bps": round((r["old_rate"] - r["new_rate"]) / 1e14, 2),
                "debt_bold": round(r["debt_bold"], 2),
                "fee_bold": round(r["fee_bold"], 2),
                "saved_interest_remaining_cooldown_bold": round(saved_interest_bold, 2),
                "net_interest_minus_fee_bold": round(net_gain_bold, 2),
                "strictly_profitable_cut": bool(net_gain_bold > 0),
            })

    return {
        "n_pos_premature_hikes_total": len(pos_prem_hikes),
        "total_pos_premature_hike_fees_bold": round(total_prem_hike_fees_bold, 2),
        "total_manager_annual_fee_base_gain_bold_per_yr": round(total_fee_base_expansion_hikes_bold_yr, 2),
        "total_manager_annual_fee_base_gain_hikes_only_bold_per_yr": round(total_fee_base_expansion_hikes_bold_yr, 2),
        "total_manager_annual_fee_base_gain_all_paid_bold_per_yr": round(total_fee_base_expansion_all_paid_bold_yr, 2),
        "fee_base_gain_scope_note": (
            "hikes_only covers the 345 positive-debt premature rate hikes (+$1,159.82/yr); "
            "all_paid also includes the 7 positive-debt premature cuts (+$1,191.72/yr)."
        ),
        "uncond_hourly_redemption_rate_by_sample": {
            s: {b: round(v, 6) for b, v in d.items()} for s, d in uncond_hourly_red_by_sample.items()
        },
        "near_notch_160_168": {
            "count": len(near_160),
            "total_fee_bold": round(sum(x["fee_bold"] for x in near_160), 2),
            "n_ceiling_constrained": sum(1 for x in near_160 if x["max_rate_ceiling_constrained"]),
            "zero_pre6h_redemptions_count": sum(1 for x in near_160 if x["pre_6h_red_count"] == 0),
            "zero_pre6h_redemptions_fee_bold": round(sum(x["fee_bold"] for x in near_160 if x["pre_6h_red_count"] == 0), 2),
            "zero_both6h_redemptions_count": sum(1 for x in near_160 if x["redemptions_pm_6h_count"] == 0),
            "zero_both6h_redemptions_fee_bold": round(sum(x["fee_bold"] for x in near_160 if x["redemptions_pm_6h_count"] == 0), 2),
            "events": near_160,
        },
        "near_notch_164_168": {
            "count": len(near_164),
            "total_fee_bold": round(sum(x["fee_bold"] for x in near_164), 2),
            "n_ceiling_constrained": sum(1 for x in near_164 if x["max_rate_ceiling_constrained"]),
            "zero_pre6h_redemptions_count": sum(1 for x in near_164 if x["pre_6h_red_count"] == 0),
            "zero_pre6h_redemptions_fee_bold": round(sum(x["fee_bold"] for x in near_164 if x["pre_6h_red_count"] == 0), 2),
            "zero_both6h_redemptions_count": sum(1 for x in near_164 if x["redemptions_pm_6h_count"] == 0),
            "zero_both6h_redemptions_fee_bold": round(sum(x["fee_bold"] for x in near_164 if x["redemptions_pm_6h_count"] == 0), 2),
            "events": near_164,
        },
        "premature_cuts_rationality_check": {
            "count": len(prem_cuts_audit),
            "n_strictly_profitable": sum(1 for x in prem_cuts_audit if x["strictly_profitable_cut"]),
            "events": prem_cuts_audit,
        },
    }


def decompose_by_manager_branch_permissions(batch_moves: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Link total upfront fee burden by manager, branch, and live immutable RPC permission tuple (closing F15)."""
    perm_path = EXT_DIR / "manager_permissions_rpc.json"
    perms = json.loads(perm_path.read_text(encoding="utf-8")) if perm_path.exists() else {"managers": {}}

    by_mgr_branch: Dict[Tuple[str, str], Dict[str, Any]] = {}
    by_mgr: Dict[str, Dict[str, Any]] = {}
    by_perm_tuple: Dict[str, Dict[str, Any]] = {}

    for r in batch_moves:
        m = r["manager"]
        ml = r["manager_label"]
        b = r["branch"]
        p_info = perms.get("managers", {}).get(m, {}).get("branches", {}).get(b, {})
        min_r = p_info.get("min_interest_rate_pct")
        max_r = p_info.get("max_interest_rate_pct")
        min_p = p_info.get("min_change_period_seconds")
        ptuple = f"[{min_r}%, {max_r}%, {min_p}s]" if min_p is not None else "UNAVAILABLE"

        for bucket, key in [(by_mgr_branch, (ml, b)), (by_mgr, ml), (by_perm_tuple, ptuple)]:
            rec = bucket.setdefault(key, {
                "n_updates": 0,
                "n_pos_debt_updates": 0,
                "n_pos_hikes": 0,
                "n_pos_prem_hikes": 0,
                "n_pos_cuts": 0,
                "n_pos_prem_cuts": 0,
                "fee_total_bold": 0.0,
                "fee_dev_bold": 0.0,
                "fee_conf_bold": 0.0,
                "fee_hikes_bold": 0.0,
                "fee_cuts_bold": 0.0,
                "annual_mgmt_gain_bold": 0.0,
            })
            rec["n_updates"] += 1
            if r["basis_wei"] > 0:
                rec["n_pos_debt_updates"] += 1
                if r["direction"] == "hike":
                    rec["n_pos_hikes"] += 1
                    if r["premature"]:
                        rec["n_pos_prem_hikes"] += 1
                else:
                    rec["n_pos_cuts"] += 1
                    if r["premature"]:
                        rec["n_pos_prem_cuts"] += 1
            rec["fee_total_bold"] += r["fee_bold"]
            if r["sample"] == "development":
                rec["fee_dev_bold"] += r["fee_bold"]
            else:
                rec["fee_conf_bold"] += r["fee_bold"]
            if r["direction"] == "hike":
                rec["fee_hikes_bold"] += r["fee_bold"]
            else:
                rec["fee_cuts_bold"] += r["fee_bold"]
            rec["annual_mgmt_gain_bold"] += r["fee_bold"] * (r["management_rate"] / 1e18)

            if bucket is by_mgr_branch:
                rec["manager_label"] = ml
                rec["manager"] = m
                rec["branch"] = b
                rec["min_rate_pct"] = min_r
                rec["max_rate_pct"] = max_r
                rec["min_period_s"] = min_p
                rec["permission_tuple"] = ptuple

    # Format clean lists
    mgr_branch_list = sorted(by_mgr_branch.values(), key=lambda x: -x["fee_total_bold"])
    for x in mgr_branch_list:
        for k in ("fee_total_bold", "fee_dev_bold", "fee_conf_bold", "fee_hikes_bold", "fee_cuts_bold", "annual_mgmt_gain_bold"):
            x[k] = round(x[k], 2)

    perm_summary = []
    for pt, v in sorted(by_perm_tuple.items(), key=lambda kv: -kv[1]["fee_total_bold"]):
        row = dict(v, permission_tuple=pt)
        for k in ("fee_total_bold", "fee_dev_bold", "fee_conf_bold", "fee_hikes_bold", "fee_cuts_bold", "annual_mgmt_gain_bold"):
            row[k] = round(row[k], 2)
        perm_summary.append(row)

    # Also summarize all registered tuples from RPC directly
    all_reg = perms.get("summary_rows", [])
    min_periods_dist: Dict[int, int] = defaultdict(int)
    max_rates_dist: Dict[float, int] = defaultdict(int)
    for row in all_reg:
        min_periods_dist[int(row["min_period_s"])] += 1
        max_rates_dist[float(row["max_rate_pct"])] += 1

    return {
        "rpc_block_number": perms.get("queried_block_number"),
        "n_registered_manager_branches": len(all_reg),
        "min_change_period_distribution_seconds": dict(sorted(min_periods_dist.items())),
        "max_rate_pct_distribution": dict(sorted(max_rates_dist.items())),
        "by_permission_tuple": perm_summary,
        "by_manager_branch": mgr_branch_list,
    }


def main() -> None:
    print("=== Module 1: 168h Cooldown Notch Bunching & Dominated-Region Agency Audit ===")
    batch_moves = extract_batch_rate_moves()
    indiv_moves = extract_individual_rate_moves()
    events = load_canonical_events("pooled")

    dev_dates = pd.date_range(DEV_START_DATE, DEV_END_DATE, freq="D").strftime("%Y-%m-%d").tolist()
    conf_dates = pd.date_range(CONF_START_DATE, CONF_END_DATE, freq="D").strftime("%Y-%m-%d").tolist()
    pooled_dates = dev_dates + conf_dates

    sample_date_map = {
        "development": dev_dates,
        "confirmation": conf_dates,
        "pooled": pooled_dates,
    }

    notch_results: Dict[str, Dict[str, Any]] = {}
    for samp in ("development", "confirmation", "pooled"):
        bm = [r for r in batch_moves if samp == "pooled" or r["sample"] == samp]
        im = [r for r in indiv_moves if samp == "pooled" or r["sample"] == samp]
        dates = sample_date_map[samp]

        # Primary notch-bunching sample strictly excludes hardcoded 604,800s (7-day) on-chain revert-wall
        # managers, isolating managers who actually face the economic 168h cooldown fee notch!
        bm_notch = [r for r in bm if r.get("min_period_s") is not None and int(r["min_period_s"]) < COOLDOWN_SECONDS]
        bm_1h = [r for r in bm if r.get("min_period_s") is not None and int(r["min_period_s"]) <= 3601]
        bm_24h = [r for r in bm if r.get("min_period_s") is not None and int(r["min_period_s"]) == 86400]
        bm_wall = [r for r in bm if r.get("min_period_s") is not None and int(r["min_period_s"]) >= COOLDOWN_SECONDS]

        groups = {
            # PRIMARY economic-notch groups (minPeriod < 604,800s: 1h & 24h managers)
            "batch_pos_cuts": [r for r in bm_notch if r["basis_wei"] > 0 and r["direction"] == "cut"],
            "batch_pos_hikes": [r for r in bm_notch if r["basis_wei"] > 0 and r["direction"] == "hike"],
            "batch_zero_debt_1h_24h": [r for r in bm_notch if r["basis_wei"] == 0],
            # 1h-only (<=3,601s) robustness & clean baseline keeper-bot floor
            "batch_pos_cuts_1h_only": [r for r in bm_1h if r["basis_wei"] > 0 and r["direction"] == "cut"],
            "batch_pos_hikes_1h_only": [r for r in bm_1h if r["basis_wei"] > 0 and r["direction"] == "hike"],
            "batch_zero_debt_1h_only": [r for r in bm_1h if r["basis_wei"] == 0],
            # 24h-only (86,400s) subgroup
            "batch_pos_cuts_24h_only": [r for r in bm_24h if r["basis_wei"] > 0 and r["direction"] == "cut"],
            "batch_pos_hikes_24h_only": [r for r in bm_24h if r["basis_wei"] > 0 and r["direction"] == "hike"],
            "batch_zero_debt_24h_only": [r for r in bm_24h if r["basis_wei"] == 0],
            # Hardcoded 7-day on-chain revert-wall group (minPeriod == 604,800s; separated from economic notch!)
            "batch_revert_wall_604800s_zero_debt": [r for r in bm_wall if r["basis_wei"] == 0],
            "batch_revert_wall_604800s_pos_cuts": [r for r in bm_wall if r["basis_wei"] > 0 and r["direction"] == "cut"],
            "batch_revert_wall_604800s_pos_hikes": [r for r in bm_wall if r["basis_wei"] > 0 and r["direction"] == "hike"],
            # Unfiltered all-manager reference (includes revert-wall managers)
            "batch_pos_cuts_all_unfiltered": [r for r in bm if r["basis_wei"] > 0 and r["direction"] == "cut"],
            "batch_pos_hikes_all_unfiltered": [r for r in bm if r["basis_wei"] > 0 and r["direction"] == "hike"],
            "batch_zero_debt_all_unfiltered": [r for r in bm if r["basis_wei"] == 0],
            # Self-managed individual troves (alpha_i == 1 control)
            "individual_cuts_control": [r for r in im if r["direction"] == "cut"],
            "individual_hikes_control": [r for r in im if r["direction"] == "hike"],
            "individual_all_control": im,
        }
        notch_results[samp] = {}
        for gname, grows in groups.items():
            res = bootstrap_notch_group(grows, dates)
            notch_results[samp][gname] = res
            if gname in (
                "batch_pos_cuts", "batch_pos_hikes", "batch_zero_debt_1h_24h",
                "batch_pos_cuts_1h_only", "batch_pos_hikes_1h_only", "batch_zero_debt_1h_only",
                "batch_revert_wall_604800s_zero_debt", "individual_cuts_control", "individual_hikes_control",
            ):
                print(
                    f"  [{samp:12s}] {gname:34s}: N={res['n_total']:4d} | prem={res['n_premature']:3d} ({res['frac_premature']*100:5.1f}%) "
                    f"| [120,168)={res['n_in_120_168']:2d} | [168,169)={res['n_in_168_169']:3d} ({res['share_in_first_free_hour']*100:5.1f}%) "
                    f"| b_post_1h={res['kw_b_post_1h']:6.1f} | kw_b_4h={res['kw_b_4h']:6.1f} | p_left={res['p_binom_vs_left']:.2e}"
                )

    # Difference-in-premature-rate tests (PRIMARY: minPeriod < 604,800s economic-notch sample + 1h-only robustness)
    pooled_bh = notch_results["pooled"]["batch_pos_hikes"]
    pooled_bc = notch_results["pooled"]["batch_pos_cuts"]
    pooled_bh_1h = notch_results["pooled"]["batch_pos_hikes_1h_only"]
    pooled_bc_1h = notch_results["pooled"]["batch_pos_cuts_1h_only"]
    pooled_ih = notch_results["pooled"]["individual_hikes_control"]
    pooled_ic = notch_results["pooled"]["individual_cuts_control"]

    _, p_batch_hike_vs_cut = stats.fisher_exact([
        [pooled_bh["n_premature"], pooled_bh["n_post_cooldown"]],
        [pooled_bc["n_premature"], pooled_bc["n_post_cooldown"]],
    ])
    _, p_batch_hike_vs_cut_1h = stats.fisher_exact([
        [pooled_bh_1h["n_premature"], pooled_bh_1h["n_post_cooldown"]],
        [pooled_bc_1h["n_premature"], pooled_bc_1h["n_post_cooldown"]],
    ])
    _, p_batch_vs_indiv_hikes = stats.fisher_exact([
        [pooled_bh["n_premature"], pooled_bh["n_post_cooldown"]],
        [pooled_ih["n_premature"], pooled_ih["n_post_cooldown"]],
    ])
    _, p_batch_vs_indiv_cuts = stats.fisher_exact([
        [pooled_bc["n_premature"], pooled_bc["n_post_cooldown"]],
        [pooled_ic["n_premature"], pooled_ic["n_post_cooldown"]],
    ])

    agency_audit = audit_dominated_premature_hikes(batch_moves, events)
    perm_decomp = decompose_by_manager_branch_permissions(batch_moves)

    # Verify exact revert-wall share of raw zero-debt [168h,169h) spike
    zd_all_168 = notch_results["pooled"]["batch_zero_debt_all_unfiltered"]["n_in_168_169"]
    zd_wall_168 = notch_results["pooled"]["batch_revert_wall_604800s_zero_debt"]["n_in_168_169"]

    out = {
        "module": "notch_and_agency",
        "primary_sample_definition": (
            "Primary notch-bunching sample restricts to batch managers with immutable on-chain "
            "minInterestRateChangePeriod < 604,800s (1h and 24h managers) who actually face the "
            "economic 168h cooldown fee notch, separating hardcoded 604,800s smart-contract revert walls."
        ),
        "revert_wall_decomposition_zero_debt_pooled": {
            "raw_zero_debt_n_in_168_169": zd_all_168,
            "hardcoded_604800s_wall_n_in_168_169": zd_wall_168,
            "revert_wall_share_of_zero_debt_spike_pct": round(100.0 * zd_wall_168 / max(zd_all_168, 1), 2),
            "remaining_1h_24h_keeper_bot_n_in_168_169": notch_results["pooled"]["batch_zero_debt_1h_24h"]["n_in_168_169"],
            "remaining_1h_only_n_in_168_169": notch_results["pooled"]["batch_zero_debt_1h_only"]["n_in_168_169"],
        },
        "counts_summary": {
            "genuine_batch_updates_pooled": len(batch_moves),
            "genuine_batch_updates_minp_lt_7d_pooled": sum(1 for r in batch_moves if r.get("min_period_s") is not None and int(r["min_period_s"]) < COOLDOWN_SECONDS),
            "genuine_batch_updates_revert_wall_7d_pooled": sum(1 for r in batch_moves if r.get("min_period_s") is not None and int(r["min_period_s"]) >= COOLDOWN_SECONDS),
            "genuine_individual_updates_pooled": len(indiv_moves),
        },
        "notch_bunching": notch_results,
        "asymmetry_tests_pooled": {
            "scope": "Primary economic-notch sample (minInterestRateChangePeriod < 604,800s)",
            "batch_hike_vs_cut_premature_diff_pp": round((pooled_bh["frac_premature"] - pooled_bc["frac_premature"]) * 100.0, 2),
            "batch_hike_vs_cut_fisher_p": float(p_batch_hike_vs_cut),
            "batch_hike_vs_cut_1h_only_diff_pp": round((pooled_bh_1h["frac_premature"] - pooled_bc_1h["frac_premature"]) * 100.0, 2),
            "batch_hike_vs_cut_1h_only_fisher_p": float(p_batch_hike_vs_cut_1h),
            "batch_vs_indiv_hike_premature_diff_pp": round((pooled_bh["frac_premature"] - pooled_ih["frac_premature"]) * 100.0, 2),
            "batch_vs_indiv_hike_fisher_p": float(p_batch_vs_indiv_hikes),
            "batch_vs_indiv_cut_premature_diff_pp": round((pooled_bc["frac_premature"] - pooled_ic["frac_premature"]) * 100.0, 2),
            "batch_vs_indiv_cut_fisher_p": float(p_batch_vs_indiv_cuts),
        },
        "dominated_region_agency_audit": agency_audit,
        "manager_branch_permission_decomposition": perm_decomp,
    }

    save_json(RES_DIR / "notch_and_agency.json", out)
    print(f"\n[DONE] Saved notch_and_agency.json")
    print(
        f"  Near-notch [164h,168h): {agency_audit['near_notch_164_168']['count']} hikes, "
        f"{agency_audit['near_notch_164_168']['total_fee_bold']:,.2f} BOLD "
        f"({agency_audit['near_notch_164_168']['zero_pre6h_redemptions_count']} with 0 PRE-6h redemptions, "
        f"{agency_audit['near_notch_164_168']['zero_both6h_redemptions_count']} with 0 +/-6h redemptions, "
        f"{agency_audit['near_notch_164_168']['n_ceiling_constrained']}/8 ceiling-constrained)"
    )
    print(
        f"  Manager fee-base expansion: +{agency_audit['total_manager_annual_fee_base_gain_hikes_only_bold_per_yr']:,.2f} BOLD/yr (hikes only) "
        f"| +{agency_audit['total_manager_annual_fee_base_gain_all_paid_bold_per_yr']:,.2f} BOLD/yr (all paid incl. cuts)"
    )


if __name__ == "__main__":
    main()
