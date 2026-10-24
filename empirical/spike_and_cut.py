"""Module 2: Mainnet Spike-and-Cut Forensics & Four-Mechanism Exact Design Comparison.

Scans ALL 1,712 canonical batch rate updates (and cross-checks all 822 individual
trove op=3 updates!) across Development (408d), Confirmation (77d), and Pooled (485d):
  1. Catalogs EVERY mainnet spike-and-cut episode (rate hike followed within < 168h
     by a downward reversal), including exact transaction-level forensics of the
     2026-03-06 wstETH (84.6% discount) and WETH (61.6% discount) mainnet episodes!
  2. Evaluates exact Solidity integer-wei upfront penalties / forfeitures across all
     1,712 batch updates under FOUR mechanisms (matching Theorems 2.1, 2.2, 2.4):
       - Status Quo (verbatim on-chain fee_wei)
       - Phase-17 Design A (increment fee on premature hikes, branch-avg on premature cuts)
       - Design A* (Symmetric-Commitment Increment Fee: increment on hikes, pro-rata
         remaining-cooldown increment on cuts; 0 extra EVM storage slots)
       - Design D (Rate-Bond Escrow: refundable vesting escrow on hikes, pro-rata
         forfeiture on premature cuts & closes; tracks exact net forfeited fees AND
         escrow capital lockup / opportunity cost!)
  3. Computes exact staircase-episode savings (all 172 maximal staircase episodes,
     decomposed by Dev vs. Conf) with 14-day circular block-bootstrap 95% CIs,
     denominated in BOTH total BOLD and BOLD per million managed debt-days!
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict
from datetime import datetime, timezone
from typing import Any, Dict, List, Sequence, Tuple

import numpy as np
import pandas as pd

from common import (
    BRANCHES,
    COOLDOWN_SECONDS,
    CONF_END_DATE,
    CONF_START_DATE,
    DEV_END_DATE,
    DEV_START_DATE,
    MIN_ANNUAL_INTEREST_RATE,
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

from offline_core import Replay  # type: ignore


def compute_exact_design_fees_batch(
    records: List[Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], Dict[str, Any]]:
    """Compute exact integer-wei fees on every batch update across Status Quo, Design A,
    Design A*, and Hardened 1-Slot Design D (Theorem 2.4 Eqs. 2.10a-b), and
    catalog every spike-and-cut episode.

    Hardened Design D (accrued-interest-safe 1-slot state machine, zero underflows):
      State per (branch, manager): (unvestedBond, lastUpdateTime, vestEndTime)
      - (D-Settle): Exact linear vesting over [t_last, min(t, t_end)] + exact continuous-time
        integrated escrow lockup (BOLD-days) over [t_last, min(t, t_end)].
      - (D-Increase): On ANY rate hike (premature OR post-cooldown), settle first, reset
        t_end = t + P, and top up bond to B_target = D*(r_new - r_min)*P/Y.
      - (D-Decrease): On premature pure rate cut (t < t_end, r_new < r_old), settle first,
        forfeit exact scale-invariant Eq. (2.10b) ratio
            Forfeit = B_rem * (r_old - r_new) / (r_old - r_min) in [0, B_rem],
        keeping t_end UNCHANGED (zero underflow even under accrued-interest debt growth!).
    """
    by_bm: Dict[Tuple[str, str], List[Dict[str, Any]]] = defaultdict(list)
    for r in records:
        by_bm[(r["branch"], str(r["manager"]).lower())].append(r)

    enriched: List[Dict[str, Any]] = []
    spike_cuts: List[Dict[str, Any]] = []
    dd_lockup_by_samp: Dict[str, float] = defaultdict(float)
    dd_underflow_count = 0
    dd_r1_underflow_diagnostic = 0

    for (branch, mgr), seq in by_bm.items():
        seq.sort(key=lambda x: (int(x["block"]), int(x["index"])))
        prev_changed: Dict[str, Any] | None = None

        # Hardened 1-slot Design D state: (bond_wei, t_last, t_end, bonded_debt_wei)
        d_bond_wei = 0
        d_t_last = 0
        d_t_end = 0
        d_bonded_wei = 0

        # Diagnostic tracker for naive highWaterRate underflows
        r1_bond = 0
        r1_hw = MIN_ANNUAL_INTEREST_RATE
        r1_last = 0

        for r in seq:
            ts = int(r["timestamp"])
            old_r = int(r["old_rate"])
            new_r = int(r["new_rate"])
            elap = int(r["elapsed"])
            basis = int(r["basis_wei"])
            sq_fee = int(r["fee_wei"])
            changed = bool(r["changed"])
            premature = elap < COOLDOWN_SECONDS
            direction = "hike" if new_r > old_r else ("cut" if new_r < old_r else "noop")
            samp = sample_label(ts)

            # 1. Phase-17 Design A
            if not changed or not premature or basis == 0:
                da_fee = 0
            elif direction == "hike":
                da_fee = calc_interest_wei(basis, new_r - old_r, COOLDOWN_SECONDS)
            else:
                da_fee = sq_fee  # Phase-17 Design A left premature cuts at branch average

            # 2. Design A* (Symmetric-Commitment Increment Fee, Theorem 2.2)
            if not changed or not premature or basis == 0:
                dastar_fee = 0
            elif direction == "hike":
                dastar_fee = calc_interest_wei(basis, new_r - old_r, COOLDOWN_SECONDS)
            else:
                rem_s = max(0, COOLDOWN_SECONDS - elap)
                dastar_fee = calc_interest_wei(basis, old_r - new_r, rem_s)

            # Diagnostic: verify naive highWaterRate underflow count
            dt1 = ts - r1_last if r1_last > 0 else COOLDOWN_SECONDS
            if dt1 >= COOLDOWN_SECONDS:
                r1_bond = 0
                r1_hw = MIN_ANNUAL_INTEREST_RATE
            elif r1_bond > 0:
                r1_bond = (r1_bond * (COOLDOWN_SECONDS - dt1)) // COOLDOWN_SECONDS
            if changed and basis > 0:
                if direction == "hike":
                    if not premature:
                        r1_bond = calc_interest_wei(basis, max(0, new_r - MIN_ANNUAL_INTEREST_RATE), COOLDOWN_SECONDS)
                        r1_hw = max(new_r, MIN_ANNUAL_INTEREST_RATE)
                        r1_last = ts
                    else:
                        if new_r > r1_hw:
                            r1_bond += calc_interest_wei(basis, new_r - r1_hw, COOLDOWN_SECONDS)
                            r1_hw = new_r
                        r1_last = ts
                elif direction == "cut":
                    if premature:
                        f1 = calc_interest_wei(basis, old_r - new_r, max(0, COOLDOWN_SECONDS - elap))
                        if f1 > r1_bond:
                            dd_r1_underflow_diagnostic += 1
                        r1_bond = max(0, r1_bond - f1)
                        r1_last = ts
                    else:
                        r1_bond = 0
                        r1_hw = max(new_r, MIN_ANNUAL_INTEREST_RATE)
                        r1_last = ts

            # 3. Hardened 1-Slot Design D (Theorem 2.4 Eqs. 2.10a-b)
            # (D-Settle): linear vesting over [d_t_last, min(ts, d_t_end)] + exact lockup integral
            if d_bond_wei > 0 and d_t_end > d_t_last:
                t_eff = min(ts, d_t_end)
                dt_lock = max(0, t_eff - d_t_last)
                if ts >= d_t_end:
                    bond_after_settle = 0
                else:
                    vested = (d_bond_wei * (ts - d_t_last)) // (d_t_end - d_t_last)
                    bond_after_settle = d_bond_wei - vested
                avg_b_bold = 0.5 * (d_bond_wei + bond_after_settle) / 1e18
                lock_bd = avg_b_bold * (dt_lock / 86400.0)
                # Attribute lockup to the interval's active sample (using d_t_last if before split, else samp)
                sk_int = sample_label(d_t_last) if d_t_last > 0 else samp
                dd_lockup_by_samp[sk_int] += lock_bd
                dd_lockup_by_samp["pooled"] += lock_bd
                d_bond_wei = bond_after_settle
                if ts >= d_t_end:
                    d_t_last = d_t_end = ts
                else:
                    d_t_last = ts

            dd_forfeit_wei = 0
            dd_deposit_wei = 0
            dd_target_wei = 0
            d_bonded_pre_cut = d_bonded_wei
            if changed and basis > 0:
                if direction == "hike":
                    # (D-Increase): ALWAYS reset t_end = ts + P and top up to B_target = D*(new_r - r_min)*P/Y
                    dd_target_wei = calc_interest_wei(basis, max(0, new_r - MIN_ANNUAL_INTEREST_RATE), COOLDOWN_SECONDS)
                    dd_deposit_wei = max(0, dd_target_wei - d_bond_wei)
                    d_bond_wei = max(d_bond_wei, dd_target_wei)
                    d_bonded_wei = basis
                    d_t_last = ts
                    d_t_end = ts + COOLDOWN_SECONDS
                elif direction == "cut":
                    # If first-ever BatchUpdated is a premature cut (opened < P ago with no prior hike),
                    # Theorem 2.4's openTrove/join (D-Increase) had bonded B_init at ts_open = ts - elap.
                    if d_bond_wei == 0 and d_t_end == 0 and premature and old_r > MIN_ANNUAL_INTEREST_RATE:
                        ts_open = ts - elap
                        b_init = calc_interest_wei(basis, old_r - MIN_ANNUAL_INTEREST_RATE, COOLDOWN_SECONDS)
                        rem_init = max(0, COOLDOWN_SECONDS - elap)
                        d_bond_wei = (b_init * rem_init) // COOLDOWN_SECONDS
                        d_bonded_wei = basis
                        d_bonded_pre_cut = basis
                        # Lockup already incurred over [ts_open, ts]
                        lock_init_bd = 0.5 * ((b_init + d_bond_wei) / 1e18) * (elap / 86400.0)
                        dd_lockup_by_samp[sample_label(ts_open)] += lock_init_bd
                        dd_lockup_by_samp["pooled"] += lock_init_bd
                        d_t_last = ts
                        d_t_end = ts_open + COOLDOWN_SECONDS

                    if ts < d_t_end and d_bond_wei > 0 and old_r > MIN_ANNUAL_INTEREST_RATE:
                        # (D-Decrease) Eq. (2.10b): accrued-interest-safe scale-invariant pure-cut forfeiture
                        dd_forfeit_wei = (d_bond_wei * (old_r - new_r)) // (old_r - MIN_ANNUAL_INTEREST_RATE)
                        if dd_forfeit_wei > d_bond_wei:
                            dd_underflow_count += 1
                            dd_forfeit_wei = d_bond_wei
                        d_bond_wei -= dd_forfeit_wei
                        d_t_last = ts
                        # d_t_end stays UNCHANGED!
                    else:
                        d_bond_wei = 0
                        d_bonded_wei = 0
                        d_t_last = d_t_end = ts

            rec = {
                "branch": branch,
                "manager": mgr,
                "manager_label": manager_label(mgr),
                "timestamp": ts,
                "date": ts_to_date(ts),
                "sample": samp,
                "block": int(r["block"]),
                "index": int(r["index"]),
                "tx": r["tx"],
                "changed": changed,
                "direction": direction,
                "premature": premature,
                "elapsed_s": elap,
                "elapsed_h": elap / 3600.0,
                "old_rate": old_r,
                "new_rate": new_r,
                "delta_bps": (new_r - old_r) / 1e14,
                "basis_wei": basis,
                "debt_bold": basis / 1e18,
                "category": r["category"],
                "sq_fee_wei": sq_fee,
                "da_fee_wei": da_fee,
                "dastar_fee_wei": dastar_fee,
                "dd_forfeit_wei": dd_forfeit_wei,
                "dd_deposit_wei": dd_deposit_wei,
                "dd_target_wei": dd_target_wei,
                "sq_fee_bold": sq_fee / 1e18,
                "da_fee_bold": da_fee / 1e18,
                "dastar_fee_bold": dastar_fee / 1e18,
                "dd_forfeit_bold": dd_forfeit_wei / 1e18,
                "dd_deposit_bold": dd_deposit_wei / 1e18,
                "dd_target_bold": dd_target_wei / 1e18,
                "is_staircase_hike": r["category"] == "staircase_paid_hike",
            }
            enriched.append(rec)

            # Detect EVERY spike-and-cut episode: prior changed update was a hike (r_base -> r_hi),
            # followed within < 168h by a cut (r_hi -> r_lo) with positive debt
            if changed and direction == "cut" and premature and basis > 0 and prev_changed is not None and prev_changed["direction"] == "hike":
                r_hi = old_r
                r_lo = new_r
                r_base = prev_changed["old_rate"]
                dt_hold = elap
                rem_s = COOLDOWN_SECONDS - dt_hold
                hold_excess_wei = calc_interest_wei(basis, r_hi - r_lo, COOLDOWN_SECONDS)
                spike_excess_interest_wei = calc_interest_wei(basis, r_hi - r_lo, dt_hold)
                rem_hold_excess_wei = calc_interest_wei(basis, r_hi - r_lo, rem_s)

                hike_sq_wei = prev_changed["sq_fee_wei"]
                hike_da_wei = prev_changed["da_fee_wei"]
                hike_dastar_wei = prev_changed["dastar_fee_wei"]

                sq_total_excess = hike_sq_wei + spike_excess_interest_wei + sq_fee
                da_total_excess = hike_da_wei + spike_excess_interest_wei + da_fee
                dastar_total_excess = hike_dastar_wei + spike_excess_interest_wei + dastar_fee
                # Design D security compares strictly on bonded principal D_bonded (Theorem 2.4 Eq. 2.10c)
                dd_hold_bonded_wei = calc_interest_wei(d_bonded_pre_cut if d_bonded_pre_cut > 0 else basis, r_hi - r_lo, COOLDOWN_SECONDS)
                dd_spike_bonded_wei = calc_interest_wei(d_bonded_pre_cut if d_bonded_pre_cut > 0 else basis, r_hi - r_lo, dt_hold)
                dd_total_excess = dd_spike_bonded_wei + dd_forfeit_wei

                # Canonical total-excess discount (1 - total_excess / hold_7d_excess)
                sq_discount = 1.0 - (sq_total_excess / hold_excess_wei) if hold_excess_wei > 0 else 0.0
                da_discount = 1.0 - (da_total_excess / hold_excess_wei) if hold_excess_wei > 0 else 0.0
                dastar_discount = 1.0 - (dastar_total_excess / hold_excess_wei) if hold_excess_wei > 0 else 0.0
                dd_discount = 1.0 - (dd_total_excess / dd_hold_bonded_wei) if dd_hold_bonded_wei > 0 else 0.0

                # Explicitly documented alternative discount conventions
                sq_cut_fee_vs_rem_disc = 1.0 - (sq_fee / rem_hold_excess_wei) if rem_hold_excess_wei > 0 else 0.0
                sq_cut_fee_vs_7d_disc = 1.0 - (sq_fee / hold_excess_wei) if hold_excess_wei > 0 else 0.0
                sq_net_saving_bold = (hold_excess_wei - sq_total_excess) / 1e18

                spike_cuts.append({
                    "branch": branch,
                    "manager_label": manager_label(mgr),
                    "manager": mgr,
                    "sample": samp,
                    "hike_utc": datetime.fromtimestamp(prev_changed["timestamp"], tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
                    "cut_utc": datetime.fromtimestamp(ts, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
                    "hike_tx": prev_changed["tx"],
                    "cut_tx": r["tx"],
                    "hike_was_free": prev_changed["sq_fee_wei"] == 0,
                    "elapsed_s": dt_hold,
                    "elapsed_h": round(dt_hold / 3600.0, 4),
                    "debt_bold": round(basis / 1e18, 2),
                    "r_base_pct": round(r_base / 1e16, 4),
                    "r_hi_pct": round(r_hi / 1e16, 4),
                    "r_lo_pct": round(r_lo / 1e16, 4),
                    "spike_bps": round((r_hi - r_base) / 1e14, 2),
                    "cut_bps": round((r_hi - r_lo) / 1e14, 2),
                    "hold_7d_excess_bold": round(hold_excess_wei / 1e18, 2),
                    "spike_window_excess_interest_bold": round(spike_excess_interest_wei / 1e18, 2),
                    "sq_hike_fee_bold": round(hike_sq_wei / 1e18, 2),
                    "sq_cut_fee_bold": round(sq_fee / 1e18, 2),
                    "sq_total_excess_bold": round(sq_total_excess / 1e18, 2),
                    "sq_saving_vs_7d_hold_bold": round(sq_net_saving_bold, 2),
                    "sq_discount_pct": round(sq_discount * 100.0, 2),
                    "sq_discount_total_excess_pct": round(sq_discount * 100.0, 2),
                    "sq_discount_cut_fee_vs_rem_pct": round(sq_cut_fee_vs_rem_disc * 100.0, 2),
                    "sq_discount_cut_fee_vs_7d_pct": round(sq_cut_fee_vs_7d_disc * 100.0, 2),
                    "design_a_cut_fee_bold": round(da_fee / 1e18, 2),
                    "design_a_discount_pct": round(da_discount * 100.0, 2),
                    "design_astar_cut_fee_bold": round(dastar_fee / 1e18, 2),
                    "design_astar_total_excess_bold": round(dastar_total_excess / 1e18, 2),
                    "design_astar_discount_pct": round(dastar_discount * 100.0, 4),
                    "design_d_forfeit_bold": round(dd_forfeit_wei / 1e18, 2),
                    "design_d_total_excess_bold": round(dd_total_excess / 1e18, 2),
                    "design_d_discount_pct": round(dd_discount * 100.0, 4),
                    "profitable_exploit_sq": bool(sq_discount > 0),
                    "profitable_exploit_design_a": bool(da_discount > 0),
                    "profitable_exploit_design_astar": bool(dastar_discount > 1e-6),
                    "profitable_exploit_design_d": bool(dd_discount > 1e-6),
                })

            if changed:
                prev_changed = rec

        # Flush final unvested tail lockup to d_t_end
        if d_bond_wei > 0 and d_t_end > d_t_last:
            dt_tail = d_t_end - d_t_last
            lock_tail_bd = 0.5 * (d_bond_wei / 1e18) * (dt_tail / 86400.0)
            sk_end = sample_label(d_t_last)
            dd_lockup_by_samp[sk_end] += lock_tail_bd
            dd_lockup_by_samp["pooled"] += lock_tail_bd

    assert dd_underflow_count == 0, f"Hardened Design D suffered {dd_underflow_count} underflows!"
    spike_cuts.sort(key=lambda x: -x["sq_saving_vs_7d_hold_bold"])
    dd_meta = {
        "hardened_design_d_underflows": dd_underflow_count,
        "legacy_highwater_underflows_on_mainnet": dd_r1_underflow_diagnostic,
        "exact_lockup_bold_days_by_sample": {
            s: round(dd_lockup_by_samp.get(s, 0.0), 4) for s in ("development", "confirmation", "pooled")
        },
    }
    return enriched, spike_cuts, dd_meta


def scan_individual_spike_and_cuts() -> List[Dict[str, Any]]:
    """Also scan all 822 individual trove op=3 rate updates for any spike-and-cut episodes."""
    events = load_canonical_events("pooled")
    out: List[Dict[str, Any]] = []
    for b in BRANCHES:
        rep = Replay()
        for e in events[b]:
            rep.apply(e)
        by_trove: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        for mv in rep.rate_moves:
            if mv["kind"] == "individual" and int(mv["old_rate"]) != int(mv["new_rate"]):
                by_trove[str(mv["controller"])].append(mv)
        for tid, seq in by_trove.items():
            prev = None
            for mv in seq:
                old_r, new_r = int(mv["old_rate"]), int(mv["new_rate"])
                elap = int(mv["elapsed"])
                basis = int(mv["debt_wei"]) - int(mv["upfront_fee_wei"])
                if prev is not None and int(prev["new_rate"]) > int(prev["old_rate"]) and new_r < old_r and elap < COOLDOWN_SECONDS and basis > 0:
                    hold_excess = calc_interest_wei(basis, old_r - new_r, COOLDOWN_SECONDS)
                    spike_int = calc_interest_wei(basis, old_r - new_r, elap)
                    sq_tot = int(prev["upfront_fee_wei"]) + spike_int + int(mv["upfront_fee_wei"])
                    disc = 1.0 - sq_tot / hold_excess if hold_excess > 0 else 0.0
                    dastar_cut = calc_interest_wei(basis, old_r - new_r, COOLDOWN_SECONDS - elap)
                    out.append({
                        "branch": b,
                        "trove": tid,
                        "sample": sample_label(int(mv["timestamp"])),
                        "hike_utc": datetime.fromtimestamp(int(prev["timestamp"]), tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
                        "cut_utc": datetime.fromtimestamp(int(mv["timestamp"]), tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
                        "hike_tx": prev["tx"],
                        "cut_tx": mv["tx"],
                        "elapsed_h": round(elap / 3600.0, 4),
                        "debt_bold": round(basis / 1e18, 2),
                        "r_base_pct": round(int(prev["old_rate"]) / 1e16, 4),
                        "r_hi_pct": round(old_r / 1e16, 4),
                        "r_lo_pct": round(new_r / 1e16, 4),
                        "sq_cut_fee_bold": round(int(mv["upfront_fee_wei"]) / 1e18, 2),
                        "design_astar_cut_fee_bold": round(dastar_cut / 1e18, 2),
                        "hold_7d_excess_bold": round(hold_excess / 1e18, 2),
                        "sq_discount_pct": round(disc * 100.0, 2),
                        "profitable_exploit_sq": bool(disc > 0),
                    })
                prev = mv
    out.sort(key=lambda x: -x["sq_discount_pct"])
    return out


def summarize_mechanisms(
    enriched: List[Dict[str, Any]],
    managed_debt_days_by_date: Dict[str, float],
    sample: str,
    dates: Sequence[str],
    dd_exact_lockup_bold_days: float,
) -> Dict[str, Any]:
    """Compute exact aggregate fees, per-million-debt-day rates, savings vs. Status Quo,
    and 14d circular block-bootstrap 95% CIs across Dev, Conf, or Pooled."""
    sub = [r for r in enriched if sample == "pooled" or r["sample"] == sample]
    total_m_dd = sum(managed_debt_days_by_date.get(d, 0.0) for d in dates) / 1e6

    # Group daily sums for fast block bootstrap
    day_sq: Dict[str, float] = defaultdict(float)
    day_da: Dict[str, float] = defaultdict(float)
    day_dastar: Dict[str, float] = defaultdict(float)
    day_dd: Dict[str, float] = defaultdict(float)
    day_dd_dep: Dict[str, float] = defaultdict(float)
    day_stair_sq: Dict[str, float] = defaultdict(float)
    day_stair_dastar: Dict[str, float] = defaultdict(float)

    for r in sub:
        d = r["date"]
        day_sq[d] += r["sq_fee_bold"]
        day_da[d] += r["da_fee_bold"]
        day_dastar[d] += r["dastar_fee_bold"]
        day_dd[d] += r["dd_forfeit_bold"]
        day_dd_dep[d] += r["dd_deposit_bold"]
        if r["is_staircase_hike"]:
            day_stair_sq[d] += r["sq_fee_bold"]
            day_stair_dastar[d] += r["dastar_fee_bold"]

    def rate_per_mdd(day_map: Dict[str, float], dlist: Sequence[str]) -> float:
        num = sum(day_map.get(d, 0.0) for d in dlist)
        den = sum(managed_debt_days_by_date.get(d, 0.0) for d in dlist) / 1e6
        return num / den if den > 0 else float("nan")

    def saving_per_mdd(day_map: Dict[str, float], dlist: Sequence[str]) -> float:
        num = sum(day_sq.get(d, 0.0) - day_map.get(d, 0.0) for d in dlist)
        den = sum(managed_debt_days_by_date.get(d, 0.0) for d in dlist) / 1e6
        return num / den if den > 0 else float("nan")

    sq_tot = sum(r["sq_fee_bold"] for r in sub)
    da_tot = sum(r["da_fee_bold"] for r in sub)
    dastar_tot = sum(r["dastar_fee_bold"] for r in sub)
    dd_forf_tot = sum(r["dd_forfeit_bold"] for r in sub)
    dd_dep_tot = sum(r["dd_deposit_bold"] for r in sub)
    dd_target_tot = sum(r["dd_target_bold"] for r in sub)

    # Exact continuous-time integrated escrow lockup opportunity cost at 5% APR (Hardened Design D!)
    dd_lockup_bold_days = float(dd_exact_lockup_bold_days)
    dd_opp_cost_5pct_bold = dd_lockup_bold_days * (0.05 / 365.0)

    stair_sq = sum(r["sq_fee_bold"] for r in sub if r["is_staircase_hike"])
    stair_dastar = sum(r["dastar_fee_bold"] for r in sub if r["is_staircase_hike"])
    prem_cut_sq = sum(r["sq_fee_bold"] for r in sub if r["direction"] == "cut" and r["premature"])
    prem_cut_dastar = sum(r["dastar_fee_bold"] for r in sub if r["direction"] == "cut" and r["premature"])
    prem_hike_sq = sum(r["sq_fee_bold"] for r in sub if r["direction"] == "hike" and r["premature"])
    prem_hike_dastar = sum(r["dastar_fee_bold"] for r in sub if r["direction"] == "hike" and r["premature"])

    return {
        "n_records": len(sub),
        "n_genuine_changed": sum(1 for r in sub if r["changed"]),
        "n_paid_sq": sum(1 for r in sub if r["sq_fee_wei"] > 0),
        "n_staircase_hikes": sum(1 for r in sub if r["is_staircase_hike"]),
        "managed_million_debt_days_panel_proxy": round(total_m_dd, 4),
        "total_fees_bold": {
            "status_quo": round(sq_tot, 2),
            "design_a_baseline": round(da_tot, 2),
            "design_a_star": round(dastar_tot, 2),
            "design_d_forfeited": round(dd_forf_tot, 2),
            "design_d_escrow_net_topups_refundable": round(dd_dep_tot, 2),
            "design_d_escrow_gross_target_locked_refundable": round(dd_target_tot, 2),
            "design_d_lockup_bold_days_exact": round(dd_lockup_bold_days, 2),
            "design_d_avg_escrow_locked_bold": round(dd_lockup_bold_days / max(1, len(dates)), 2),
            "design_d_opp_cost_at_5pct_bold": round(dd_opp_cost_5pct_bold, 2),
            "design_d_allin_forfeit_plus_5pct_opp_bold": round(dd_forf_tot + dd_opp_cost_5pct_bold, 2),
        },
        "savings_vs_sq_bold": {
            "design_a_baseline": round(sq_tot - da_tot, 2),
            "design_a_star": round(sq_tot - dastar_tot, 2),
            "design_d_net_forfeit": round(sq_tot - dd_forf_tot, 2),
            "design_d_net_after_5pct_opp": round(sq_tot - dd_forf_tot - dd_opp_cost_5pct_bold, 2),
            "design_a_star_pct_reduction": round((sq_tot - dastar_tot) / sq_tot * 100.0, 2) if sq_tot > 0 else 0.0,
            "design_d_pct_reduction_after_opp": round((sq_tot - dd_forf_tot - dd_opp_cost_5pct_bold) / sq_tot * 100.0, 2) if sq_tot > 0 else 0.0,
        },
        "decomposition_bold": {
            "staircase_hikes_sq": round(stair_sq, 2),
            "staircase_hikes_share_of_sq_pct": round(stair_sq / sq_tot * 100.0, 2) if sq_tot > 0 else 0.0,
            "staircase_hikes_design_a_star": round(stair_dastar, 2),
            "staircase_savings_design_a_star": round(stair_sq - stair_dastar, 2),
            "all_premature_hikes_sq": round(prem_hike_sq, 2),
            "all_premature_hikes_design_a_star": round(prem_hike_dastar, 2),
            "all_premature_cuts_sq": round(prem_cut_sq, 2),
            "all_premature_cuts_design_a_star": round(prem_cut_dastar, 2),
            "cut_commitment_clawback_astar_minus_a_bold": round(prem_cut_dastar - prem_cut_sq, 2),
        },
        "per_million_debt_days_boot14d": {
            "status_quo": circular_block_bootstrap(dates, lambda dl: rate_per_mdd(day_sq, dl), block_len=14, n_boot=999, seed=20261201),
            "design_a_baseline": circular_block_bootstrap(dates, lambda dl: rate_per_mdd(day_da, dl), block_len=14, n_boot=999, seed=20261202),
            "design_a_star": circular_block_bootstrap(dates, lambda dl: rate_per_mdd(day_dastar, dl), block_len=14, n_boot=999, seed=20261203),
            "design_d_forfeited": circular_block_bootstrap(dates, lambda dl: rate_per_mdd(day_dd, dl), block_len=14, n_boot=999, seed=20261204),
            "saving_design_a_vs_sq": circular_block_bootstrap(dates, lambda dl: saving_per_mdd(day_da, dl), block_len=14, n_boot=999, seed=20261205),
            "saving_design_a_star_vs_sq": circular_block_bootstrap(dates, lambda dl: saving_per_mdd(day_dastar, dl), block_len=14, n_boot=999, seed=20261206),
            "saving_design_d_vs_sq": circular_block_bootstrap(dates, lambda dl: saving_per_mdd(day_dd, dl), block_len=14, n_boot=999, seed=20261207),
        },
    }


def scan_batch_join_switch_spike_bypass() -> Dict[str, Any]:
    """Batch transition audit: Scan ALL TroveOperation op in {7, 8, 9}
    (setInterestBatchManager, removeFromBatch, switchBatchManager) across all 485d using
    the TRUE pre-operation snapshot `rep.pending[tid]` (saved before TroveUpdated/BatchedTroveUpdated
    mutates `rep.troves[tid]`) AND tracking `BatchUpdated` manager hikes!"""
    events = load_canonical_events("pooled")
    indiv_hike_episodes: List[Dict[str, Any]] = []
    batch_hike_episodes: List[Dict[str, Any]] = []
    n_op7 = n_op8 = n_op9 = 0
    n_any_rate_drop_789 = 0

    for b in BRANCHES:
        rep = Replay()
        last_indiv_hike: Dict[Any, Tuple[int, int, int, str, int]] = {}  # tid -> (ts, old_r, new_r, tx, op)
        last_batch_hike: Dict[str, Tuple[int, int, int, str]] = {}       # mgr -> (ts, old_r, new_r, tx)

        for e in events[b]:
            nm = e["name"]
            if nm == "BatchUpdated":
                mgr = str(e["fields"]["interestBatchManager"]).lower()
                old_b = rep.batches.get(mgr)
                rep.apply(e)
                new_b = rep.batches.get(mgr)
                if int(e["fields"]["operation"]) == 2 and old_b and new_b and new_b["rate"] > old_b["rate"]:
                    last_batch_hike[mgr] = (int(e["timestamp"]), int(old_b["rate"]), int(new_b["rate"]), e["tx"])
            elif nm == "TroveOperation":
                op = int(e["fields"]["operation"])
                tid = e["fields"]["troveId"]
                ts = int(e["timestamp"])
                if op == 7:
                    n_op7 += 1
                elif op == 8:
                    n_op8 += 1
                elif op == 9:
                    n_op9 += 1

                # TRUE pre-operation snapshot is in rep.pending[tid]!
                old_t = rep.pending.get(tid)
                if old_t is not None:
                    pre_rate = int(rep.latest(old_t, ts)[6])
                    pre_debt = int(rep.latest(old_t, ts)[0])
                    pre_mgr = str(old_t["manager"]).lower()
                else:
                    pre_rate = pre_debt = 0
                    pre_mgr = "0x" + "0" * 40

                rep.apply(e)
                post_t = rep.troves.get(tid)
                post_rate = int(rep.latest(post_t, ts)[6]) if post_t else 0
                post_debt = int(rep.latest(post_t, ts)[0]) if post_t else 0

                if op == 3 and post_rate > pre_rate and pre_debt > 0:
                    last_indiv_hike[tid] = (ts, pre_rate, post_rate, e["tx"], op)
                elif op == 0 and post_rate > MIN_ANNUAL_INTEREST_RATE and post_debt > 0:
                    last_indiv_hike[tid] = (ts, MIN_ANNUAL_INTEREST_RATE, post_rate, e["tx"], op)

                if op in (7, 8, 9) and pre_debt > 0 and post_rate < pre_rate:
                    n_any_rate_drop_789 += 1
                    fee_wei = int(e["fields"]["debtIncreaseFromUpfrontFee"])

                    # Case A: Preceded within <168h by individual hike (op=3) or high-rate open (op=0)
                    if tid in last_indiv_hike:
                        hts, h_old, h_hi, htx, hop = last_indiv_hike[tid]
                        dt = ts - hts
                        if 0 <= dt < COOLDOWN_SECONDS:
                            hold_exc = calc_interest_wei(pre_debt, h_hi - post_rate, COOLDOWN_SECONDS)
                            spike_int = calc_interest_wei(pre_debt, h_hi - post_rate, dt)
                            disc = 1.0 - (spike_int + fee_wei) / hold_exc if hold_exc > 0 else 0.0
                            indiv_hike_episodes.append({
                                "pathway": "indiv_op3_then_789" if hop == 3 else "indiv_op0_open_then_789",
                                "prior_op": hop,
                                "branch": b,
                                "trove": str(tid),
                                "op": op,
                                "sample": sample_label(ts),
                                "date": ts_to_date(ts),
                                "hike_tx": htx,
                                "bypass_tx": e["tx"],
                                "elapsed_h": round(dt / 3600.0, 4),
                                "debt_bold": round(pre_debt / 1e18, 2),
                                "r_hi_pct": round(h_hi / 1e16, 4),
                                "r_post_pct": round(post_rate / 1e16, 4),
                                "fee_paid_bold": round(fee_wei / 1e18, 2),
                                "hold_7d_excess_bold": round(hold_exc / 1e18, 2),
                                "sq_discount_pct": round(disc * 100.0, 2),
                                "profitable_bypass": bool(disc > 0),
                            })

                    # Case B: Batched trove exited/switched (op=8/9) to lower rate within <168h of manager hike
                    if pre_mgr in last_batch_hike:
                        hts, h_old, h_hi, htx = last_batch_hike[pre_mgr]
                        dt = ts - hts
                        if 0 <= dt < COOLDOWN_SECONDS:
                            hold_exc = calc_interest_wei(pre_debt, pre_rate - post_rate, COOLDOWN_SECONDS)
                            spike_int = calc_interest_wei(pre_debt, pre_rate - post_rate, dt)
                            disc = 1.0 - (spike_int + fee_wei) / hold_exc if hold_exc > 0 else 0.0
                            batch_hike_episodes.append({
                                "pathway": "batch_hike_then_exit_or_switch_89",
                                "branch": b,
                                "manager_label": manager_label(pre_mgr),
                                "trove": str(tid),
                                "op": op,
                                "sample": sample_label(ts),
                                "date": ts_to_date(ts),
                                "hike_tx": htx,
                                "bypass_tx": e["tx"],
                                "elapsed_h": round(dt / 3600.0, 4),
                                "debt_bold": round(pre_debt / 1e18, 2),
                                "r_hi_pct": round(pre_rate / 1e16, 4),
                                "r_post_pct": round(post_rate / 1e16, 4),
                                "fee_paid_bold": round(fee_wei / 1e18, 2),
                                "hold_7d_excess_bold": round(hold_exc / 1e18, 2),
                                "sq_discount_pct": round(disc * 100.0, 2),
                                "profitable_bypass": bool(disc > 0),
                            })
            else:
                rep.apply(e)

    all_episodes = sorted(indiv_hike_episodes + batch_hike_episodes, key=lambda x: -x["sq_discount_pct"])
    return {
        "n_batch_joins_op7": n_op7,
        "n_batch_removals_op8": n_op8,
        "n_batch_switches_op9": n_op9,
        "n_total_rate_lowering_op789": n_any_rate_drop_789,
        "n_spike_then_join_or_switch_within_7d": len(all_episodes),
        "n_after_indiv_op3_hike": sum(1 for x in indiv_hike_episodes if x["prior_op"] == 3),
        "n_after_indiv_op0_open": sum(1 for x in indiv_hike_episodes if x["prior_op"] == 0),
        "n_after_batch_manager_hike": len(batch_hike_episodes),
        "n_profitable_bypasses_observed": sum(1 for x in all_episodes if x["profitable_bypass"]),
        "max_observed_sq_discount_pct": all_episodes[0]["sq_discount_pct"] if all_episodes else None,
        "episodes": all_episodes,
    }


def main() -> None:
    print("=== Module 2: Mainnet Spike-and-Cut Forensics & Four-Mechanism Comparison ===")
    batch_ledger = load_batch_rate_ledger()
    records = batch_ledger["records"]
    enriched, batch_spike_cuts, dd_meta = compute_exact_design_fees_batch(records)
    indiv_spike_cuts = scan_individual_spike_and_cuts()
    join_switch_scan = scan_batch_join_switch_spike_bypass()

    # Load daily managed debt-days from canonical panels for exact BOLD/M debt-days denominator
    panel = load_daily_panels("pooled")
    managed_by_date = panel[panel["delegated"] == 1].groupby("date")["debt_bold"].sum().to_dict()

    dev_dates = pd.date_range(DEV_START_DATE, DEV_END_DATE, freq="D").strftime("%Y-%m-%d").tolist()
    conf_dates = pd.date_range(CONF_START_DATE, CONF_END_DATE, freq="D").strftime("%Y-%m-%d").tolist()
    pooled_dates = dev_dates + conf_dates

    mech_comparison = {
        "development": summarize_mechanisms(enriched, managed_by_date, "development", dev_dates, dd_meta["exact_lockup_bold_days_by_sample"]["development"]),
        "confirmation": summarize_mechanisms(enriched, managed_by_date, "confirmation", conf_dates, dd_meta["exact_lockup_bold_days_by_sample"]["confirmation"]),
        "pooled": summarize_mechanisms(enriched, managed_by_date, "pooled", pooled_dates, dd_meta["exact_lockup_bold_days_by_sample"]["pooled"]),
    }

    # Exact median staircase step & overcharge ratio (matching Theorem 2.1)
    stair_steps = [r for r in enriched if r["is_staircase_hike"] and r["sq_fee_wei"] > 0 and r["dastar_fee_wei"] > 0]
    step_bps = np.array([r["delta_bps"] for r in stair_steps], dtype=float)
    step_elap_h = np.array([r["elapsed_h"] for r in stair_steps], dtype=float)
    overcharge = np.array([r["sq_fee_wei"] / r["dastar_fee_wei"] for r in stair_steps], dtype=float)
    stair_micro = {
        "n_staircase_paid_hikes_pooled": len(stair_steps),
        "median_step_bps": float(np.median(step_bps)),
        "iqr_step_bps": [float(np.percentile(step_bps, 25)), float(np.percentile(step_bps, 75))],
        "mean_step_bps": float(np.mean(step_bps)),
        "median_elapsed_h": float(np.median(step_elap_h)),
        "iqr_elapsed_h": [float(np.percentile(step_elap_h, 25)), float(np.percentile(step_elap_h, 75))],
        "median_sq_to_dastar_overcharge_ratio": float(np.median(overcharge)),
        "mean_sq_to_dastar_overcharge_ratio": float(np.mean(overcharge)),
        "dollar_weighted_sq_to_dastar_ratio": float(sum(r["sq_fee_wei"] for r in stair_steps) / sum(r["dastar_fee_wei"] for r in stair_steps)),
    }

    out = {
        "module": "spike_and_cut",
        "design_d_audit_integrity": dd_meta,
        "batch_spike_and_cut_episodes": {
            "count": len(batch_spike_cuts),
            "n_profitable_under_sq": sum(1 for x in batch_spike_cuts if x["profitable_exploit_sq"]),
            "n_profitable_under_design_a": sum(1 for x in batch_spike_cuts if x["profitable_exploit_design_a"]),
            "n_profitable_under_design_a_star": sum(1 for x in batch_spike_cuts if x["profitable_exploit_design_astar"]),
            "n_profitable_under_design_d": sum(1 for x in batch_spike_cuts if x["profitable_exploit_design_d"]),
            "total_sq_discount_extracted_bold": round(sum(max(0.0, x["sq_saving_vs_7d_hold_bold"]) for x in batch_spike_cuts), 2),
            "discount_convention_note": (
                "Canonical discount sq_discount_pct = 1 - (hike_fee + spike_window_excess_interest + cut_fee)/hold_7d_excess "
                "(84.02% wstETH M01; 60.96% WETH M03). Alternative cut-fee-only ratios sq_discount_cut_fee_vs_rem_pct "
                "(84.53%/61.33%) and sq_discount_cut_fee_vs_7d_pct (84.62%/61.56%) are recorded alongside."
            ),
            "episodes": batch_spike_cuts,
        },
        "individual_spike_and_cut_episodes": {
            "count": len(indiv_spike_cuts),
            "n_profitable_under_sq": sum(1 for x in indiv_spike_cuts if x["profitable_exploit_sq"]),
            "episodes": indiv_spike_cuts,
        },
        "batch_join_switch_bypass_scan": join_switch_scan,
        "staircase_microstructure_pooled": stair_micro,
        "mechanism_comparison": mech_comparison,
    }

    save_json(RES_DIR / "spike_and_cut.json", out)

    print(
        f"Design D final Hardened underflows={dd_meta['hardened_design_d_underflows']} "
        f"(vs naive highWaterRate diagnostic underflows={dd_meta['legacy_highwater_underflows_on_mainnet']})"
    )
    print(
        f"Batch-transition scan: {join_switch_scan['n_total_rate_lowering_op789']} rate-lowering op{{7,8,9}}, "
        f"{join_switch_scan['n_spike_then_join_or_switch_within_7d']} within 7d "
        f"(op3={join_switch_scan['n_after_indiv_op3_hike']}, op0={join_switch_scan['n_after_indiv_op0_open']}, "
        f"batch={join_switch_scan['n_after_batch_manager_hike']}), "
        f"profitable={join_switch_scan['n_profitable_bypasses_observed']} (max disc={join_switch_scan['max_observed_sq_discount_pct']}%)"
    )
    print(f"Batch spike-and-cut episodes found: {len(batch_spike_cuts)} (profitable SQ={out['batch_spike_and_cut_episodes']['n_profitable_under_sq']}, Design A={out['batch_spike_and_cut_episodes']['n_profitable_under_design_a']}, Design A*={out['batch_spike_and_cut_episodes']['n_profitable_under_design_a_star']}, Design D={out['batch_spike_and_cut_episodes']['n_profitable_under_design_d']})")
    for ep in batch_spike_cuts:
        print(
            f"  [SPIKE-CUT] {ep['branch']:6s} {ep['manager_label']} | {ep['hike_utc']} -> {ep['cut_utc']} ({ep['elapsed_h']:.2f}h) "
            f"| {ep['r_base_pct']:.2f}%->{ep['r_hi_pct']:.2f}%->{ep['r_lo_pct']:.2f}% | debt={ep['debt_bold']:,.0f} "
            f"| SQ tot_disc={ep['sq_discount_pct']:+.2f}% (cut_vs_rem={ep['sq_discount_cut_fee_vs_rem_pct']:+.2f}%, cut_vs_7d={ep['sq_discount_cut_fee_vs_7d_pct']:+.2f}%) "
            f"| A*={ep['design_astar_discount_pct']:+.3f}% | D={ep['design_d_discount_pct']:+.3f}%"
        )
    for samp in ("development", "confirmation", "pooled"):
        mc = mech_comparison[samp]
        tf = mc["total_fees_bold"]
        sv = mc["savings_vs_sq_bold"]
        print(
            f"  [{samp:12s}] SQ={tf['status_quo']:10,.2f} | DesignA={tf['design_a_baseline']:9,.2f} | DesignA*={tf['design_a_star']:9,.2f} (save {sv['design_a_star']:9,.2f}, -{sv['design_a_star_pct_reduction']:.1f}%) "
            f"| DesignD={tf['design_d_forfeited']:8,.2f} (+5%opp={tf['design_d_opp_cost_at_5pct_bold']:,.2f} => {tf['design_d_allin_forfeit_plus_5pct_opp_bold']:8,.2f})"
        )
    print(f"  Staircase microstructure: median step={stair_micro['median_step_bps']:.1f} bp, median elapsed={stair_micro['median_elapsed_h']:.2f}h, median SQ/A*={stair_micro['median_sq_to_dastar_overcharge_ratio']:.2f}x, $-weighted={stair_micro['dollar_weighted_sq_to_dastar_ratio']:.2f}x")
    print("[DONE] Saved spike_and_cut.json")


if __name__ == "__main__":
    main()
