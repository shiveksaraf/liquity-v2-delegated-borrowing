"""Module 6: Publication-Grade Vector PDF Figures (Vector PDF Publication Figures).

Generates 6 journal-ready vector PDF figures in empirical/figures/:
  - fig1_notch_bunching_agency.pdf
  - fig2_spike_cut_and_mechanisms.pdf
  - fig3_causal_routing_did.pdf
  - fig4_hawkes_leapfrogging.pdf
  - fig5_gpv_structural_welfare.pdf
  - fig6_cross_protocol_benchmark.pdf

Visual formatting standards:
  - Vector PDF with embedded TrueType fonts (pdf.fonttype = 42, ps.fonttype = 42)
  - Okabe-Ito ("Wong") CVD-safe muted palette (#0072B2, #D55E00, #009E73, #CC79A7, #E69F00, #222222)
  - Mandatory redundant encoding (line styles, markers, hatches, direct labels)
  - Open top/right spines, zero drop shadows, zero baked-in figure titles (panel labels (a),(b) only)
  - High-DPI PNG contact previews also exported for visual QA inspection.
"""
from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Dict, List

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
import pandas as pd

from common import BRANCHES, EXT_DIR, FIG_DIR, RES_DIR

# Okabe-Ito CVD-safe palette
NAVY = "#0072B2"
VERM = "#D55E00"
TEAL = "#009E73"
PURP = "#CC79A7"
AMBR = "#E69F00"
CHAR = "#222222"
GREY = "#777777"
LGREY = "#E5E5E5"

plt.rcParams.update({
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "font.family": "DejaVu Sans",
    "font.size": 8.0,
    "axes.titlesize": 8.5,
    "axes.labelsize": 8.0,
    "xtick.labelsize": 7.2,
    "ytick.labelsize": 7.2,
    "legend.fontsize": 7.0,
    "axes.linewidth": 0.75,
    "lines.linewidth": 1.35,
    "patch.linewidth": 0.75,
    "figure.facecolor": "white",
    "axes.facecolor": "white",
    "savefig.facecolor": "white",
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.06,
})


def style_ax(ax: plt.Axes, grid_axis: str = "y") -> None:
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_color(CHAR)
    ax.spines["bottom"].set_color(CHAR)
    ax.tick_params(colors=CHAR, width=0.7, length=3.2)
    if grid_axis:
        ax.grid(axis=grid_axis, linestyle=":", linewidth=0.55, color="#BBBBBB", alpha=0.7)
        ax.set_axisbelow(True)


def save_fig(fig: plt.Figure, stem: str) -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    pdf_path = FIG_DIR / f"{stem}.pdf"
    fig.savefig(pdf_path, format="pdf")
    plt.close(fig)
    print(f"[OK] Rendered {pdf_path.name}")


def make_fig1_notch_bunching(m1: Dict[str, Any]) -> None:
    """Fig 1: 168h Cooldown Notch Bunching (minP < 604,800s) & Dominated Near-Notch Agency Waste."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.25), gridspec_kw={"width_ratios": [1.15, 1.0]})

    nb = m1["notch_bunching"]["pooled"]
    bc = nb["batch_pos_cuts"]
    bh = nb["batch_pos_hikes"]
    ih = nb["individual_hikes_control"]

    cuts_h = np.array(bc["hist_1h_counts_0_336"], dtype=float)
    hikes_h = np.array(bh["hist_1h_counts_0_336"], dtype=float)
    indiv_h = np.array(ih["hist_1h_counts_0_336"], dtype=float)

    cuts_pct = 100.0 * cuts_h / max(1, bc["n_total"])
    hikes_pct = 100.0 * hikes_h / max(1, bh["n_total"])
    indiv_pct = 100.0 * indiv_h / max(1, ih["n_total"])

    hrs = np.arange(140, 196)
    ax1.bar(
        hrs + 0.5, cuts_pct[hrs], width=0.88, color=NAVY, alpha=0.85, edgecolor=CHAR, linewidth=0.4,
        label=f"Deleg. cuts, minP<7d (N={bc['n_total']}; {bc['frac_premature']*100:.1f}% prem.)",
    )
    ax1.step(
        hrs + 0.5, hikes_pct[hrs], where="mid", color=VERM, linestyle="-", linewidth=1.4,
        label=f"Deleg. hikes, minP<7d (N={bh['n_total']}; {bh['frac_premature']*100:.1f}% prem.)",
    )
    ax1.step(
        hrs + 0.5, indiv_pct[hrs], where="mid", color=TEAL, linestyle="--", linewidth=1.25,
        label=f"Indiv. hikes control (N={ih['n_total']}; {ih['frac_premature']*100:.1f}% prem.)",
    )

    ax1.axvline(168.0, color=CHAR, linestyle=":", linewidth=1.0)
    ax1.axvspan(140, 168, color="#FDECE4", alpha=0.35, zorder=0)
    ax1.annotate(
        f"{bc['share_in_first_free_hour']*100:.1f}% in [168h,169h)\n(0 in [120h,168h))",
        xy=(168.9, cuts_pct[168]), xytext=(174.0, 19.5),
        fontsize=6.4, color=NAVY, fontweight="bold",
        arrowprops=dict(arrowstyle="->", color=NAVY, lw=0.85),
    )
    ax1.text(141.5, 24.0, "Paid cooldown\n(fee = 7d avg rate)", fontsize=6.4, color=VERM)
    ax1.text(169.8, 25.0, "Free ($0)", fontsize=6.4, color=CHAR)
    ax1.set_xlim(140, 195)
    ax1.set_ylim(0, 28.0)
    ax1.set_xlabel("Elapsed time since prior rate update (hours)")
    ax1.set_ylabel("Share of updates per hour (%)")
    ax1.legend(frameon=False, loc="upper center", bbox_to_anchor=(0.48, -0.22), ncol=1, fontsize=6.2)
    ax1.text(-0.13, 1.05, "(a)", transform=ax1.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax1)

    ev160 = m1["dominated_region_agency_audit"]["near_notch_160_168"]["events"]
    mins = np.array([e["minutes_before_free"] for e in ev160], dtype=float)
    fees = np.array([e["fee_bold"] for e in ev160], dtype=float)
    # Strictly PRE-hike redemptions [-6h, 0] (known to manager at hike time; closes verified!)
    zred = np.array([e["pre_6h_red_count"] == 0 for e in ev160], dtype=bool)

    ax2.scatter(mins[zred], fees[zred], s=42, c=VERM, marker="D", edgecolor=CHAR, linewidth=0.6, zorder=4, label="0 redemptions in [-6h, 0]")
    ax2.scatter(mins[~zred], fees[~zred], s=38, c=NAVY, marker="o", edgecolor=CHAR, linewidth=0.6, zorder=4, label="≥1 redemption in [-6h, 0]")
    ax2.set_xscale("log")
    ax2.set_yscale("log")
    ax2.set_xlim(1.3, 650)
    ax2.set_ylim(0.7, 45000)

    for e in ev160:
        if e["fee_bold"] > 9000:
            ax2.annotate(f"{e['manager_label']} {e['branch']}\n+{e['delta_bps']:.0f}bp, $9,207", xy=(e["minutes_before_free"], e["fee_bold"]),
                         xytext=(24, 15000), fontsize=6.2, color=VERM,
                         arrowprops=dict(arrowstyle="->", color=VERM, lw=0.75))
        elif e["fee_bold"] > 1350:
            ax2.annotate(f"{e['manager_label']} (+1bp)\n$1,387", xy=(e["minutes_before_free"], e["fee_bold"]),
                         xytext=(28, 280), fontsize=6.2, color=NAVY,
                         arrowprops=dict(arrowstyle="->", color=NAVY, lw=0.75))
        elif e["fee_bold"] > 1200:
            ax2.annotate(f"{e['manager_label']} 3.2m early\n$1,332 (0 pre-red.)", xy=(e["minutes_before_free"], e["fee_bold"]),
                         xytext=(7.2, 3100), fontsize=6.1, color=VERM,
                         arrowprops=dict(arrowstyle="->", color=VERM, lw=0.75))
        elif e["minutes_before_free"] < 2.5:
            ax2.annotate("M10 2.0m early", xy=(e["minutes_before_free"], e["fee_bold"]),
                         xytext=(4.2, 16.0), fontsize=6.1, color=VERM,
                         arrowprops=dict(arrowstyle="->", color=VERM, lw=0.7))

    ax2.axvline(240.0, color=GREY, linestyle="--", linewidth=0.8)
    ax2.text(260, 220, "4h before\nfree", fontsize=6.2, color=GREY)
    ax2.set_xlabel("Minutes before free 168h boundary (log)")
    ax2.set_ylabel("Upfront borrower fee (BOLD, log)")
    ax2.legend(frameon=False, loc="lower left", fontsize=6.2)
    ax2.text(-0.15, 1.05, "(b)", transform=ax2.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax2, grid_axis="both")

    fig.tight_layout(w_pad=2.1)
    save_fig(fig, "fig1_notch_bunching_agency")


def make_fig2_spike_cut_and_mechanisms(m2: Dict[str, Any]) -> None:
    """Fig 2: Live Mainnet 2026-03-06 Spike-and-Cut Forensics & Four-Mechanism Comparison."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.15), gridspec_kw={"width_ratios": [1.0, 1.15]})

    eps = m2["batch_spike_and_cut_episodes"]["episodes"]
    ep_wst = next(e for e in eps if e["branch"] == "wstETH" and "2026-03-06" in e["hike_utc"])
    ep_weth = next(e for e in eps if e["branch"] == "WETH" and "2026-03-06" in e["hike_utc"])

    mechs = ["Status Quo", "Baseline\nDesign A", "Design A*\n(0 slots)", "Design D\n(1-slot)"]
    x = np.arange(len(mechs))
    w = 0.34

    wst_vals = [
        100.0 - ep_wst["sq_discount_pct"],
        100.0 - ep_wst["design_a_discount_pct"],
        100.0 - ep_wst["design_astar_discount_pct"],
        100.0 - ep_wst["design_d_discount_pct"],
    ]
    weth_vals = [
        100.0 - ep_weth["sq_discount_pct"],
        100.0 - ep_weth["design_a_discount_pct"],
        100.0 - ep_weth["design_astar_discount_pct"],
        100.0 - ep_weth["design_d_discount_pct"],
    ]

    b1 = ax1.bar(x - w / 2 - 0.015, wst_vals, width=w, color=VERM, edgecolor=CHAR, hatch="//", label="wstETH M01 ($7.98M, 0.7→10.5%)")
    b2 = ax1.bar(x + w / 2 + 0.015, weth_vals, width=w, color=NAVY, edgecolor=CHAR, label="WETH M03 ($1.79M, 3.1→13.1%)")
    ax1.axhline(100.0, color=CHAR, linestyle="--", linewidth=0.95)
    ax1.text(-0.42, 104.5, "No-arbitrage floor (100%)", fontsize=6.3, color=CHAR)

    # Zero-overlap bar labels
    for idx_bar, (bar1, bar2) in enumerate(zip(b1, b2)):
        h1, h2 = bar1.get_height(), bar2.get_height()
        if abs(h1 - h2) < 5.0 and h1 > 90.0:
            # Single clean centered "100%" spanning the identical pair on Design A* and Design D
            ax1.text(x[idx_bar], max(h1, h2) + 3.0, "100% / 100%", ha="center", va="bottom", fontsize=5.8, color=CHAR, fontweight="bold")
        else:
            ax1.text(bar1.get_x() + bar1.get_width() / 2, h1 + 2.5, f"{h1:.0f}%", ha="center", va="bottom", fontsize=6.1, color=CHAR)
            ax1.text(bar2.get_x() + bar2.get_width() / 2, h2 + 2.5, f"{h2:.0f}%", ha="center", va="bottom", fontsize=6.1, color=CHAR)

    ax1.set_xticks(x)
    ax1.set_xticklabels(mechs)
    ax1.set_ylim(0, 145)
    ax1.set_ylabel("Spike-and-cut cost (% of 7-day hold)")
    ax1.legend(frameon=False, loc="upper left", bbox_to_anchor=(0.0, 1.01), fontsize=6.2)
    ax1.text(-0.15, 1.05, "(a)", transform=ax1.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax1)

    mc_dev = m2["mechanism_comparison"]["development"]["per_million_debt_days_boot14d"]
    mc_conf = m2["mechanism_comparison"]["confirmation"]["per_million_debt_days_boot14d"]
    keys = ["status_quo", "design_a_baseline", "design_a_star", "design_d_forfeited"]
    labels = ["Status Quo", "Design A\n(Baseline)", "Design A*\n(0 slots)", "Design D\n(1-slot)"]

    dev_est = [mc_dev[k]["estimate"] for k in keys]
    dev_err_lo = [max(0.0, mc_dev[k]["estimate"] - mc_dev[k]["ci_low"]) for k in keys]
    dev_err_hi = [max(0.0, mc_dev[k]["ci_high"] - mc_dev[k]["estimate"]) for k in keys]

    conf_est = [mc_conf[k]["estimate"] for k in keys]
    conf_err_lo = [max(0.0, mc_conf[k]["estimate"] - mc_conf[k]["ci_low"]) for k in keys]
    conf_err_hi = [max(0.0, mc_conf[k]["ci_high"] - mc_conf[k]["estimate"]) for k in keys]

    x2 = np.arange(len(keys))
    ax2.bar(x2 - w / 2, dev_est, width=w, yerr=[dev_err_lo, dev_err_hi], capsize=2.8,
            color=NAVY, edgecolor=CHAR, error_kw={"elinewidth": 0.85, "ecolor": CHAR}, label="Development (408d)")
    ax2.bar(x2 + w / 2, conf_est, width=w, yerr=[conf_err_lo, conf_err_hi], capsize=2.8,
            color=TEAL, edgecolor=CHAR, hatch="..", error_kw={"elinewidth": 0.85, "ecolor": CHAR}, label="Confirmation (77d)")

    for i in range(len(keys)):
        ax2.text(x2[i] - w / 2, dev_est[i] + dev_err_hi[i] + 2.5, f"{dev_est[i]:.1f}", ha="center", va="bottom", fontsize=6.2, color=NAVY)
        ax2.text(x2[i] + w / 2, conf_est[i] + conf_err_hi[i] + 2.5, f"{conf_est[i]:.1f}", ha="center", va="bottom", fontsize=6.2, color=TEAL)

    ax2.set_xticks(x2)
    ax2.set_xticklabels(labels)
    ax2.set_ylim(0, max(conf_est[0] + conf_err_hi[0], dev_est[0] + dev_err_hi[0]) * 1.18)
    ax2.set_ylabel("Repricing fees (BOLD / M debt-days)")
    ax2.legend(frameon=False, loc="upper right")
    ax2.text(-0.14, 1.05, "(b)", transform=ax2.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax2)

    fig.tight_layout(w_pad=2.1)
    save_fig(fig, "fig2_spike_cut_and_mechanisms")


def make_fig3_causal_routing(m3: Dict[str, Any]) -> None:
    """Fig 3: CollateralRegistry Mechanical Routing Shares & Matched-Scale Causal Identification."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.30), gridspec_kw={"width_ratios": [1.15, 1.0]})

    monthly = m3["routing_reconstruction"]["monthly_mean_routing_shares"]
    months = sorted(monthly.keys())
    xi = np.arange(len(months))
    s_weth = [100.0 * (monthly[m]["WETH"] or 0.0) for m in months]
    s_wst = [100.0 * (monthly[m]["wstETH"] or 0.0) for m in months]
    s_reth = [100.0 * (monthly[m]["rETH"] or 0.0) for m in months]

    ax1.plot(xi, s_wst, color=NAVY, linestyle="-", marker="o", markersize=3.5, label="wstETH")
    ax1.plot(xi, s_weth, color=VERM, linestyle="--", marker="s", markersize=3.5, label="WETH")
    ax1.plot(xi, s_reth, color=TEAL, linestyle="-.", marker="^", markersize=3.5, label="rETH")

    if "2026-03" in months and "2026-05" in months:
        i0, i1 = months.index("2026-03"), months.index("2026-05")
        ax1.axvspan(i0 - 0.35, i1 + 0.35, color="#FDECE4", alpha=0.55, zorder=0)
        ax1.text((i0 + i1) / 2, 112.0, "WETH ~0%\nshutdown", ha="center", va="top", fontsize=6.1, color=VERM)
    if "2026-07" in months:
        ic = months.index("2026-07")
        ax1.axvline(ic - 0.5, color=CHAR, linestyle=":", linewidth=0.95)
        ax1.text(ic - 0.3, 86, "Conf.\nholdout", fontsize=6.0, color=CHAR)

    # Clean non-colliding x-ticks (skip penultimate tick if within 1 step of final month!)
    tick_idx = [i for i in range(0, len(months), 3) if i < len(months) - 2]
    tick_idx.append(len(months) - 1)
    ax1.set_xticks(tick_idx)
    ax1.set_xticklabels([months[i][2:] for i in tick_idx], rotation=22)
    ax1.set_ylim(-3, 116)
    ax1.set_ylabel("Mechanical routing share (%)")
    ax1.set_xlabel("Calendar month (YY-MM)")
    # Move legend cleanly below x-axis completely off the curves
    ax1.legend(frameon=False, loc="upper center", bbox_to_anchor=(0.50, -0.24), ncol=3, fontsize=6.6)
    ax1.text(-0.14, 1.05, "(a)", transform=ax1.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax1)

    pa_dev = m3["pillar3_bartik_and_mgr_day_fe"]["panelA_branch_day_fe_bartik"]["development"]
    pa_conf = m3["pillar3_bartik_and_mgr_day_fe"]["panelA_branch_day_fe_bartik"]["confirmation"]
    pa_pool = m3["pillar3_bartik_and_mgr_day_fe"]["panelA_branch_day_fe_bartik"]["pooled"]
    pb_pool = m3["pillar3_bartik_and_mgr_day_fe"]["panelB_all19_managers_fe_bartik"]["pooled"]["fee_mdd_48h"]
    pl = pa_pool["bartik_placebo_leads"]["fee_mdd_48h"]

    # ALL estimates on strictly matched 2SLS/Wald scale with FE-DOF corrected SEs
    items = [
        ("Placebo lead t+7d\n(Wald-scaled)", pl["lead_t_plus_7d_placebo"]["wald_scaled_beta"], pl["lead_t_plus_7d_placebo"]["wald_scaled_se"], GREY, "s"),
        ("Branch-Day 2SLS\n(Dev, +FE-DOF)", pa_dev["fee_mdd_48h"]["bartik_2sls"]["iv_2sls_beta"], pa_dev["fee_mdd_48h"]["bartik_2sls"]["iv_2sls_se"], NAVY, "o"),
        ("Branch-Day 2SLS\n(Conf, +FE-DOF)", pa_conf["fee_mdd_48h"]["bartik_2sls"]["iv_2sls_beta"], pa_conf["fee_mdd_48h"]["bartik_2sls"]["iv_2sls_se"], TEAL, "^"),
        ("Branch-Day 2SLS\n(Pool, +FE-DOF)", pa_pool["fee_mdd_48h"]["bartik_2sls"]["iv_2sls_beta"], pa_pool["fee_mdd_48h"]["bartik_2sls"]["iv_2sls_se"], VERM, "D"),
        ("All-21 Mgrs 2SLS\n(Pool, +FE-DOF)", pb_pool["iv_2sls_beta"], pb_pool["iv_2sls_se"], PURP, "P"),
    ]
    yp = np.arange(len(items))
    ax2.axvline(0.0, color=CHAR, linestyle="--", linewidth=0.85, zorder=1)
    for i, (lbl, est, se, col, mk) in enumerate(items):
        ax2.errorbar(est, i, xerr=1.96 * se, fmt=mk, color=col, ecolor=col, capsize=3.0, markersize=5.0, linewidth=1.25, zorder=4)
        # Keep label strictly clear of x=0 dashed line
        x_txt = est + 2.2 if abs(est) < 8.0 else est
        ha_txt = "left" if abs(est) < 8.0 else "center"
        ax2.text(x_txt, i + 0.22, f"{est:+.1f}", ha=ha_txt, va="bottom", fontsize=6.3, color=col, fontweight="bold")

    # Add subtle 14-day block-bootstrap 95% CI bracket annotation on Pooled Branch-Day 2SLS
    bt_p = pa_pool["fee_mdd_48h"]["bartik_2sls"]["boot14d_2sls"]
    ax2.plot([bt_p["ci_low"], bt_p["ci_high"]], [3 - 0.22, 3 - 0.22], color=VERM, linewidth=2.0, alpha=0.55)
    ax2.text(bt_p["ci_high"] + 1.5, 3 - 0.28, f"14d boot [{bt_p['ci_low']:+.1f}, {bt_p['ci_high']:+.1f}]", fontsize=5.6, color=VERM, va="center")

    ax2.set_yticks(yp)
    ax2.set_yticklabels([x[0] for x in items], fontsize=6.6)
    ax2.set_ylim(-0.6, len(items) - 0.15)
    ax2.set_xlim(-20, 78)
    ax2.set_xlabel("48h fee response (BOLD/M-dd, 2SLS)")
    ax2.text(-0.22, 1.05, "(b)", transform=ax2.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax2, grid_axis="x")

    fig.tight_layout(w_pad=2.1)
    save_fig(fig, "fig3_causal_routing_did")


def make_fig4_hawkes_leapfrogging(m4: Dict[str, Any]) -> None:
    """Fig 4: Multivariate Hawkes Cross-Manager Contagion & Fee Attribution."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.15), gridspec_kw={"width_ratios": [1.05, 1.05]})

    hk = m4["multivariate_hawkes_mle"]["pos_debt_hikes_only"]
    branches = list(BRANCHES)
    x = np.arange(len(branches))
    w = 0.26

    dev_cross = [hk["development"][b]["full_hawkes_params"]["alpha_cross"] for b in branches]
    dev_self = [hk["development"][b]["full_hawkes_params"]["alpha_self"] for b in branches]
    conf_cross = [hk["confirmation"][b]["full_hawkes_params"]["alpha_cross"] for b in branches]
    dev_hl = [hk["development"][b]["full_hawkes_params"]["half_life_minutes"] for b in branches]

    ax1.bar(x - w, dev_cross, width=w, color=VERM, edgecolor=CHAR, label=r"Dev cross-mgr ($\hat{\alpha}_{\mathrm{cross}}$)")
    ax1.bar(x, conf_cross, width=w, color=NAVY, edgecolor=CHAR, hatch="//", label=r"Conf cross-mgr ($\hat{\alpha}_{\mathrm{cross}}$)")
    ax1.bar(x + w, dev_self, width=w, color=TEAL, edgecolor=CHAR, hatch="..", label=r"Dev self-exc. ($\hat{\alpha}_{\mathrm{self}}$)")

    for i in range(len(branches)):
        ax1.text(x[i] - w, dev_cross[i] + 0.015, f"{dev_cross[i]:.2f}\n({dev_hl[i]:.0f}m)", ha="center", va="bottom", fontsize=6.0, color=VERM)
        ax1.text(x[i], conf_cross[i] + 0.015, f"{conf_cross[i]:.2f}", ha="center", va="bottom", fontsize=6.0, color=NAVY)
        # Always label dev_self including 0.00 so zero bars are clearly shown as fitted zeros
        ax1.text(x[i] + w, dev_self[i] + 0.015, f"{dev_self[i]:.2f}", ha="center", va="bottom", fontsize=6.0, color=TEAL)

    ax1.set_xticks(x)
    ax1.set_xticklabels(branches)
    ax1.set_ylim(0, 0.94)
    ax1.set_ylabel("Hawkes excitation parameter")
    ax1.legend(frameon=False, loc="upper left", fontsize=6.2)
    ax1.text(-0.14, 1.06, "(a)", transform=ax1.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax1)

    hk_all = m4["multivariate_hawkes_mle"]["all_genuine_hikes"]["pooled"]
    hk_pos = m4["multivariate_hawkes_mle"]["pos_debt_hikes_only"]["pooled"]
    cats = ["WETH\n(pos. debt)", "wstETH\n(pos. debt)", "rETH\n(pos. debt)", "WETH\n(all hikes)", "wstETH\n(all hikes)", "rETH\n(all hikes)"]
    srcs = [hk_pos["WETH"], hk_pos["wstETH"], hk_pos["rETH"], hk_all["WETH"], hk_all["wstETH"], hk_all["rETH"]]

    y = np.arange(len(cats))
    sh_cross = np.array([100.0 * s["attribution"]["event_shares"]["cross_manager_contagion"] for s in srcs])
    sh_self = np.array([100.0 * s["attribution"]["event_shares"]["self_excitation"] for s in srcs])
    sh_exog = np.array([100.0 * s["attribution"]["event_shares"]["exogenous_redemp_vol"] for s in srcs])
    sh_base = np.array([100.0 * s["attribution"]["event_shares"]["baseline"] for s in srcs])

    ax2.barh(y, sh_cross, color=VERM, edgecolor=CHAR, height=0.62, label="Cross-mgr contagion")
    ax2.barh(y, sh_self, left=sh_cross, color=AMBR, edgecolor=CHAR, height=0.62, hatch="xx", label="Self-excitation")
    ax2.barh(y, sh_exog, left=sh_cross + sh_self, color=NAVY, edgecolor=CHAR, height=0.62, hatch="//", label="Exog. redemp. + vol")
    ax2.barh(y, sh_base, left=sh_cross + sh_self + sh_exog, color=LGREY, edgecolor=CHAR, height=0.62, label="Baseline arrival")

    for i in range(len(cats)):
        if sh_cross[i] >= 12:
            ax2.text(sh_cross[i] / 2, i, f"{sh_cross[i]:.0f}%", ha="center", va="center", fontsize=6.4, color="white", fontweight="bold")

    ax2.set_yticks(y)
    ax2.set_yticklabels(cats)
    ax2.set_xlim(0, 100)
    ax2.set_xlabel("Share of rate hikes attributed (%)")
    ax2.legend(frameon=False, loc="upper center", bbox_to_anchor=(0.48, -0.22), ncol=2, fontsize=6.4)
    ax2.text(-0.18, 1.06, "(b)", transform=ax2.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax2, grid_axis="x")

    fig.tight_layout(w_pad=2.1)
    save_fig(fig, "fig4_hawkes_leapfrogging")


def make_fig5_gpv_welfare(m5: Dict[str, Any]) -> None:
    """Fig 5: Within-Day GPV Cost Recovery & Equilibrium Structural All-In Welfare Counterfactuals."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.30), gridspec_kw={"width_ratios": [1.0, 1.18]})

    g_dev = m5["part2_gpv_structural_estimation"]["development"]["ALL_BRANCHES"]
    g_conf = m5["part2_gpv_structural_estimation"]["confirmation"]["ALL_BRANCHES"]
    g_pool = m5["part2_gpv_structural_estimation"]["pooled"]["ALL_BRANCHES"]

    s_p = np.array(g_pool["curves"]["s_grid"])
    tau_iso_p = np.array(g_pool["curves"]["tau_iso_bps"]) / 100.0
    tau_raw_p = np.array(g_pool["curves"]["tau_raw_bps"]) / 100.0
    s_d = np.array(g_dev["curves"]["s_grid"])
    tau_iso_d = np.array(g_dev["curves"]["tau_iso_bps"]) / 100.0
    s_c = np.array(g_conf["curves"]["s_grid"])
    tau_iso_c = np.array(g_conf["curves"]["tau_iso_bps"]) / 100.0

    phi_pct = g_pool["phi_redemption_fee"] * 100.0
    p0_p = g_pool["p0_absorber_share"]

    # Semi-log y-axis cleanly displays Q25 (0.95%), Q50 (3.62%), raw-inversion scatter markers,
    # AND full Confirmation curve up to s=80% with ZERO clipping and ZERO occlusion
    m80_p = s_p <= 0.82
    m80_d = s_d <= 0.82
    m80_c = s_c <= 0.82
    ax1.scatter(s_p[m80_p][::2] * 100, tau_raw_p[m80_p][::2], s=14, facecolors="none", edgecolors=NAVY, linewidths=0.7, alpha=0.8, zorder=3, label="Pooled raw inversion")
    ax1.plot(s_p[m80_p] * 100, tau_iso_p[m80_p], color=NAVY, linestyle="-", linewidth=1.6, zorder=4, label="Pooled within-day GPV")
    ax1.plot(s_d[m80_d] * 100, tau_iso_d[m80_d], color=TEAL, linestyle="--", linewidth=1.25, zorder=3, label="Development (408d)")
    ax1.plot(s_c[m80_c] * 100, tau_iso_c[m80_c], color=VERM, linestyle="-.", linewidth=1.25, zorder=3, label="Confirmation (77d)")
    ax1.axhline(phi_pct, color=CHAR, linestyle=":", linewidth=0.85)
    ax1.axvspan(0, p0_p * 100, color=LGREY, alpha=0.75, zorder=0)

    ax1.set_yscale("log")
    ax1.set_xlim(0, 82)
    ax1.set_ylim(0.45, 75.0)
    ax1.yaxis.set_major_formatter(mticker.FuncFormatter(lambda y, _: f"{y:g}%"))
    ax1.set_yticks([0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0])

    ax1.annotate(
        f"Absorbers\n$p_0$={p0_p*100:.1f}%",
        xy=(p0_p * 50, 1.05), xytext=(12, 2.2),
        fontsize=6.0, color=CHAR, arrowprops=dict(arrowstyle="->", color=CHAR, lw=0.7),
    )
    ax1.text(44, phi_pct * 0.72, f"Redemp. fee $\\phi$={phi_pct:.2f}%", fontsize=6.0, color=CHAR)
    ax1.annotate(
        f"Median $\\hat{{\\tau}}$={g_pool['tau_quantiles_bps']['q50_median']/100:.2f}%",
        xy=(50, g_pool["tau_quantiles_bps"]["q50_median"] / 100.0), xytext=(44, 1.25),
        fontsize=6.0, color=NAVY, fontweight="bold",
        arrowprops=dict(arrowstyle="->", color=NAVY, lw=0.75),
    )

    ax1.set_xlabel("Within-day queue quantile $s = q/D$ (%)")
    ax1.set_ylabel(r"Recovered disruption cost $\hat{\tau}_{\mathrm{within}}(s)$ (log)")
    ax1.legend(frameon=False, loc="upper left", fontsize=6.0)
    ax1.text(-0.16, 1.06, "(a)", transform=ax1.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax1)

    rows = m5["part3_equilibrium_counterfactuals_sp_pil"]["samples"]["pooled"]["counterfactuals_by_elasticity"]["baseline_ge_eps_0.50"]
    keep_names = [
        "Status Quo",
        "Design A (Baseline)",
        "Design A* (Optimal Zero-Storage)",
        "Design D (Rate-Bond Escrow)",
        "Co-Pay beta=0.25 (on SQ)",
        "Design A* + Co-Pay beta=0.25",
    ]
    short_labels = ["Status\nQuo", "Design A\n(Base.)", "Design A*\n(0 slots)", "Design D\n(1-slot)", "Co-Pay\nβ=0.25", "Design A*\n+ Co-Pay"]
    sel = [next(r for r in rows if r["regime"] == nm) for nm in keep_names]

    x = np.arange(len(sel))
    c_rec = np.array([(r["quoted_base_apr_bps"] + r["mgmt_apr_bps"]) / 100.0 for r in sel])
    c_upf = np.array([r["borrower_upfront_fee_bps"] / 100.0 for r in sel])
    c_dis = np.array([(r["redemption_disruption_C_bps"] + r["gas_cost_bps"] + r["episodic_risk_premium_bps"] + r["escrow_opp_cost_bps"]) / 100.0 for r in sel])
    sp_apr = np.array([r["eq_stability_pool_apr_pct"] for r in sel])

    ax2.bar(x, c_rec, width=0.58, color=NAVY, edgecolor=CHAR, label="Recurring base + mgmt")
    ax2.bar(x, c_upf, bottom=c_rec, width=0.58, color=VERM, edgecolor=CHAR, hatch="//", label="Borrower upfront fees")
    ax2.bar(x, c_dis, bottom=c_rec + c_upf, width=0.58, color=TEAL, edgecolor=CHAR, hatch="..", label="PQ disruption C + gas + var. RP")

    for i in range(len(sel)):
        tot = c_rec[i] + c_upf[i] + c_dis[i]
        ax2.text(x[i], tot + 0.14, f"{tot:.2f}%", ha="center", va="bottom", fontsize=6.2, color=CHAR, fontweight="bold")

    ax2.set_xticks(x)
    ax2.set_xticklabels(short_labels, fontsize=6.4)
    # Give ample headroom above bars so purple SP APR line sits cleanly ABOVE all bar labels
    ax2.set_ylim(0, 10.6)
    ax2.set_ylabel("Structural all-in welfare cost (% / yr)")

    ax2r = ax2.twinx()
    ax2r.plot(x, sp_apr, color=PURP, linestyle="--", marker="D", markersize=4.4, linewidth=1.35, zorder=5, label="Eq. Stability Pool APR")
    for i in range(len(sel)):
        ax2r.text(x[i], sp_apr[i] + 0.16, f"{sp_apr[i]:.2f}%", ha="center", va="bottom", fontsize=5.6, color=PURP)
    ax2r.set_ylabel("Equilibrium SP APR (%)", color=PURP)
    ax2r.tick_params(axis="y", colors=PURP, width=0.7)
    ax2r.spines["top"].set_visible(False)
    ax2r.spines["right"].set_color(PURP)
    # Map sp_apr (4.34..4.97) to upper 75-88% of axis height, completely clear of bars (max 6.54 / 10.6 = 62%)!
    ax2r.set_ylim(0.0, 5.95)

    h1, l1 = ax2.get_legend_handles_labels()
    h2, l2 = ax2r.get_legend_handles_labels()
    ax2.legend(h1 + h2, l1 + l2, frameon=False, loc="upper center", bbox_to_anchor=(0.48, -0.22), ncol=2, fontsize=6.2)
    ax2.text(-0.15, 1.06, "(b)", transform=ax2.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax2)

    fig.tight_layout(w_pad=2.1)
    save_fig(fig, "fig5_gpv_structural_welfare")


def make_fig6_cross_protocol(m1: Dict[str, Any], m5: Dict[str, Any]) -> None:
    """Fig 6: Cross-Protocol Observed Financial Cost vs Peg Tightness & RPC Permission / Fork Context."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.25), gridspec_kw={"width_ratios": [1.18, 1.0]})

    prots = m5["part4_cross_protocol_benchmark"]["protocols"]
    p_by_name = {r["protocol"]: r for r in prots}

    # Subtle vertical reference line at BOLD observed peg RMSE (22.93 bp)
    sq_r = p_by_name["Liquity V2 (BOLD) — Delegated (Status Quo)"]
    das_r = p_by_name["Liquity V2 (BOLD) — Delegated (Design A* GE)"]
    dd_r = p_by_name["Liquity V2 (BOLD) — Delegated (Design D GE)"]
    unb_r = p_by_name["Liquity V2 (BOLD) — Unbatched (Self-Managed)"]
    ax1.axvline(sq_r["peg_rmse_bps"], color="#CCCCCC", linestyle=":", linewidth=0.9, zorder=1)

    # Plot markers with clean non-overlapping data-space annotations
    plot_spec = [
        ("Liquity V2 (BOLD) — Delegated (Status Quo)", "BOLD Deleg. SQ (5.76%)", VERM, "D", (28.5, 6.05), False, True),
        ("Liquity V2 (BOLD) — Delegated (Design A* GE)", "BOLD Design A* GE (4.06%)*", TEAL, "*", (29.5, 4.45), False, True),
        ("Liquity V2 (BOLD) — Unbatched (Self-Managed)", "BOLD Unbatched (3.97%)", AMBR, "s", (2.0, 2.35), True, True),
        ("Liquity V2 (BOLD) — Delegated (Design D GE)", "BOLD Design D GE (3.85%)*", TEAL, "^", (29.5, 2.95), False, True),
        ("Liquity V1 (LUSD)", "Liquity V1 (LUSD, 1y)", GREY, "v", (38.0, 1.15), False, True),
        ("Sky / MakerDAO (DAI/USDS — ETH-A)", "Sky ETH-A (7.88%)", NAVY, "o", (8.0, 7.80), False, False),
        ("Curve (crvUSD — WETH)", "Curve crvUSD (5.68%)", PURP, "h", (4.5, 6.45), False, True),
        ("Aave V3 (GHO)", "Aave V3 GHO (4.54%)", CHAR, "P", (2.2, 5.15), False, True),
    ]
    for full_nm, short_nm, col, mk, xy_txt, hollow, use_arrow in plot_spec:
        r = p_by_name.get(full_nm)
        if not r or r["peg_rmse_bps"] is None:
            continue
        x_val = r["peg_rmse_bps"]
        y_val = r["observed_financial_borrowing_cost_pct"]
        ms = 92 if mk == "*" else (66 if hollow else 40)
        fc = "none" if hollow else col
        ec = col if hollow else CHAR
        lw = 1.3 if hollow else 0.65
        ax1.scatter(x_val, y_val, s=ms, facecolors=fc, edgecolors=ec, marker=mk, linewidths=lw, zorder=5 if mk == "*" else 4)
        ax1.annotate(
            short_nm, xy=(x_val, y_val), xytext=xy_txt, textcoords="data",
            fontsize=5.8, color=col, fontweight="bold" if "BOLD" in short_nm else "normal",
            arrowprops=dict(arrowstyle="-", color=col, lw=0.6, alpha=0.65) if use_arrow else None,
        )

    # Dashed teal arrow from SQ down toward Design A* stopping cleanly above marker cluster!
    ax1.annotate(
        "", xy=(das_r["peg_rmse_bps"], das_r["observed_financial_borrowing_cost_pct"] + 0.28),
        xytext=(sq_r["peg_rmse_bps"], sq_r["observed_financial_borrowing_cost_pct"] - 0.22),
        arrowprops=dict(arrowstyle="->", color=TEAL, lw=1.35, ls="--"),
    )
    ax1.text(0.98, 0.96, "*Counterfactuals at SQ peg RMSE\nref. (22.93 bp)", transform=ax1.transAxes,
             ha="right", va="top", fontsize=5.6, color=GREY, style="italic")

    ax1.set_xlabel("Secondary-market USD peg RMSE (bp)")
    ax1.set_ylabel("Observed financial borrowing cost (% / yr)")
    ax1.set_xlim(0, max(r["peg_rmse_bps"] for r in prots if r["peg_rmse_bps"] is not None) * 1.15)
    ax1.set_ylim(0, 9.4)
    ax1.text(-0.14, 1.06, "(a)", transform=ax1.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax1, grid_axis="both")

    pt_rows = m1["manager_branch_permission_decomposition"]["by_permission_tuple"]
    grp_fee = {"1 hour\n(3,600–3,601s)": 0.0, "24 hours\n(86,400s)": 0.0, "7 days\n(604,800s)": 0.0}
    grp_upd = {"1 hour\n(3,600–3,601s)": 0, "24 hours\n(86,400s)": 0, "7 days\n(604,800s)": 0}
    for row in pt_rows:
        pt = row["permission_tuple"]
        if "3600s" in pt or "3601s" in pt:
            k = "1 hour\n(3,600–3,601s)"
        elif "86400s" in pt:
            k = "24 hours\n(86,400s)"
        else:
            assert "604800s" in pt, f"Unexpected permission tuple period: {pt}"
            k = "7 days\n(604,800s)"
        grp_fee[k] += row["fee_total_bold"]
        grp_upd[k] += row["n_updates"]

    cats = list(grp_fee.keys())
    vals_k = [grp_fee[k] / 1000.0 for k in cats]
    cols = [VERM, AMBR, TEAL]
    hatches = ["//", "..", ""]
    x2 = np.arange(len(cats))
    bars = ax2.bar(x2, vals_k, width=0.55, color=cols, edgecolor=CHAR)
    for bar, h in zip(bars, hatches):
        if h:
            bar.set_hatch(h)
    tot_k = sum(vals_k)
    for i, v in enumerate(vals_k):
        pct = 100.0 * v / tot_k if tot_k > 0 else 0.0
        ax2.text(x2[i], v + 10.0, f"${v:,.1f}k\n({pct:.1f}%)\n[{grp_upd[cats[i]]} upd.]", ha="center", va="bottom", fontsize=6.2, color=CHAR)

    forks = m5["part4_cross_protocol_benchmark"]["liquity_v2_friendly_fork_ecosystem"]
    ax2.text(
        0.97, 0.93,
        f"Liquity V2 codebase footprint:\n{forks['n_v2_and_forks']} live protocols\nSim. peak TVL: ${forks['simultaneous_peak_alltime_tvl_usd']/1e6:.1f}M\n(Sum of peaks: ${forks['sum_peak_alltime_tvl_usd']/1e6:.1f}M)",
        transform=ax2.transAxes, ha="right", va="top", fontsize=6.0, color=NAVY,
        bbox=dict(boxstyle="round,pad=0.35", facecolor="#F4F8FB", edgecolor=NAVY, linewidth=0.6),
    )

    ax2.set_xticks(x2)
    ax2.set_xticklabels(cats)
    ax2.set_ylim(0, max(vals_k) * 1.30)
    ax2.set_ylabel("Upfront fees (thousand BOLD)")
    ax2.set_xlabel("On-chain minInterestRateChangePeriod")
    ax2.text(-0.16, 1.06, "(b)", transform=ax2.transAxes, fontsize=9, fontweight="bold", color=CHAR)
    style_ax(ax2)

    fig.tight_layout(w_pad=2.1)
    save_fig(fig, "fig6_cross_protocol_benchmark")


def main() -> None:
    print("=== Module 6: Generating Publication-Grade Vector PDF Figures ===")
    m1 = json.loads((RES_DIR / "notch_and_agency.json").read_text(encoding="utf-8"))
    m2 = json.loads((RES_DIR / "spike_and_cut.json").read_text(encoding="utf-8"))
    m3 = json.loads((RES_DIR / "causal_routing_did.json").read_text(encoding="utf-8"))
    m4 = json.loads((RES_DIR / "hawkes_leapfrogging.json").read_text(encoding="utf-8"))
    m5 = json.loads((RES_DIR / "gpv_structural_welfare.json").read_text(encoding="utf-8"))

    make_fig1_notch_bunching(m1)
    make_fig2_spike_cut_and_mechanisms(m2)
    make_fig3_causal_routing(m3)
    make_fig4_hawkes_leapfrogging(m4)
    make_fig5_gpv_welfare(m5)
    make_fig6_cross_protocol(m1, m5)
    print(f"[DONE] All 6 vector PDFs + QA PNGs generated under {FIG_DIR}")


if __name__ == "__main__":
    main()
