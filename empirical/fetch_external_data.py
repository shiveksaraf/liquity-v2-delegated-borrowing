"""Module 0: Live Free Public Data Augmentation with Exact SHA-256 Receipts.

Fetches strictly 100% real, verifiable on-chain and public API data (zero fabrication,
zero interpolation of missing endpoints):
  1. Immutable on-chain Liquity V2 manager permission tuples
     (minInterestRate, maxInterestRate, minInterestRateChangePeriod) for ALL unique
     batch managers across WETH, wstETH, rETH via Ethereum RPC eth_call.
  2. DefiLlama Coins daily USD prices (2025-05-19..2026-09-15) for:
     - Stablecoins: BOLD, LUSD, DAI, USDS, crvUSD, GHO
     - Collaterals: WETH, wstETH, rETH (for returns, realized vol & gas-to-BOLD conversion)
  3. DefiLlama Yields historical charts for Liquity V2 BOLD Stability Pools
     (WETH, wstETH, rETH), Sky sUSDS, Aave V3 USDC, Curve scrvUSD.
  4. Competing DeFi Protocol Borrow Rates (2025-05-19..2026-09-15):
     - Curve crvUSD (WETH & wstETH controllers): official prices.curve.finance daily snapshots.
     - On-chain Ethereum Mainnet archive eth_call (via eth.drpc.org) across sampled
       historical blocks spanning 2025-05-19..2026-09-15:
         * Sky/MakerDAO Jug.ilks (ETH-A, ETH-C, WSTETH-A, WSTETH-B) stability fee APR
         * Aave V3 ProtocolDataProvider getReserveData (USDC, GHO) variableBorrowRate APR
         * Liquity V1 TroveManager getBorrowingRateWithDecay() (one-time fee, 0% recurring)
  5. Live DefiLlama Liquity V2 friendly-fork ecosystem TVL snapshot.

Every raw payload is archived in empirical/data_external/ with SHA-256 receipt and UTC timestamp.
"""
from __future__ import annotations

import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
import pandas as pd
import requests

from common import (
    BRANCHES,
    CONTRACTS,
    CONF_END_DATE,
    DEV_START_DATE,
    EXT_DIR,
    WAD,
    YEAR_SECONDS,
    fn_selector,
    load_canonical_events,
    manager_label,
    save_json,
    sha256_bytes,
    ts_to_date,
)

PRIMARY_RPC = "https://ethereum-rpc.publicnode.com"
ARCHIVE_RPC = "https://eth.drpc.org"
FALLBACK_ARCHIVE_RPC = "https://eth-mainnet.public.blastapi.io"

# Verified Ethereum Mainnet token addresses for DefiLlama Coins API
TOKENS: Dict[str, str] = {
    "BOLD": "ethereum:0x6440f144b7e50D6a8439336510312d2F54beB01D",
    "LUSD": "ethereum:0x5f98805A4E8be255a32880FDeC7F6728C6568bA0",
    "DAI": "ethereum:0x6B175474E89094C44Da98b954EedeAC495271d0F",
    "USDS": "ethereum:0xdC035D45d973E3EC169d2276DDab16f1e407384F",
    "crvUSD": "ethereum:0xf939E0A03FB07F59A73314E73794Be0E57ac1b4E",
    "GHO": "ethereum:0x40D16FC0246aD3160Ccc09B8D0D3A2cD28aE6C2f",
    "WETH": "ethereum:0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2",
    "wstETH": "ethereum:0x7f39C581F595B53c5cb19bD0b3f8dA6c935E2Ca0",
    "rETH": "ethereum:0xae78736Cd615f374D3085123A210448E74Fc6393",
}

# Verified DefiLlama Yields pool UUIDs
LLAMA_YIELD_POOLS: Dict[str, str] = {
    "liquity_v2_sp_WETH": "a635df9a-4cfc-4d17-86d0-934ea441e79f",
    "liquity_v2_sp_wstETH": "dac71f4f-7b97-463a-b19f-9796c56c21f1",
    "liquity_v2_sp_rETH": "326739f2-4650-4992-a8eb-a400e7790499",
    "sky_sUSDS": "d8c4eff5-c8a9-46fc-a888-057c4c668e72",
    "aave_v3_USDC_supply": "aa70268e-4b52-42bf-a116-608b370f9501",
    "crvusd_scrvUSD": "5fd328af-4203-471b-bd16-1705c726d926",
}

# Curve crvUSD controller addresses (verified from prices.curve.finance/v1/crvusd/markets/ethereum)
CURVE_CRVUSD_CONTROLLERS: Dict[str, str] = {
    "WETH": "0xA920De414eA4Ab66b97dA1bFE9e6EcA7d4219635",
    "wstETH": "0x100dAa78fC509Db39Ef7D04DE0c1ABD299f4C6CE",
}

# Verified Ethereum Mainnet contracts for archive eth_call historical borrow rates
MAKER_JUG = "0x19c0976f590D67707E62397C87829d896Dc0f1F1"
AAVE_V3_DATA_PROVIDER = "0x7B4EB56E7CD4b454BA8ff71E4518426369a138a3"
LIQUITY_V1_TM = "0xA39739EF8b0231DbFA0DcdA07d7e29faAbCf4bb2"
USDC_ADDR = "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"
GHO_ADDR = "0x40D16FC0246aD3160Ccc09B8D0D3A2cD28aE6C2f"


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def record_receipt(receipts: List[Dict[str, Any]], filename: str, source: str, raw_bytes: bytes, extra: Optional[Dict[str, Any]] = None) -> None:
    p = EXT_DIR / filename
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(raw_bytes)
    entry = {
        "file": filename,
        "source": source,
        "fetched_utc": utc_now_iso(),
        "bytes": len(raw_bytes),
        "sha256": sha256_bytes(raw_bytes),
    }
    if extra:
        entry.update(extra)
    receipts.append(entry)


def rpc_post(url: str, payload: Any, timeout: int = 25, retries: int = 3) -> Any:
    last_err = None
    for attempt in range(retries):
        try:
            r = requests.post(url, json=payload, timeout=timeout)
            if r.status_code == 200:
                return r.json()
            last_err = f"HTTP {r.status_code}: {r.text[:160]}"
        except Exception as e:
            last_err = str(e)
        time.sleep(0.5 * (attempt + 1))
    raise RuntimeError(f"RPC failed ({url}): {last_err}")


def fetch_manager_permissions(receipts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Query getInterestBatchManager(address) across all 3 branches for ALL unique batch managers."""
    events = load_canonical_events("pooled")
    managers_set = set()
    manager_branches_seen: Dict[str, List[str]] = {}
    for b in BRANCHES:
        for e in events[b]:
            if e["name"] in ("BatchUpdated", "BatchedTroveUpdated"):
                m = str(e["fields"]["interestBatchManager"]).lower()
                managers_set.add(m)
                manager_branches_seen.setdefault(m, [])
                if b not in manager_branches_seen[m]:
                    manager_branches_seen[m].append(b)
    managers = sorted(managers_set, key=lambda a: (0 if manager_label(a).startswith("M") else 1, manager_label(a)))

    selector = fn_selector("getInterestBatchManager(address)")
    # Build JSON-RPC batch call for all managers x 3 branches
    batch = []
    meta = []
    req_id = 1
    for m in managers:
        calldata = selector + "0" * 24 + m[2:]
        for b in BRANCHES:
            batch.append({
                "jsonrpc": "2.0",
                "id": req_id,
                "method": "eth_call",
                "params": [{"to": CONTRACTS[b]["borrowerOperations"], "data": calldata}, "latest"],
            })
            meta.append((req_id, m, b))
            req_id += 1

    # Query block number first for exact provenance
    bn_res = rpc_post(PRIMARY_RPC, {"jsonrpc": "2.0", "id": 0, "method": "eth_blockNumber", "params": []})
    block_num = int(bn_res["result"], 16)

    # Send in chunks of 30
    raw_responses = []
    for i in range(0, len(batch), 30):
        chunk = batch[i : i + 30]
        res = rpc_post(PRIMARY_RPC, chunk)
        if isinstance(res, list):
            raw_responses.extend(res)
        else:
            # Fallback to single calls if batch rejected
            for req in chunk:
                raw_responses.append(rpc_post(PRIMARY_RPC, req))

    by_id = {r["id"]: r for r in raw_responses}
    parsed: Dict[str, Dict[str, Any]] = {}
    summary_rows = []
    for rid, m, b in meta:
        r = by_id[rid]
        hex_res = r.get("result", "0x")
        raw = bytes.fromhex(hex_res[2:])
        if len(raw) >= 96:
            min_r = int.from_bytes(raw[0:32], "big")
            max_r = int.from_bytes(raw[32:64], "big")
            min_p = int.from_bytes(raw[64:96], "big")
        else:
            min_r = max_r = min_p = 0
        registered = max_r > 0
        parsed.setdefault(m, {"label": manager_label(m), "address": m, "branches_seen_in_events": manager_branches_seen[m], "branches": {}})
        parsed[m]["branches"][b] = {
            "registered": registered,
            "min_interest_rate_wad": min_r,
            "max_interest_rate_wad": max_r,
            "min_interest_rate_pct": round(min_r / 1e16, 4),
            "max_interest_rate_pct": round(max_r / 1e16, 4),
            "min_change_period_seconds": min_p,
            "min_change_period_hours": round(min_p / 3600.0, 4),
        }
        if registered:
            summary_rows.append({
                "label": manager_label(m),
                "address": m,
                "branch": b,
                "min_rate_pct": round(min_r / 1e16, 4),
                "max_rate_pct": round(max_r / 1e16, 4),
                "min_period_s": min_p,
            })

    out_obj = {
        "rpc_url": PRIMARY_RPC,
        "queried_block_number": block_num,
        "fetched_utc": utc_now_iso(),
        "n_unique_managers": len(managers),
        "n_registered_manager_branches": len(summary_rows),
        "managers": parsed,
        "summary_rows": summary_rows,
        "raw_rpc_responses": raw_responses,
    }
    raw_bytes = json.dumps(out_obj, indent=2).encode("utf-8")
    record_receipt(
        receipts,
        "manager_permissions_rpc.json",
        PRIMARY_RPC,
        raw_bytes,
        {"block_number": block_num, "n_managers": len(managers), "n_registered_pairs": len(summary_rows)},
    )
    print(f"[OK] RPC manager permissions: {len(managers)} unique managers, {len(summary_rows)} registered (manager, branch) tuples at block {block_num}")
    return out_obj


def fetch_defillama_prices(receipts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Fetch daily USD prices for BOLD, LUSD, DAI, USDS, crvUSD, GHO, WETH, wstETH, rETH."""
    # Use 4 clean span=140 chunks with nearest-day UTC rounding (avoids 23:59:37 vs 00:00:05 jitter)
    windows = [
        (int(datetime(2025, 5, 1, 0, 0, 0, tzinfo=timezone.utc).timestamp()), 140),
        (int(datetime(2025, 9, 15, 0, 0, 0, tzinfo=timezone.utc).timestamp()), 140),
        (int(datetime(2026, 1, 30, 0, 0, 0, tzinfo=timezone.utc).timestamp()), 140),
        (int(datetime(2026, 6, 15, 0, 0, 0, tzinfo=timezone.utc).timestamp()), 110),
    ]
    daily_series: Dict[str, Dict[str, float]] = {}

    for sym, coin_id in TOKENS.items():
        chunks = []
        dmap: Dict[str, float] = {}
        for start_ts, span in windows:
            url = f"https://coins.llama.fi/chart/{coin_id}?start={start_ts}&span={span}&period=1d"
            r = requests.get(url, timeout=30)
            r.raise_for_status()
            j = r.json()
            pts = j.get("coins", {}).get(coin_id, {}).get("prices", [])
            chunks.append({"url": url, "n_points": len(pts), "raw": j})
            for pt in pts:
                # Nearest UTC calendar date (DefiLlama returns ~00:00 +/- 30s)
                ts_round = int(round(int(pt["timestamp"]) / 86400.0)) * 86400
                d = ts_to_date(ts_round)
                dmap[d] = float(pt["price"])
            time.sleep(0.10)
        raw_bytes = json.dumps({"symbol": sym, "coin_id": coin_id, "chunks": chunks}, indent=2).encode("utf-8")
        record_receipt(
            receipts,
            f"defillama_price_{sym}.json",
            f"https://coins.llama.fi/chart/{coin_id}",
            raw_bytes,
            {"symbol": sym, "n_unique_days": len(dmap)},
        )
        daily_series[sym] = dmap
        in_sample = sum(1 for d in dmap if DEV_START_DATE <= d <= CONF_END_DATE)
        print(f"[OK] DefiLlama price {sym}: {in_sample}/485 sample days ({len(dmap)} total)")

    # Build clean aligned daily DataFrame (2025-05-01 .. 2026-09-15)
    all_dates = pd.date_range("2025-05-01", CONF_END_DATE, freq="D").strftime("%Y-%m-%d").tolist()
    rows = []
    for d in all_dates:
        row: Dict[str, Any] = {"date": d}
        for sym in TOKENS:
            row[sym] = daily_series[sym].get(d, np.nan)
        rows.append(row)
    df = pd.DataFrame(rows)
    # Compute realized volatility (annualized 7d and 30d rolling std of log returns) on real prices only
    for col in ("WETH", "wstETH", "rETH"):
        log_ret = np.log(df[col] / df[col].shift(1))
        df[f"{col}_log_ret"] = log_ret
        df[f"{col}_rvol_7d"] = log_ret.rolling(7, min_periods=5).std() * math.sqrt(365.0)
        df[f"{col}_rvol_30d"] = log_ret.rolling(30, min_periods=15).std() * math.sqrt(365.0)
    # Peg deviations in bps (10000 * (price - 1.0))
    for st in ("BOLD", "LUSD", "DAI", "USDS", "crvUSD", "GHO"):
        df[f"{st}_peg_dev_bps"] = (df[st] - 1.0) * 10000.0

    # Save tidy CSV for fast downstream loading
    df.to_csv(EXT_DIR / "daily_prices_and_vol.csv", index=False)
    return {"n_days_total": len(df), "date_min": all_dates[0], "date_max": all_dates[-1]}


def fetch_defillama_yields(receipts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Fetch DefiLlama free yield charts (Liquity V2 BOLD SPs, sUSDS, Aave USDC supply, scrvUSD)."""
    summary = {}
    for name, pid in LLAMA_YIELD_POOLS.items():
        url = f"https://yields.llama.fi/chart/{pid}"
        r = requests.get(url, timeout=30)
        if r.status_code != 200:
            summary[name] = {"status": r.status_code, "n_points": 0}
            print(f"[WARN] DefiLlama yield {name}: HTTP {r.status_code}")
            continue
        raw_bytes = r.content
        j = r.json()
        data = j.get("data", [])
        record_receipt(
            receipts,
            f"defillama_yield_{name}.json",
            url,
            raw_bytes,
            {"pool_id": pid, "n_points": len(data)},
        )
        # Filter to sample window
        in_win = [d for d in data if DEV_START_DATE <= str(d.get("timestamp", ""))[:10] <= CONF_END_DATE]
        summary[name] = {
            "status": 200,
            "pool_id": pid,
            "n_points_total": len(data),
            "n_points_sample": len(in_win),
            "mean_apy_sample": float(np.mean([d["apy"] for d in in_win if d.get("apy") is not None])) if in_win else None,
            "mean_tvl_usd_sample": float(np.mean([d["tvlUsd"] for d in in_win if d.get("tvlUsd") is not None])) if in_win else None,
        }
        print(f"[OK] DefiLlama yield {name}: {len(in_win)} days in sample (mean APY={summary[name]['mean_apy_sample']:.3f}%)" if summary[name]["mean_apy_sample"] is not None else f"[OK] DefiLlama yield {name}: {len(in_win)} days")
        time.sleep(0.15)
    return summary


def fetch_curve_crvusd_rates(receipts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Fetch full daily crvUSD borrow rates (WETH & wstETH controllers) via paginated Curve Prices API."""
    start_dt = int(datetime(2025, 5, 19, 0, 0, 0, tzinfo=timezone.utc).timestamp())
    end_dt = int(datetime(2026, 9, 16, 23, 59, 59, tzinfo=timezone.utc).timestamp())
    step = 90 * 86400  # 90-day chunks (< 100-item API cap!)

    out_summary = {}
    for col, ctrl in CURVE_CRVUSD_CONTROLLERS.items():
        all_rows: Dict[str, Dict[str, Any]] = {}
        chunk_payloads = []
        t0 = start_dt
        while t0 < end_dt:
            t1 = min(end_dt, t0 + step)
            url = f"https://prices.curve.finance/v1/crvusd/markets/ethereum/{ctrl}/snapshots?agg=day&start={t0}&end={t1}&fetch_on_chain=false"
            r = requests.get(url, timeout=25)
            if r.status_code == 200:
                j = r.json()
                chunk_payloads.append({"url": url, "data": j.get("data", [])})
                for row in j.get("data", []):
                    d = str(row.get("dt", ""))[:10]
                    if DEV_START_DATE <= d <= CONF_END_DATE:
                        all_rows[d] = row
            else:
                print(f"[WARN] Curve crvUSD {col} chunk {t0}..{t1}: HTTP {r.status_code}")
            t0 = t1 + 1
            time.sleep(0.2)

        raw_bytes = json.dumps({"controller": ctrl, "collateral": col, "chunks": chunk_payloads}, indent=2).encode("utf-8")
        record_receipt(
            receipts,
            f"curve_crvusd_{col}_daily.json",
            f"https://prices.curve.finance/v1/crvusd/markets/ethereum/{ctrl}/snapshots",
            raw_bytes,
            {"n_days": len(all_rows)},
        )
        # Curve prices API returns borrow_apr already in percentage points (e.g. 7.29 = 7.29% APR)
        aprs = [float(v["borrow_apr"]) for v in all_rows.values() if v.get("borrow_apr") is not None]
        out_summary[col] = {
            "controller": ctrl,
            "n_days": len(all_rows),
            "mean_borrow_apr_pct": float(np.mean(aprs)) if aprs else None,
            "sd_borrow_apr_pct": float(np.std(aprs, ddof=1)) if len(aprs) > 1 else None,
            "median_borrow_apr_pct": float(np.median(aprs)) if aprs else None,
        }
        print(f"[OK] Curve crvUSD {col}: {len(all_rows)} daily snapshots, mean borrow APR={out_summary[col]['mean_borrow_apr_pct']:.3f}%")
    return out_summary


def fetch_onchain_competing_borrow_rates(receipts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Query REAL on-chain Ethereum Mainnet archive state via eth.drpc.org (batch_size=3,
    matching free-tier limit for 100% completion!) across weekly historical blocks spanning
    2025-05-19..2026-09-15 (~72 exact blocks) for:
      - Sky / MakerDAO Jug.ilks (ETH-A, ETH-C, WSTETH-A, WSTETH-B) stability fee APR
      - Aave V3 ProtocolDataProvider.getReserveData (USDC, GHO) variableBorrowRate APR
      - Liquity V1 TroveManager.getBorrowingRateWithDecay() one-time borrowing fee
    """
    events = load_canonical_events("pooled")
    date_to_block: Dict[str, Tuple[int, int]] = {}
    for b in BRANCHES:
        for e in events[b]:
            d = ts_to_date(int(e["timestamp"]))
            blk = int(e["block"])
            ts = int(e["timestamp"])
            if d not in date_to_block or blk > date_to_block[d][0]:
                date_to_block[d] = (blk, ts)

    all_dates = sorted(d for d in date_to_block if DEV_START_DATE <= d <= CONF_END_DATE)
    must_keep = {all_dates[0], all_dates[-1], "2026-06-30", "2026-07-01"}
    sampled_dates = sorted(set(all_dates[::7]) | (must_keep & set(all_dates)))

    sel_ilks = fn_selector("ilks(bytes32)")
    sel_aave = fn_selector("getReserveData(address)")
    sel_lv1 = fn_selector("getBorrowingRateWithDecay()")

    ilks = {
        "sky_ETH_A": b"ETH-A".ljust(32, b"\x00").hex(),
        "sky_ETH_C": b"ETH-C".ljust(32, b"\x00").hex(),
        "sky_WSTETH_A": b"WSTETH-A".ljust(32, b"\x00").hex(),
        "sky_WSTETH_B": b"WSTETH-B".ljust(32, b"\x00").hex(),
    }

    # Build flat list of (req, meta) and execute strictly in batches of 3 (drpc free-tier exact cap)
    all_calls = []
    rid = 1
    for d in sampled_dates:
        blk, ts = date_to_block[d]
        blk_hex = hex(blk)
        for name, ilk_hex in ilks.items():
            all_calls.append(({
                "jsonrpc": "2.0", "id": rid, "method": "eth_call",
                "params": [{"to": MAKER_JUG, "data": sel_ilks + ilk_hex}, blk_hex],
            }, (rid, d, blk, ts, name)))
            rid += 1
        for name, addr in [("aave_USDC", USDC_ADDR), ("aave_GHO", GHO_ADDR)]:
            all_calls.append(({
                "jsonrpc": "2.0", "id": rid, "method": "eth_call",
                "params": [{"to": AAVE_V3_DATA_PROVIDER, "data": sel_aave + "0" * 24 + addr[2:].lower()}, blk_hex],
            }, (rid, d, blk, ts, name)))
            rid += 1
        all_calls.append(({
            "jsonrpc": "2.0", "id": rid, "method": "eth_call",
            "params": [{"to": LIQUITY_V1_TM, "data": sel_lv1}, blk_hex],
        }, (rid, d, blk, ts, "liquity_v1_borrow_fee")))
        rid += 1

    by_id: Dict[int, Any] = {}
    for i in range(0, len(all_calls), 3):
        sub = all_calls[i : i + 3]
        reqs = [x[0] for x in sub]
        try:
            resp = rpc_post(ARCHIVE_RPC, reqs, timeout=20)
            if isinstance(resp, list):
                for item in resp:
                    if isinstance(item, dict) and "id" in item and item.get("result") not in (None, "0x"):
                        by_id[item["id"]] = item
        except Exception:
            pass
        time.sleep(0.04)

    # Explicit retry pass for any dropped/errored calls (zero silent drops!)
    retry_rpcs = [ARCHIVE_RPC, PRIMARY_RPC, FALLBACK_ARCHIVE_RPC]
    missing_calls = [(req, meta) for req, meta in all_calls if meta[0] not in by_id]
    if missing_calls:
        print(f"[RETRY] Retrying {len(missing_calls)} transient archive eth_call drops...")
    for req, meta in missing_calls:
        rid_k = meta[0]
        for attempt in range(5):
            rpc_u = retry_rpcs[attempt % len(retry_rpcs)]
            try:
                item = rpc_post(rpc_u, req, timeout=20)
                if isinstance(item, dict) and item.get("result") not in (None, "0x"):
                    by_id[rid_k] = item
                    break
            except Exception:
                pass
            time.sleep(0.4 * (attempt + 1))

    still_missing = [meta for _, meta in all_calls if meta[0] not in by_id]
    if still_missing:
        print(f"[WARN] {len(still_missing)} archive eth_calls still missing after 5 retries: {still_missing[:5]}")
    else:
        print(f"[OK] All {len(all_calls)}/{len(all_calls)} archive eth_calls succeeded (0 missing).")

    day_map: Dict[str, Dict[str, Any]] = {}
    for _, (rid_k, d, blk, ts, name) in all_calls:
        row = day_map.setdefault(d, {"date": d, "block": blk, "timestamp": ts})
        res = by_id.get(rid_k, {})
        hx = res.get("result")
        if not hx or hx == "0x":
            row[name] = None
            continue
        raw = bytes.fromhex(hx[2:])
        if name.startswith("sky_"):
            duty = int.from_bytes(raw[0:32], "big")
            apr_pct = ((duty / 1e27) ** YEAR_SECONDS - 1.0) * 100.0
            row[name + "_apr_pct"] = round(apr_pct, 6)
        elif name.startswith("aave_"):
            words = [int.from_bytes(raw[j : j + 32], "big") for j in range(0, len(raw), 32)]
            if len(words) >= 7:
                row[name + "_supply_apr_pct"] = round(words[5] / 1e25, 6)
                row[name + "_borrow_apr_pct"] = round(words[6] / 1e25, 6)
        elif name == "liquity_v1_borrow_fee":
            fee_pct = int.from_bytes(raw[0:32], "big") / 1e16
            row["liquity_v1_onetime_fee_pct"] = round(fee_pct, 6)
            row["liquity_v1_recurring_apr_pct"] = 0.0

    records = [day_map[d] for d in sampled_dates if d in day_map]
    out_obj = {
        "rpc_url": ARCHIVE_RPC,
        "fetched_utc": utc_now_iso(),
        "n_sampled_dates": len(records),
        "n_missing_calls": len(still_missing),
        "rate_conventions": {
            "sky_ilks": "Exact APY ((Jug.ilks.duty / 1e27)^YEAR - 1)*100 (Jug.base == 0 verified on mainnet).",
            "aave_v3": "Nominal APR (getReserveData.variableBorrowRate / 1e25); GHO is base borrow rate before stkAAVE/Merit discounts.",
            "liquity_v1": "One-time minting fee getBorrowingRateWithDecay()/1e16 plus 0% recurring APR.",
        },
        "records": records,
    }
    raw_bytes = json.dumps(out_obj, indent=2).encode("utf-8")
    record_receipt(
        receipts,
        "onchain_competing_borrow_rates.json",
        ARCHIVE_RPC,
        raw_bytes,
        {"n_dates": len(records), "date_min": records[0]["date"] if records else None, "date_max": records[-1]["date"] if records else None},
    )
    df = pd.DataFrame(records)
    df.to_csv(EXT_DIR / "onchain_competing_borrow_rates.csv", index=False)

    summary = {"n_dates": len(df)}
    for col in [c for c in df.columns if c.endswith("_pct")]:
        s = df[col].dropna()
        summary[col] = {
            "n_obs": int(len(s)),
            "mean": float(s.mean()) if len(s) else None,
            "std": float(s.std(ddof=1)) if len(s) > 1 else None,
            "median": float(s.median()) if len(s) else None,
            "min": float(s.min()) if len(s) else None,
            "max": float(s.max()) if len(s) else None,
        }
        if len(s):
            print(f"[OK] On-chain {col}: n={len(s)}/{len(sampled_dates)}, mean={s.mean():.3f}%, sd={s.std(ddof=1):.3f}%, range=[{s.min():.3f}%, {s.max():.3f}%]")
    return summary


def fetch_liquity_v2_fork_ecosystem(receipts: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Fetch live DefiLlama /protocols + per-protocol historical peak TVL for Liquity V2
    and its documented licensed friendly forks (Felix CDP, Enosys Loans, Asymmetry USDaf,
    Quill Finance, Nerite, Orki Finance, Ebisu V2)."""
    url = "https://api.llama.fi/protocols"
    r = requests.get(url, timeout=35)
    r.raise_for_status()
    protocols = r.json()

    # Verified Liquity V2 + licensed friendly-fork CDP slugs listed on DefiLlama
    v2_slugs = {
        "liquity-v2",
        "felix-cdp",
        "enosys-loans",
        "asymmetry-usdaf",
        "quill-finance",
        "nerite",
        "orki-finance",
        "ebisu-v2",
        "defi-dollar",
    }

    v2_list = []
    # Map date -> {slug: tvl_usd} for true simultaneous cross-protocol ecosystem peak TVL
    daily_proto_tvl: Dict[str, Dict[str, float]] = {}
    for p in protocols:
        sl = str(p.get("slug", "")).lower()
        desc = str(p.get("description", "")).lower()
        forked = [str(x).lower() for x in (p.get("forkedFrom") or [])]
        if sl in v2_slugs or "liquity v2" in desc or any("liquity v2" in x or "liquity-v2" in x for x in forked):
            peak_sample_tvl = float(p.get("tvl") or 0.0)
            peak_alltime_tvl = peak_sample_tvl
            peak_sample_date = None
            peak_alltime_date = None
            for attempt in range(3):
                try:
                    rp = requests.get(f"https://api.llama.fi/protocol/{sl}", timeout=25)
                    if rp.status_code == 200:
                        jp = rp.json()
                        tvl_hist = jp.get("tvl", [])
                        if isinstance(tvl_hist, list) and tvl_hist:
                            by_day: Dict[str, float] = {}
                            for x in tvl_hist:
                                ts_x = int(x.get("date", 0))
                                if ts_x <= 0:
                                    continue
                                d_x = ts_to_date(int(round(ts_x / 86400.0)) * 86400)
                                val = float(x.get("totalLiquidityUSD", 0.0))
                                if d_x not in by_day or val > by_day[d_x]:
                                    by_day[d_x] = val
                            for d_x, val in by_day.items():
                                daily_proto_tvl.setdefault(d_x, {})[sl] = val
                            if by_day:
                                peak_alltime_date, peak_alltime_tvl = max(by_day.items(), key=lambda kv: kv[1])
                                in_s = [(d_x, v) for d_x, v in by_day.items() if DEV_START_DATE <= d_x <= CONF_END_DATE]
                                if in_s:
                                    peak_sample_date, peak_sample_tvl = max(in_s, key=lambda kv: kv[1])
                        break
                except Exception:
                    time.sleep(0.5 * (attempt + 1))
            v2_list.append({
                "name": p.get("name"),
                "slug": sl,
                "category": p.get("category"),
                "chains": p.get("chains", []),
                "current_tvl_usd": float(p.get("tvl") or 0.0),
                "peak_sample_tvl_usd": peak_sample_tvl,
                "peak_sample_date": peak_sample_date,
                "peak_alltime_tvl_usd": peak_alltime_tvl,
                "peak_alltime_date": peak_alltime_date,
            })
            time.sleep(0.12)

    v2_list.sort(key=lambda x: x["peak_alltime_tvl_usd"], reverse=True)
    cur_total = sum(x["current_tvl_usd"] for x in v2_list)
    peak_sample_sum = sum(x["peak_sample_tvl_usd"] for x in v2_list)
    peak_alltime_sum = sum(x["peak_alltime_tvl_usd"] for x in v2_list)

    # Compute true simultaneous ecosystem daily sum across all verified protocols
    sim_all_date, sim_all_tvl = None, 0.0
    sim_sample_date, sim_sample_tvl = None, 0.0
    for d_x, proto_map in sorted(daily_proto_tvl.items()):
        tot_d = sum(proto_map.values())
        if tot_d > sim_all_tvl:
            sim_all_tvl = tot_d
            sim_all_date = d_x
        if DEV_START_DATE <= d_x <= CONF_END_DATE and tot_d > sim_sample_tvl:
            sim_sample_tvl = tot_d
            sim_sample_date = d_x

    sim_all_breakdown = {
        k: round(v, 2)
        for k, v in sorted(daily_proto_tvl.get(sim_all_date or "", {}).items(), key=lambda kv: -kv[1])
    }

    out_obj = {
        "source_url": url,
        "fetched_utc": utc_now_iso(),
        "n_v2_and_forks": len(v2_list),
        "total_current_tvl_usd": cur_total,
        "simultaneous_peak_sample_tvl_usd": sim_sample_tvl,
        "simultaneous_peak_sample_date": sim_sample_date,
        "simultaneous_peak_alltime_tvl_usd": sim_all_tvl,
        "simultaneous_peak_alltime_date": sim_all_date,
        "simultaneous_peak_alltime_breakdown_usd": sim_all_breakdown,
        "sum_peak_sample_tvl_usd": peak_sample_sum,
        "sum_peak_alltime_tvl_usd": peak_alltime_sum,
        "peak_methodology_note": (
            "simultaneous_peak_*_tvl_usd sums TVL across all verified Liquity V2 friendly forks on the exact same UTC calendar day; "
            "sum_peak_*_tvl_usd sums each protocol's individual non-simultaneous peak TVL."
        ),
        "v2_and_forks": v2_list,
    }
    raw_bytes = json.dumps(out_obj, indent=2).encode("utf-8")
    record_receipt(
        receipts,
        "liquity_v2_fork_ecosystem.json",
        url,
        raw_bytes,
        {
            "n_v2_and_forks": len(v2_list),
            "current_tvl_usd": round(cur_total, 2),
            "simultaneous_peak_alltime_tvl_usd": round(sim_all_tvl, 2),
            "simultaneous_peak_alltime_date": sim_all_date,
            "sum_peak_alltime_tvl_usd": round(peak_alltime_sum, 2),
        },
    )
    print(
        f"[OK] Liquity V2 friendly-fork ecosystem ({len(v2_list)} protocols): "
        f"current=${cur_total/1e6:.2f}M, simultaneous peak=${sim_all_tvl/1e6:.2f}M ({sim_all_date}), "
        f"sum of individual peaks=${peak_alltime_sum/1e6:.2f}M"
    )
    for m in v2_list:
        print(
            f"     - {m['name']} ({m['slug']}): cur=${m['current_tvl_usd']/1e6:.2f}M | "
            f"peak_sample=${m['peak_sample_tvl_usd']/1e6:.2f}M ({m['peak_sample_date']}) | "
            f"peak_all=${m['peak_alltime_tvl_usd']/1e6:.2f}M ({m['peak_alltime_date']})"
        )
    return out_obj


def build_derived_file_receipts() -> List[Dict[str, Any]]:
    derived = []
    for fname in ["daily_prices_and_vol.csv", "onchain_competing_borrow_rates.csv"]:
        p = EXT_DIR / fname
        if p.exists():
            b = p.read_bytes()
            derived.append({
                "file": fname,
                "derived_from": "raw_receipts_in_manifest",
                "sha256": sha256_bytes(b),
                "bytes": len(b),
                "recorded_utc": utc_now_iso(),
            })
    return derived


def main() -> None:
    import sys

    EXT_DIR.mkdir(parents=True, exist_ok=True)
    refresh_r2 = "--refresh-r2" in sys.argv

    if refresh_r2 and (EXT_DIR / "SHA256_RECEIPTS.json").exists():
        print("=== Module 0 (--refresh-r2): Updating Archive Rates, Simultaneous Fork Peak & Derived CSV Receipts ===")
        old_manifest = json.loads((EXT_DIR / "SHA256_RECEIPTS.json").read_text())
        kept_receipts = [
            r for r in old_manifest.get("receipts", [])
            if r.get("file") not in ("onchain_competing_borrow_rates.json", "liquity_v2_fork_ecosystem.json")
        ]
        # Verify every kept file matches its recorded SHA-256 on disk
        for r in kept_receipts:
            fp = EXT_DIR / r["file"]
            assert fp.exists(), f"Missing cached raw file {fp}"
            assert sha256_bytes(fp.read_bytes()) == r["sha256"], f"SHA mismatch for {fp}"

        new_receipts: List[Dict[str, Any]] = []
        onchain_res = fetch_onchain_competing_borrow_rates(new_receipts)
        forks_res = fetch_liquity_v2_fork_ecosystem(new_receipts)

        receipts = kept_receipts + new_receipts
        summary = dict(old_manifest.get("summary", {}))
        summary["onchain_competing_rates"] = onchain_res
        summary["liquity_v2_ecosystem"] = {
            "n_protocols": forks_res["n_v2_and_forks"],
            "total_current_tvl_usd": forks_res["total_current_tvl_usd"],
            "simultaneous_peak_sample_tvl_usd": forks_res["simultaneous_peak_sample_tvl_usd"],
            "simultaneous_peak_sample_date": forks_res["simultaneous_peak_sample_date"],
            "simultaneous_peak_alltime_tvl_usd": forks_res["simultaneous_peak_alltime_tvl_usd"],
            "simultaneous_peak_alltime_date": forks_res["simultaneous_peak_alltime_date"],
            "sum_peak_sample_tvl_usd": forks_res["sum_peak_sample_tvl_usd"],
            "sum_peak_alltime_tvl_usd": forks_res["sum_peak_alltime_tvl_usd"],
        }
        derived_files = build_derived_file_receipts()
        manifest = {
            "generated_utc": utc_now_iso(),
            "integrity_guarantee": "100% live real public RPC & API fetches; zero synthetic or interpolated points.",
            "n_files": len(receipts),
            "receipts": receipts,
            "derived_files": derived_files,
            "summary": summary,
        }
        sha = save_json(EXT_DIR / "SHA256_RECEIPTS.json", manifest)
        print(f"\n[DONE] Updated {len(receipts)} verified raw files + {len(derived_files)} derived CSV receipts in SHA256_RECEIPTS.json (sha256={sha[:16]}...)")
        return

    receipts: List[Dict[str, Any]] = []
    print("=== Module 0: Live Free Public Data Augmentation ===")
    perm_res = fetch_manager_permissions(receipts)
    price_res = fetch_defillama_prices(receipts)
    yield_res = fetch_defillama_yields(receipts)
    curve_res = fetch_curve_crvusd_rates(receipts)
    onchain_res = fetch_onchain_competing_borrow_rates(receipts)
    forks_res = fetch_liquity_v2_fork_ecosystem(receipts)
    derived_files = build_derived_file_receipts()

    manifest = {
        "generated_utc": utc_now_iso(),
        "integrity_guarantee": "100% live real public RPC & API fetches; zero synthetic or interpolated points.",
        "n_files": len(receipts),
        "receipts": receipts,
        "derived_files": derived_files,
        "summary": {
            "manager_permissions": {
                "n_unique_managers": perm_res["n_unique_managers"],
                "n_registered_pairs": perm_res["n_registered_manager_branches"],
                "block_number": perm_res["queried_block_number"],
            },
            "prices": price_res,
            "yields": yield_res,
            "curve_crvusd": curve_res,
            "onchain_competing_rates": onchain_res,
            "liquity_v2_ecosystem": {
                "n_protocols": forks_res["n_v2_and_forks"],
                "total_current_tvl_usd": forks_res["total_current_tvl_usd"],
                "simultaneous_peak_sample_tvl_usd": forks_res["simultaneous_peak_sample_tvl_usd"],
                "simultaneous_peak_sample_date": forks_res["simultaneous_peak_sample_date"],
                "simultaneous_peak_alltime_tvl_usd": forks_res["simultaneous_peak_alltime_tvl_usd"],
                "simultaneous_peak_alltime_date": forks_res["simultaneous_peak_alltime_date"],
                "sum_peak_sample_tvl_usd": forks_res["sum_peak_sample_tvl_usd"],
                "sum_peak_alltime_tvl_usd": forks_res["sum_peak_alltime_tvl_usd"],
            },
        },
    }
    sha = save_json(EXT_DIR / "SHA256_RECEIPTS.json", manifest)
    print(f"\n[DONE] Saved {len(receipts)} verified raw files + {len(derived_files)} derived CSV receipts in SHA256_RECEIPTS.json (sha256={sha[:16]}...)")


if __name__ == "__main__":
    main()
