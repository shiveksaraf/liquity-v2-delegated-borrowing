#!/usr/bin/env python3
"""Run the complete offline Liquity V2 empirical replication pipeline and figure builder."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_receipts() -> None:
    in_manifest = json.loads((ROOT / "inputs" / "INPUT_SHA256.json").read_text(encoding="utf-8"))
    for entry in in_manifest["files"]:
        p = ROOT / "inputs" / entry["path"]
        got = sha256_file(p)
        if got != entry["sha256"]:
            raise RuntimeError(f"Canonical input hash mismatch for {entry['path']}: {got} != {entry['sha256']}")
    print(f"[OK] Verified {len(in_manifest['files'])} canonical mainnet input files")

    ext_manifest = json.loads((ROOT / "data_external" / "SHA256_RECEIPTS.json").read_text(encoding="utf-8"))
    items = ext_manifest.get("receipts", []) + ext_manifest.get("derived_files", [])
    for item in items:
        fname = item.get("file") or item.get("filename")
        p = ROOT / "data_external" / Path(fname).name
        got = sha256_file(p)
        if got != item["sha256"]:
            raise RuntimeError(f"External receipt hash mismatch for {fname}: {got} != {item['sha256']}")
    print(f"[OK] Verified {len(items)} archived external data receipts (20 raw + 2 derived)")


def main() -> None:
    verify_receipts()
    steps = [
        "notch_and_agency.py",
        "spike_and_cut.py",
        "causal_routing_did.py",
        "hawkes_leapfrogging.py",
        "gpv_structural_welfare.py",
        "build_master_ledger.py",
        "make_figures.py",
    ]
    for script in steps:
        print(f"\n>>> Running {script}")
        res = subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=False)
        if res.returncode != 0:
            raise SystemExit(res.returncode)
    print("\n[DONE] Offline empirical replication complete.")


if __name__ == "__main__":
    main()
