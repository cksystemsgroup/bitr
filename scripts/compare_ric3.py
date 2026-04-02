#!/usr/bin/env python3
"""Compare bitr results against rIC3 (and other solvers) from HWMCC'24 reference CSV."""

import csv
import sys
from pathlib import Path


def load_bitr_results(path):
    """Load bitr results CSV (name,status,time_s)."""
    results = {}
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            results[row["name"]] = {
                "status": row["status"],
                "time_s": float(row["time_s"]),
            }
    return results


def load_hwmcc_results(path, solver="ric3"):
    """Load HWMCC'24 reference results for a specific solver."""
    results = {}
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["solver"] != solver:
                continue
            bench = row["benchmark"]
            # Extract name without path for matching
            name = Path(bench).stem
            result = row["result"]
            status = "timeout" if row["status"] == "to" else result
            time_s = float(row["time_real"])
            results[name] = {"status": status, "time_s": time_s, "path": bench}
            # Also store by full path for exact matching
            results[bench] = {"status": status, "time_s": time_s, "path": bench}
    return results


def compare(bitr_path, hwmcc_path, solver="ric3", timeout=300.0):
    bitr = load_bitr_results(bitr_path)
    ref = load_hwmcc_results(hwmcc_path, solver)

    # Match by stem name
    matched = 0
    bitr_solved = 0
    ref_solved = 0
    both_solved = 0
    bitr_only = 0
    ref_only = 0
    wrong = []
    bitr_faster = 0
    ref_faster = 0
    bitr_time_total = 0.0
    ref_time_total = 0.0

    for bname, bdata in bitr.items():
        rdata = ref.get(bname)
        if rdata is None:
            continue
        matched += 1

        b_solved = bdata["status"] in ("sat", "unsat")
        r_solved = rdata["status"] in ("sat", "unsat")

        if b_solved:
            bitr_solved += 1
            bitr_time_total += bdata["time_s"]
        if r_solved:
            ref_solved += 1
            ref_time_total += rdata["time_s"]

        if b_solved and r_solved:
            both_solved += 1
            if bdata["status"] != rdata["status"]:
                wrong.append((bname, bdata["status"], rdata["status"]))
            elif bdata["time_s"] < rdata["time_s"]:
                bitr_faster += 1
            else:
                ref_faster += 1
        elif b_solved and not r_solved:
            bitr_only += 1
        elif r_solved and not b_solved:
            ref_only += 1

    # PAR-2 scores
    bitr_par2 = sum(
        bitr[n]["time_s"] if bitr[n]["status"] in ("sat", "unsat") else 2 * timeout
        for n in bitr
        if n in ref
    )
    ref_par2 = sum(
        ref[n]["time_s"] if ref[n]["status"] in ("sat", "unsat") else 2 * timeout
        for n in bitr
        if n in ref
    )

    print(f"=== bitr vs {solver} ===")
    print(f"Benchmarks matched:  {matched}")
    print(f"bitr solved:         {bitr_solved}")
    print(f"{solver} solved:      {ref_solved}")
    print(f"Both solved:         {both_solved}")
    print(f"bitr-only:           {bitr_only}")
    print(f"{solver}-only:        {ref_only}")
    print(f"bitr faster:         {bitr_faster}")
    print(f"{solver} faster:      {ref_faster}")
    print(f"WRONG ANSWERS:       {len(wrong)}")
    if wrong:
        for w in wrong[:10]:
            print(f"  {w[0]}: bitr={w[1]} {solver}={w[2]}")
    print(f"bitr time (solved):  {bitr_time_total:.1f}s")
    print(f"{solver} time (solved): {ref_time_total:.1f}s")
    print(f"bitr PAR-2:          {bitr_par2:.1f}")
    print(f"{solver} PAR-2:       {ref_par2:.1f}")

    # Difficulty tier breakdown
    print(f"\n--- Difficulty tiers (by {solver} time) ---")
    tiers = {"fast (<1s)": [], "medium (1-60s)": [], "hard (60-300s)": [], "unsolved": []}
    for bname in bitr:
        rdata = ref.get(bname)
        if rdata is None:
            continue
        r_solved = rdata["status"] in ("sat", "unsat")
        if not r_solved:
            tiers["unsolved"].append(bname)
        elif rdata["time_s"] < 1:
            tiers["fast (<1s)"].append(bname)
        elif rdata["time_s"] < 60:
            tiers["medium (1-60s)"].append(bname)
        else:
            tiers["hard (60-300s)"].append(bname)

    for tier_name, names in tiers.items():
        total = len(names)
        b_solved = sum(1 for n in names if bitr[n]["status"] in ("sat", "unsat"))
        print(f"  {tier_name}: bitr {b_solved}/{total}")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <bitr.csv> <hwmcc24-results.csv> [solver]")
        print("  solver defaults to 'ric3'")
        sys.exit(1)
    solver = sys.argv[3] if len(sys.argv) > 3 else "ric3"
    compare(sys.argv[1], sys.argv[2], solver)
