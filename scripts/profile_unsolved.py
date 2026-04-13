#!/usr/bin/env python3
"""Profile unsolved HWMCC BV benchmarks to characterize bottlenecks.

Runs each benchmark with --verbose and parses stderr to extract:
- K-induction outcome (max k reached, result)
- BMC step reached and term growth
- Solver tier used per step
- Computed cache hit rate
- Term size at final step

Usage:
    python3 scripts/profile_unsolved.py [--timeout 30] [--only-timeout] [--jobs 1]

Output: results/profile_unsolved.csv
"""

import argparse
import csv
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BITR = ROOT / "target" / "release" / "bitr"


def find_bv_benchmarks():
    """Find all .btor2 files under benchmarks/bv/."""
    bv_dir = ROOT / "benchmarks" / "bv"
    if not bv_dir.exists():
        print(f"Error: {bv_dir} does not exist", file=sys.stderr)
        sys.exit(1)
    files = sorted(bv_dir.rglob("*.btor2"))
    return files


def load_previous_results():
    """Load previous results CSV to identify timeout benchmarks."""
    csv_path = ROOT / "results" / "bv.csv"
    if not csv_path.exists():
        return {}
    results = {}
    with open(csv_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            results[row["name"]] = row["status"]
    return results


def parse_verbose_output(stderr_text):
    """Parse bitr --verbose stderr output into structured metrics."""
    info = {
        "kind_max_k": -1,
        "kind_result": "none",
        "kind_base_results": [],
        "kind_ind_results": [],
        "bmc_max_step": -1,
        "bmc_final_tier": "none",
        "bmc_final_term_size": 0,
        "bmc_final_terms": 0,
        "bmc_cache_rate": 0.0,
        "bmc_cache_total": 0,
        "term_growth": [],  # (step, terms) pairs
        "num_states": 0,
        "num_nodes": 0,
        "coi_removed": 0,
    }

    for line in stderr_text.splitlines():
        # Parse model info
        m = re.search(r"(\d+) nodes \((\d+) removed by COI\)", line)
        if m:
            info["num_nodes"] = int(m.group(1))
            info["coi_removed"] = int(m.group(2))

        m = re.search(r"(\d+) states", line)
        if m:
            info["num_states"] = int(m.group(1))

        # K-induction lines
        m = re.match(r"bitr: k-induction k=(\d+) \(terms=(\d+)\)", line)
        if m:
            info["kind_max_k"] = int(m.group(1))

        m = re.match(r"bitr: k-ind base k=(\d+): (\w+) \(term_size=(\d+)\)", line)
        if m:
            info["kind_base_results"].append({
                "k": int(m.group(1)),
                "result": m.group(2),
                "term_size": int(m.group(3)),
            })

        m = re.match(r"bitr: inductive step k=(\d+): (\w+)", line)
        if m:
            info["kind_ind_results"].append({
                "k": int(m.group(1)),
                "result": m.group(2),
            })

        if "k-induction succeeded" in line:
            info["kind_result"] = "proved"
        elif "k-induction inconclusive" in line:
            info["kind_result"] = "inconclusive"
        elif "k-induction timeout" in line:
            info["kind_result"] = "timeout"

        # BMC lines
        m = re.match(r"bitr: BMC step (\d+) \(terms=(\d+), cache=([0-9.]+)% of (\d+)", line)
        if m:
            step = int(m.group(1))
            terms = int(m.group(2))
            cache_rate = float(m.group(3))
            cache_total = int(m.group(4))
            info["bmc_max_step"] = step
            info["bmc_final_terms"] = terms
            info["bmc_cache_rate"] = cache_rate
            info["bmc_cache_total"] = cache_total
            info["term_growth"].append((step, terms))

        m = re.match(r"bitr: step (\d+) bad\[\d+\] = (\w+) \(tier=(\w+), term_size=(\d+)", line)
        if m:
            info["bmc_final_tier"] = m.group(3)
            info["bmc_final_term_size"] = int(m.group(4))

        # Timeout
        if "wall-clock timeout" in line:
            info["kind_result"] = info.get("kind_result", "none")

    return info


def classify_benchmark(result, info):
    """Classify a benchmark into a category based on profiling data."""
    if result in ("sat", "unsat"):
        return "solved"

    if info["kind_result"] == "proved":
        return "solved_kind"

    # Check BMC progress first (term blowup takes priority)
    if info["bmc_max_step"] >= 0:
        terms = info["bmc_final_terms"]
        step = info["bmc_max_step"]
        if terms > 500_000:
            return "term_blowup"
        elif step >= 20:
            return "deep_bmc"
        elif step >= 0:
            return "shallow_bmc"

    # Check if k-induction was promising (base cases all UNSAT but induction failed)
    if info["kind_result"] == "inconclusive":
        kind_k = info["kind_max_k"]
        if kind_k >= 2 and all(r["result"] == "Unsat" for r in info["kind_base_results"]):
            return "kind_promising"

    if info["bmc_max_step"] == -1 and info["kind_max_k"] >= 0:
        return "kind_only"

    return "unknown"


def term_growth_rate(info):
    """Compute average term growth per step."""
    tg = info["term_growth"]
    if len(tg) < 2:
        return 0
    first_step, first_terms = tg[0]
    last_step, last_terms = tg[-1]
    steps = last_step - first_step
    if steps == 0:
        return 0
    return (last_terms - first_terms) / steps


def run_benchmark(btor2_path, timeout_s):
    """Run a single benchmark and return (stdout_result, parsed_info)."""
    try:
        proc = subprocess.Popen(
            [str(BITR), "--no-oracle", "--verbose", "--timeout", str(timeout_s),
             str(btor2_path)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        try:
            stdout, stderr = proc.communicate(timeout=timeout_s + 10)
        except subprocess.TimeoutExpired:
            proc.kill()
            stdout, stderr = proc.communicate()

        stdout = (stdout or "").strip()
        stderr = stderr or ""
        result = "unknown"
        if stdout.endswith("sat") and not stdout.endswith("unsat"):
            result = "sat"
        elif stdout.endswith("unsat"):
            result = "unsat"
        elif proc.returncode != 0 and not stdout:
            result = "timeout"
        info = parse_verbose_output(stderr)
        return result, info
    except Exception as e:
        print(f"  Error: {e}", file=sys.stderr)
        return "error", parse_verbose_output("")


def main():
    parser = argparse.ArgumentParser(description="Profile unsolved HWMCC BV benchmarks")
    parser.add_argument("--timeout", type=int, default=30, help="Timeout per benchmark (seconds)")
    parser.add_argument("--only-timeout", action="store_true",
                        help="Only profile benchmarks that timed out in previous run")
    parser.add_argument("--max", type=int, default=0, help="Max benchmarks to profile (0=all)")
    args = parser.parse_args()

    if not BITR.exists():
        print("Building bitr (release)...", file=sys.stderr)
        subprocess.run(["cargo", "build", "--release"], cwd=ROOT, check=True)

    benchmarks = find_bv_benchmarks()
    prev_results = load_previous_results()

    # Build name→path mapping
    name_to_path = {}
    for p in benchmarks:
        name = p.stem
        name_to_path[name] = p

    # Filter to timeout benchmarks if requested
    if args.only_timeout and prev_results:
        timeout_names = {n for n, s in prev_results.items() if s == "timeout"}
        benchmarks = [p for p in benchmarks if p.stem in timeout_names]
        print(f"Profiling {len(benchmarks)} timeout benchmarks (of {len(timeout_names)} in CSV)",
              file=sys.stderr)
    else:
        print(f"Profiling {len(benchmarks)} benchmarks", file=sys.stderr)

    if args.max > 0:
        benchmarks = benchmarks[:args.max]

    print(f"Timeout: {args.timeout}s per benchmark", file=sys.stderr)

    # Output CSV
    out_path = ROOT / "results" / "profile_unsolved.csv"
    os.makedirs(out_path.parent, exist_ok=True)

    fieldnames = [
        "name", "path", "result", "category",
        "num_nodes", "coi_removed", "num_states",
        "kind_max_k", "kind_result",
        "bmc_max_step", "bmc_final_terms", "bmc_final_term_size",
        "bmc_final_tier", "bmc_cache_rate", "bmc_cache_total",
        "term_growth_per_step",
    ]

    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()

        for i, bpath in enumerate(benchmarks):
            name = bpath.stem
            rel_path = bpath.relative_to(ROOT)
            print(f"\r  [{i+1}/{len(benchmarks)}] {name[:50]:50s}", end="", file=sys.stderr)

            result, info = run_benchmark(bpath, args.timeout)
            category = classify_benchmark(result, info)

            writer.writerow({
                "name": name,
                "path": str(rel_path),
                "result": result,
                "category": category,
                "num_nodes": info["num_nodes"],
                "coi_removed": info["coi_removed"],
                "num_states": info["num_states"],
                "kind_max_k": info["kind_max_k"],
                "kind_result": info["kind_result"],
                "bmc_max_step": info["bmc_max_step"],
                "bmc_final_terms": info["bmc_final_terms"],
                "bmc_final_term_size": info["bmc_final_term_size"],
                "bmc_final_tier": info["bmc_final_tier"],
                "bmc_cache_rate": f"{info['bmc_cache_rate']:.1f}",
                "bmc_cache_total": info["bmc_cache_total"],
                "term_growth_per_step": f"{term_growth_rate(info):.0f}",
            })
            f.flush()

    print(f"\n\nResults written to {out_path}", file=sys.stderr)

    # Print summary
    print("\n=== Profile Summary ===", file=sys.stderr)
    categories = {}
    with open(out_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            cat = row["category"]
            categories[cat] = categories.get(cat, 0) + 1

    for cat, count in sorted(categories.items(), key=lambda x: -x[1]):
        print(f"  {cat:20s}: {count}", file=sys.stderr)


if __name__ == "__main__":
    main()
