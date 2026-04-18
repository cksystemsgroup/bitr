#!/usr/bin/env python3
"""Benchmark sweep with real wall-clock timeout enforcement.

Usage:
    python3 scripts/run_sweep.py --list /tmp/bv155.txt --out results/bv_phaseABC.csv \
        --timeout 60 --flags --legacy-bmc

The script resolves each benchmark name by basename against benchmarks/bv
(recursive), runs bitr under subprocess.run with a hard kill on timeout, and
writes a CSV compatible with results/bv_*.csv.
"""

import argparse
import csv
import os
import signal
import subprocess
import sys
import time
from pathlib import Path


def find_benchmark(root: Path, name: str) -> Path | None:
    """Locate a benchmark .btor2 by basename under `root`."""
    target = name + ".btor2"
    for candidate in root.rglob(target):
        return candidate
    return None


def run_one(bitr: Path, benchmark: Path, timeout: int, flags: list[str]) -> tuple[str, float]:
    """Run bitr on a benchmark with a hard wall-clock timeout.

    Returns (status, elapsed_seconds) where status is one of
    'sat', 'unsat', 'unknown', 'timeout', 'error'.
    """
    args = [str(bitr), *flags, "--timeout", str(timeout), str(benchmark)]
    start = time.monotonic()
    try:
        # Python's subprocess timeout sends SIGTERM; we give the solver a small
        # grace window then kill. Our --timeout is given to bitr too so it can
        # bail out gracefully first.
        proc = subprocess.run(
            args,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=timeout + 5,
            check=False,
            start_new_session=True,
        )
        elapsed = time.monotonic() - start
        last = proc.stdout.decode("utf-8", "replace").strip().splitlines()
        answer = last[-1].strip() if last else ""
        if answer == "sat":
            return "sat", elapsed
        if answer == "unsat":
            return "unsat", elapsed
        if answer == "unknown":
            return "unknown", elapsed
        return "error", elapsed
    except subprocess.TimeoutExpired:
        # Nuke the whole process group to catch any stray child processes.
        try:
            os.killpg(proc.pid, signal.SIGKILL)  # type: ignore[name-defined]
        except Exception:
            pass
        return "timeout", time.monotonic() - start


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True,
                    help="newline-separated benchmark basenames (without .btor2)")
    ap.add_argument("--out", required=True,
                    help="output CSV path (name,status,time_s)")
    ap.add_argument("--root", default="benchmarks/bv",
                    help="root directory to recursively search for benchmarks")
    ap.add_argument("--bitr", default="target/release/bitr",
                    help="path to the bitr binary")
    ap.add_argument("--timeout", type=int, default=60,
                    help="per-benchmark wall-clock budget in seconds")
    ap.add_argument("--flags", nargs=argparse.REMAINDER, default=[],
                    help="extra flags to pass to bitr (e.g. --legacy-bmc)")
    args = ap.parse_args()

    root = Path(args.root)
    bitr = Path(args.bitr)
    if not bitr.is_file():
        print(f"bitr binary not found at {bitr}", file=sys.stderr)
        return 2

    names = [ln.strip() for ln in Path(args.list).read_text().splitlines() if ln.strip()]
    print(f"sweep: {len(names)} benchmarks, timeout {args.timeout}s, flags {args.flags}",
          file=sys.stderr)

    results: list[tuple[str, str, float]] = []
    solved = 0
    sat_count = 0
    unsat_count = 0
    timeout_count = 0
    start_all = time.monotonic()

    for i, name in enumerate(names, 1):
        bench = find_benchmark(root, name)
        if bench is None:
            print(f"[{i}/{len(names)}] {name}: MISSING", file=sys.stderr)
            results.append((name, "missing", 0.0))
            continue

        status, elapsed = run_one(bitr, bench, args.timeout, args.flags)
        results.append((name, status, elapsed))
        if status == "sat":
            solved += 1
            sat_count += 1
        elif status == "unsat":
            solved += 1
            unsat_count += 1
        elif status == "timeout":
            timeout_count += 1

        print(f"[{i}/{len(names)}] {name[:50]:50s} {status:8s} {elapsed:6.1f}s "
              f"(solved {solved}, to {timeout_count})",
              file=sys.stderr)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["name", "status", "time_s"])
        for name, status, elapsed in results:
            w.writerow([name, status, f"{elapsed:.2f}"])

    total_elapsed = time.monotonic() - start_all
    print(f"\n=== sweep done in {total_elapsed:.0f}s ===", file=sys.stderr)
    print(f"solved: {solved}/{len(names)} "
          f"(sat={sat_count}, unsat={unsat_count}, timeout={timeout_count})",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
