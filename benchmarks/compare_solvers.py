#!/usr/bin/env python3
"""Benchmark comparison: BITR vs bitwuzla (Python API) on BTOR2 problems.

For combinational BTOR2 problems, we translate them to bitwuzla QF_BV queries
and compare solving time and correctness.

For sequential (BMC) problems, we unroll the transition relation and solve
each step as a QF_BV query.
"""

import subprocess
import sys
import os
import time
import csv
import re

BITR_BIN = os.path.join(os.path.dirname(__file__), "..", "target", "release", "bitr")
TIMEOUT = 60  # seconds

def run_bitr(btor2_path, extra_args=None):
    """Run BITR on a BTOR2 file. Returns (result, time_s)."""
    args = [BITR_BIN, "--no-oracle", "--timeout", str(TIMEOUT)]
    if extra_args:
        args.extend(extra_args)
    args.append(btor2_path)
    start = time.monotonic()
    try:
        proc = subprocess.run(args, capture_output=True, text=True, timeout=TIMEOUT + 5)
        elapsed = time.monotonic() - start
        out = proc.stdout.strip().lower()
        if "sat" in out and "unsat" not in out:
            return ("sat", elapsed)
        elif "unsat" in out:
            return ("unsat", elapsed)
        else:
            return ("unknown", elapsed)
    except subprocess.TimeoutExpired:
        return ("timeout", TIMEOUT)
    except Exception as e:
        return (f"error:{e}", 0.0)


def solve_with_bitwuzla(btor2_path):
    """Translate BTOR2 to bitwuzla Python API calls and solve.

    Only handles combinational (no state/next) benchmarks.
    Returns (result, time_s).
    """
    try:
        import bitwuzla as bz_mod
        from bitwuzla import Bitwuzla, Kind, Option, Result
    except ImportError:
        return ("n/a", 0.0)

    with open(btor2_path) as f:
        lines = f.readlines()

    # Parse BTOR2 into a simple IR
    sorts = {}
    nodes = {}
    bads = []
    states = {}
    inits = {}
    nexts = {}
    inputs_list = []
    constraints = []
    is_sequential = False

    for line in lines:
        line = line.strip()
        if not line or line.startswith(';'):
            continue
        parts = line.split()
        if len(parts) < 2:
            continue

        nid = int(parts[0])
        op = parts[1]

        if op == "sort":
            if parts[2] == "bitvec":
                sorts[nid] = int(parts[3])
        elif op == "input":
            sid = int(parts[2])
            name = parts[3] if len(parts) > 3 else f"v{nid}"
            nodes[nid] = ("input", sid, name)
            inputs_list.append(nid)
        elif op == "state":
            sid = int(parts[2])
            name = parts[3] if len(parts) > 3 else f"s{nid}"
            nodes[nid] = ("state", sid, name)
            states[nid] = sid
            is_sequential = True
        elif op == "init":
            sid = int(parts[2])
            state_nid = int(parts[3])
            val_nid = int(parts[4])
            inits[state_nid] = val_nid
        elif op == "next":
            sid = int(parts[2])
            state_nid = int(parts[3])
            next_nid = int(parts[4])
            nexts[state_nid] = next_nid
        elif op == "bad":
            bads.append(int(parts[2]))
        elif op == "constraint":
            constraints.append(int(parts[2]))
        elif op in ("zero", "one", "ones"):
            sid = int(parts[2])
            nodes[nid] = (op, sid)
        elif op == "const":
            sid = int(parts[2])
            val = parts[3]
            nodes[nid] = ("const", sid, val)
        elif op == "constd":
            sid = int(parts[2])
            val = int(parts[3])
            nodes[nid] = ("constd", sid, val)
        elif op == "consth":
            sid = int(parts[2])
            val = int(parts[3], 16)
            nodes[nid] = ("constd", sid, val)
        elif op in ("slice",):
            sid = int(parts[2])
            arg = int(parts[3])
            upper = int(parts[4])
            lower = int(parts[5])
            nodes[nid] = (op, sid, arg, upper, lower)
        elif op in ("uext", "sext"):
            sid = int(parts[2])
            arg = int(parts[3])
            amount = int(parts[4]) if len(parts) > 4 else 0
            # If amount is 0, compute from sort widths
            if amount == 0 and sid in sorts and arg in nodes:
                # Infer extension amount from target sort width minus source sort width
                target_w = sorts[sid]
                src_node = nodes.get(arg)
                if src_node and src_node[1] in sorts:
                    src_w = sorts[src_node[1]]
                    amount = target_w - src_w
            nodes[nid] = (op, sid, arg, amount)
        elif op in ("not", "neg", "redand", "redor", "redxor"):
            sid = int(parts[2])
            arg = int(parts[3])
            nodes[nid] = (op, sid, arg)
        else:
            # Binary ops
            sid = int(parts[2])
            args = [int(x) for x in parts[3:]]
            nodes[nid] = (op, sid, *args)

    if not bads:
        return ("unsat", 0.0)

    def solve_combinational(max_steps=1):
        """Solve combinational or BMC problem."""
        start = time.monotonic()

        tm = bz_mod.TermManager()
        opts = bz_mod.Options()
        opts.set(Option.PRODUCE_MODELS, True)
        bz = Bitwuzla(tm, opts)

        bv_sorts = {}
        for sid, width in sorts.items():
            bv_sorts[sid] = tm.mk_bv_sort(width)

        def get_sort(sid):
            return bv_sorts[sid]

        # For BMC, we may need multiple copies of variables per step
        steps = max_steps if is_sequential else 1

        for step in range(steps):
            # Build terms for this step
            bz_nodes = {}  # (nid, step) -> bitwuzla term

            def get_term(nid, s=step):
                key = (nid, s)
                if key in bz_nodes:
                    return bz_nodes[key]

                if nid not in nodes:
                    return None

                node = nodes[nid]
                op = node[0]

                if op == "input":
                    sid = node[1]
                    name = f"{node[2]}_s{s}"
                    t = tm.mk_const(get_sort(sid), name)
                    bz_nodes[key] = t
                    return t
                elif op == "state":
                    if s == 0 and nid in inits:
                        t = get_term(inits[nid], 0)
                    elif s > 0 and nid in nexts:
                        t = get_term(nexts[nid], s - 1)
                    else:
                        # Unconstrained state
                        sid = node[1]
                        name = f"{node[2]}_s{s}"
                        t = tm.mk_const(get_sort(sid), name)
                    bz_nodes[key] = t
                    return t
                elif op == "zero":
                    w = sorts[node[1]]
                    t = tm.mk_bv_zero(get_sort(node[1]))
                    bz_nodes[key] = t
                    return t
                elif op == "one":
                    t = tm.mk_bv_one(get_sort(node[1]))
                    bz_nodes[key] = t
                    return t
                elif op == "ones":
                    t = tm.mk_bv_ones(get_sort(node[1]))
                    bz_nodes[key] = t
                    return t
                elif op == "const":
                    w = sorts[node[1]]
                    val_str = node[2]
                    t = tm.mk_bv_value(get_sort(node[1]), val_str, 2)
                    bz_nodes[key] = t
                    return t
                elif op == "constd":
                    w = sorts[node[1]]
                    val = node[2]
                    t = tm.mk_bv_value(get_sort(node[1]), str(val), 10)
                    bz_nodes[key] = t
                    return t
                elif op == "not":
                    a = get_term(node[2], s)
                    t = tm.mk_term(Kind.BV_NOT, [a])
                    bz_nodes[key] = t
                    return t
                elif op == "neg":
                    a = get_term(node[2], s)
                    t = tm.mk_term(Kind.BV_NEG, [a])
                    bz_nodes[key] = t
                    return t
                elif op == "redand":
                    a = get_term(node[2], s)
                    t = tm.mk_term(Kind.BV_REDAND, [a])
                    bz_nodes[key] = t
                    return t
                elif op == "redor":
                    a = get_term(node[2], s)
                    t = tm.mk_term(Kind.BV_REDOR, [a])
                    bz_nodes[key] = t
                    return t
                elif op == "slice":
                    a = get_term(node[2], s)
                    upper = node[3]
                    lower = node[4]
                    t = tm.mk_term(Kind.BV_EXTRACT, [a], [upper, lower])
                    bz_nodes[key] = t
                    return t
                elif op in ("uext",):
                    a = get_term(node[2], s)
                    amount = node[3]
                    t = tm.mk_term(Kind.BV_ZERO_EXTEND, [a], [amount])
                    bz_nodes[key] = t
                    return t
                elif op in ("sext",):
                    a = get_term(node[2], s)
                    amount = node[3]
                    t = tm.mk_term(Kind.BV_SIGN_EXTEND, [a], [amount])
                    bz_nodes[key] = t
                    return t
                else:
                    # Binary ops
                    op_map = {
                        "add": Kind.BV_ADD, "sub": Kind.BV_SUB,
                        "mul": Kind.BV_MUL, "udiv": Kind.BV_UDIV,
                        "urem": Kind.BV_UREM, "sdiv": Kind.BV_SDIV,
                        "srem": Kind.BV_SREM,
                        "and": Kind.BV_AND, "or": Kind.BV_OR,
                        "xor": Kind.BV_XOR, "nand": Kind.BV_NAND,
                        "nor": Kind.BV_NOR, "xnor": Kind.BV_XNOR,
                        "sll": Kind.BV_SHL, "srl": Kind.BV_SHR,
                        "sra": Kind.BV_ASHR,
                        "eq": Kind.EQUAL, "neq": Kind.DISTINCT,
                        "ult": Kind.BV_ULT, "ule": Kind.BV_ULE,
                        "ugt": Kind.BV_UGT, "uge": Kind.BV_UGE,
                        "slt": Kind.BV_SLT, "sle": Kind.BV_SLE,
                        "sgt": Kind.BV_SGT, "sge": Kind.BV_SGE,
                        "concat": Kind.BV_CONCAT,
                        "ite": Kind.ITE,
                    }
                    if op == "ite":
                        cond = get_term(node[2], s)
                        then_v = get_term(node[3], s)
                        else_v = get_term(node[4], s)
                        if any(x is None for x in [cond, then_v, else_v]):
                            return None
                        t = tm.mk_term(Kind.ITE, [cond, then_v, else_v])
                    elif op in op_map:
                        a = get_term(node[2], s)
                        b = get_term(node[3], s) if len(node) > 3 else None
                        if a is None or b is None:
                            return None
                        # Coerce b to same sort as a for shift/arith ops
                        try:
                            a_w = a.sort().bv_size()
                            b_w = b.sort().bv_size()
                            if a_w != b_w and op in ("sll", "srl", "sra"):
                                if b_w < a_w:
                                    b = tm.mk_term(Kind.BV_ZERO_EXTEND, [b], [a_w - b_w])
                                else:
                                    b = tm.mk_term(Kind.BV_EXTRACT, [b], [a_w - 1, 0])
                        except Exception:
                            pass
                        try:
                            t = tm.mk_term(op_map[op], [a, b])
                        except Exception:
                            return None
                    else:
                        return None
                    bz_nodes[key] = t
                    return t

            # For each bad property at this step
            for bad_nid in bads:
                bad_term = get_term(bad_nid, step)
                if bad_term is None:
                    continue

                # Add constraints
                for c_nid in constraints:
                    c_term = get_term(c_nid, step)
                    if c_term is not None:
                        try:
                            w = c_term.sort().bv_size()
                            if w == 1:
                                bz.assert_formula(
                                    tm.mk_term(Kind.EQUAL, [c_term, tm.mk_bv_one(tm.mk_bv_sort(1))])
                                )
                        except Exception:
                            bz.assert_formula(c_term)

                # Assert bad == 1
                try:
                    w = bad_term.sort().bv_size()
                    if w == 1:
                        bz.assert_formula(
                            tm.mk_term(Kind.EQUAL, [bad_term, tm.mk_bv_one(tm.mk_bv_sort(1))])
                        )
                    else:
                        # Non-boolean bad: assert != 0
                        bz.assert_formula(
                            tm.mk_term(Kind.DISTINCT, [bad_term, tm.mk_bv_zero(bad_term.sort())])
                        )
                except Exception:
                    # Might be a boolean sort
                    bz.assert_formula(bad_term)

                result = bz.check_sat()
                elapsed = time.monotonic() - start

                if result == Result.SAT:
                    return ("sat", elapsed)

        elapsed = time.monotonic() - start
        return ("unsat", elapsed)

    max_bmc = 201 if is_sequential else 1
    return solve_combinational(max_bmc)


def main():
    import bitwuzla as bz_mod
    bench_dirs = [
        os.path.join(os.path.dirname(__file__), "tiny"),
        os.path.join(os.path.dirname(__file__), "perf"),
    ]

    results = []
    print(f"{'Benchmark':<35} {'BITR':>10} {'Time':>8} {'Bitwuzla':>10} {'Time':>8} {'Match':>6}")
    print("-" * 85)

    for d in bench_dirs:
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".btor2"):
                continue
            path = os.path.join(d, fn)
            label = os.path.basename(d) + "/" + fn

            # Run BITR
            bitr_result, bitr_time = run_bitr(path)

            # Run bitwuzla
            bz_result, bz_time = solve_with_bitwuzla(path)

            match = "OK" if bitr_result == bz_result else "DIFF"
            if bz_result == "n/a":
                match = "n/a"

            speedup = ""
            if bitr_time > 0 and bz_time > 0 and bz_result != "n/a":
                ratio = bitr_time / bz_time
                if ratio > 2:
                    speedup = f" ({ratio:.0f}x slower)"
                elif ratio < 0.5:
                    speedup = f" ({1/ratio:.0f}x faster)"

            print(f"{label:<35} {bitr_result:>10} {bitr_time:>7.3f}s {bz_result:>10} {bz_time:>7.3f}s {match:>6}{speedup}")
            results.append({
                "benchmark": label,
                "bitr_result": bitr_result,
                "bitr_time": bitr_time,
                "bitwuzla_result": bz_result,
                "bitwuzla_time": bz_time,
                "match": match,
            })

    # Write CSV
    csv_path = os.path.join(os.path.dirname(__file__), "comparison_results.csv")
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["benchmark", "bitr_result", "bitr_time", "bitwuzla_result", "bitwuzla_time", "match"])
        writer.writeheader()
        writer.writerows(results)
    print(f"\nResults saved to {csv_path}")

    # Summary
    bitr_solved = sum(1 for r in results if r["bitr_result"] in ("sat", "unsat"))
    bz_solved = sum(1 for r in results if r["bitwuzla_result"] in ("sat", "unsat"))
    mismatches = sum(1 for r in results if r["match"] == "DIFF")
    bitr_total = sum(r["bitr_time"] for r in results if r["bitr_result"] in ("sat", "unsat"))
    bz_total = sum(r["bitwuzla_time"] for r in results if r["bitwuzla_result"] in ("sat", "unsat"))
    print(f"\nSolved: BITR={bitr_solved}, bitwuzla={bz_solved}")
    print(f"Total time: BITR={bitr_total:.3f}s, bitwuzla={bz_total:.3f}s")
    if mismatches:
        print(f"WARNING: {mismatches} result mismatches!")


if __name__ == "__main__":
    main()
