# agent-bitr

**Hypothesis**: Do Bitvector Decision Diagrams (BVDDs) represent reasoning state efficiently and effectively enough to outperform the state of the art in SMT solving and bounded model checking on hardware and software verification benchmarks?

Agent-bitr is inspired by [agent-sat](https://github.com/iliazintchenko/agent-sat). However, unlike agent-sat, which aims at demonstrating that AI agents may autonomously discover competitive solving techniques for a well-understood problem (SAT), agent-bitr tests whether agents can build a competitive solver around a **novel, unproven data structure** encoded as agent skill. The question is not just "can agents build a solver?" but "do BVDDs — where the decision diagram IS the complete solver state — provide a unified representation of the usually separate clause databases and assignment trails of conventional CDCL(T) and DPLL(T) solvers and bounded model checkers?". Similar to agent-sat, success is determined through benchmarking against existing state-of-the-art tools.

## What are BVDDs?

BVDDs are nested decision diagrams with **256-bit bitmask edge labels** where:

- **Bitmask AND** is propagation (intersect feasible values)
- **Bitmask OR** is resolution (merge conflicting edges)
- **Empty bitmask** is a conflict (UNSAT)
- Operations work on **bytes rather than bits**

A single BVDD encodes the formula, the assignment trail, AND the learned clauses — all in one incrementally canonical structure. Algorithmic details are in an upcoming publication.

## Architecture

The project is split into two crates:

- **`bvdd/`** — Standalone BVDD library (publishable on crates.io, C API via FFI)
- **`bitr/`** — BTOR2 solver built on the BVDD library

## Build & Run

```bash
# Build (debug)
cargo build

# Build (release, optimized)
cargo build --release

# Run tests
cargo test

# Run on a BTOR2 file
cargo run --release -- benchmarks/tiny/simple_sat.btor2

# Run with statistics
cargo run --release -- --stats --verbose benchmarks/tiny/simple_sat.btor2
```

## Benchmarks

### Hardware Verification
- **HWMCC'24**: 3,498 BTOR2 tasks (1,977 bitvector + 1,521 array) from [Zenodo](https://zenodo.org/records/14156844)
- **CAV'18 BTOR2 suite**: 10 real-world (System)Verilog designs from [JKU](http://fmv.jku.at/cav18-btor2)

### Software Verification
- **QF_BV**: Quantifier-free bitvector benchmarks from [SMT-LIB](https://smt-lib.org/)
- **QF_ABV**: Quantifier-free bitvector + array benchmarks

### Reference Solvers
- **bitwuzla** — State of the art for QF_BV/QF_ABV in SMT-COMP
- **rIC3** — HWMCC'24 gold medalist (BV tracks), [github](https://github.com/gipsyh/rIC3-HWMCC24)
- **AVR** — HWMCC'24 gold in arrays track (IC3sa algorithm)

### Running Benchmarks

```bash
# Download HWMCC'24 benchmarks
./benchmarks/download.sh

# Run bitr on all benchmarks with 300s timeout
./scripts/run_benchmarks.sh

# Compare against reference solver
python3 scripts/compare.py results/bitr.csv results/bitwuzla.csv
```

## Current Status

Phases 0–9 complete. Core solver operational on combinational, sequential, and array benchmarks. 16/16 tiny benchmarks correct. Optimization ongoing.

| Metric | bitr | bitwuzla | rIC3 |
|--------|------|----------|------|
| HW BV solved | — | — | — |
| HW Array solved | — | — | — |
| SW BV solved | — | — | — |
| Total time (s) | — | — | — |

### BVDD Component Status

<!-- PERF_TABLE_START — updated automatically during optimization rounds -->

| Component | Status | Size/Space | Throughput | Notes |
|-----------|--------|-----------|------------|-------|
| **ValueSet** (256-bit bitmask) | Complete | 32 B per set | branchless AND/OR/NOT | `#[inline]` on hot paths; `[u64; 4]` layout |
| **TermTable** (hash-consed DAG) | Complete | 4 B per TermId | — | Memoized `subst_and_fold` + `subst_term` caches |
| **ConstraintTable** | Complete | 4 B per ConstraintId | — | Hash-consed; Restrict with short-circuit AND/OR |
| **BvcManager** | Complete | 4 B per BvcId | — | Structural + lifted ops; fresh var allocation |
| **BvddManager** | Complete | 4 B per BvddId | — | Unique table; edge merging; 64K computed cache |
| **Compiled evaluator** | Complete | stack-alloc ≤32 regs | **81M eval/s** (1-var 28-bit) | `unsafe get_unchecked`; `eval_into` pre-alloc |
| | | | **67M eval/s** (1-var 24-bit) | |
| | | | **35M eval/s** (3-var 8-bit) | More complex term trees run slower per eval |
| **Solver (Canonicalize/Solve)** | Complete | — | — | 4-stage theory resolution cascade |
| **Boolean decomposition** | Complete | — | — | Stage 1: branch on comparison subterms |
| **Generalized blast** | Complete | — | budget 2^28 | Stage 2: narrowest-var-first; compiled multi-eval |
| **Byte-blast oracle** | Complete | — | — | Stage 3: MSB-byte split; adaptive 25% bailout |
| **SMT oracle** | Complete | cached | — | Stage 4: bitwuzla/z3 subprocess; SMT-LIB2 gen |
| **HSC** (hierarchical cascade) | Complete | — | — | MSB→LSB 8-bit slice decomposition |
| **BTOR2 parser** | Complete | — | — | All operators; sorts; negated refs |
| **BTOR2→BVC lifter** | Complete | — | — | Structural/lifted ops; slice/ext; array ROW |
| **Array support** | Complete | — | — | READ-over-WRITE → ITE chain expansion |
| **BMC loop** | Complete | — | — | Init/next substitution (const + symbolic) |
| **Counterexample extraction** | Complete | — | — | Witness from BVDD + blast assignments |

**Performance benchmarks** (exhaustive UNSAT, `x²+1 ≡ 0 mod 2^n`, Apple Silicon):

| Width | Domain | Time | Eval/s |
|-------|--------|------|--------|
| 12-bit | 4K | <0.01s | — |
| 20-bit | 1M | 0.06s | ~17M |
| 24-bit | 16M | 0.24s | ~67M |
| 28-bit | 268M | 3.3s | ~81M |

| Multi-var benchmark | Variables | Domain | Time |
|---------------------|-----------|--------|------|
| two_var_10 (UNSAT) | 2 × 10-bit | 1M | 0.06s |
| three_var_8 (UNSAT) | 3 × 8-bit | 16M | 0.46s |

**Test suite**: 87 tests, 0 clippy warnings, 16/16 tiny benchmarks correct.

<!-- PERF_TABLE_END -->

## Agent-Driven Development

This solver is being built iteratively by Claude Code agents. Each agent session:

1. Reads `program.md` for current status and next steps
2. Reads `.claude/commands/bitr-expert.md` for algorithmic reference
3. Implements the next phase
4. Runs tests and benchmarks
5. Updates `expert.md` with discoveries
6. Commits progress

## License

MIT
