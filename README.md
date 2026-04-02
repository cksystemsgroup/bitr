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

# Head-to-head comparison: bitr vs bitwuzla (Python API) on tiny+perf benchmarks
pip install bitwuzla
cargo build --release
python3 benchmarks/compare_solvers.py
```

## Current Status

Phases 0–9 complete. Phase 10 optimization in progress. Core solver operational on combinational, sequential, and array benchmarks. 35/35 benchmarks correct. Native CDCL bit-blasting via splr eliminates exhaustive enumeration bottleneck.

| Metric | bitr | bitwuzla | rIC3 |
|--------|------|----------|------|
| HW BV solved (≤500K, 10s) | 42/155 | — | — |
| QF_BV (SMT-LIB2, 20s) | 10/10 | — | — |
| QF_ABV (SMT-LIB2, 20s) | 6/6 | — | — |
| HW Array solved (10s) | 210/321 | — | — |
| Tiny benchmarks | 16/16 | 16/16 | — |
| Perf benchmarks | 19/19 | 19/19 | — |
| Total perf time (no oracle) | 1.4s | 1.1s | — |

### bitr vs bitwuzla Comparison

Benchmarked on combinational and sequential BTOR2 problems (no external oracle). bitwuzla uses CDCL-based bit-blasting; bitr uses BVDD theory resolution with native CDCL bit-blasting (splr) for large domains.

| Benchmark | bitr | bitwuzla | Ratio |
|---|---|---|---|
| tiny (16 combinational+sequential) | all <10ms | all <1ms | ~7x |
| exhaustive_28 (single-var UNSAT, 28-bit) | 1.0s | 0.001s | 1000x |
| wide_mul_32 (single-var UNSAT, 32-bit) | 5ms | 0.001s | 5x |
| shift_puzzle_sat (2-var SAT, 16-bit) | 5ms | 1ms | 5x |
| three_var_8_unsat (3-var UNSAT, 8-bit) | 131ms | 0.5ms | 260x |
| twovars_16 (2-var, 16-bit) | 4ms | 0.5ms | 8x |
| counter_deep (BMC, 16-bit) | 7ms | 136ms | **19x faster** |
| counter_unsat (BMC, 8-bit) | 7ms | 150ms | **21x faster** |

**Key finding**: bitr outperforms bitwuzla on sequential BMC problems (19-21x faster) due to native transition-relation unrolling. For wide combinational problems, native CDCL bit-blasting (splr) closes the gap from 10,000-16,000x to 5-8x. The remaining gap is on exhaustive_28 (compiled blast, 1000x) and three_var_8 (multi-variable enumeration, 260x).

### Optimization History

| Change | Before | After | Speedup |
|---|---|---|---|
| Edge merging O(n²)→O(n) | — | — | structural |
| Solve hot path: avoid enum clone | — | — | terminal path |
| BMC: single-pass substitution | — | — | ~2x per step |
| BMC: conjoin constraints | — | — | N solves → 1 |
| BMC: persist computed cache | 22ms | 7ms | 3x |
| Multi-variable HSC decomposition | — | — | wide BV support |
| Parallel blast budget (2^33/2^32) | — | — | 32-bit support |
| Byte-blast 500ms bailout | 36.4s | 5.2s | 7x |
| CDCL bit-blast reorder (Stage 2b) | 25.4s | 0.004s | 6,600x |
| Gate memoization in bitblaster | — | — | CNF size reduction |
| **Total benchmark time** | **59.7s** | **1.4s** | **43x** |

### BVDD Implementation Status

<!-- PERF_TABLE_START — updated automatically during optimization rounds -->

The table below tracks each BVDD concept, its DPLL(T) analogue, and measured performance.

| BVDD Concept | DPLL(T) Analogue | Status | Space | Notes |
|---|---|---|---|---|
| **Value sets** — 256-bit bitmask edge labels | Literal watches / domain | Done | 32 B | `[u64; 4]`; branchless AND/OR/NOT |
| **BVDD nodes** — decision DAG with value-set edges | Clause database + trail | Done | 4 B id | Hash-consed unique table; arena-allocated |
| **Edge merging** — OR value sets of same-child edges | Clause subsumption | Done | — | Reduces branching factor at construction |
| **BVCs** — constrained symbolic values at terminals | Theory atoms | Done | 4 B id | (term, constraint) pairs |
| **Hash-consed terms** — symbolic expression DAG | Term algebra | Done | 4 B id | Memoized substitution caches |
| **Constraints** — Boolean formulas over predicates | Learned clauses | Done | 4 B id | Hash-consed; short-circuit Restrict |
| **HSC** — hierarchical 8-bit slice cascade | Bit-blasting to SAT | Done | — | MSB→LSB cascade for variables > 8 bits |
| **Computed cache** — memoize Solve(node, valueset) | Conflict cache | Done | 64K entries | Direct-mapped; persists across BMC steps |
| **Canonicalize/Solve** — reducing BVDD to canonical form decides SAT | DPLL(T) search | Done | — | Ground check → terminal → decision traversal |
| **Decide/Restrict** — partition domain by predicate signatures | Decision + BCP | Done | — | Coarsest partition; short-circuit AND/OR |
| **Theory resolution** — 5-stage cascade when no predicates remain | Theory solver | Done | — | See cascade table below |

**Theory resolution cascade** (invoked when all constraints reduce to TRUE/FALSE):

| Stage | Strategy | Budget | Throughput |
|---|---|---|---|
| 1. Boolean decomposition | Branch on 1-bit comparison subterms | — | — |
| 2. Generalized blast | Enumerate variables (packed bytecode evaluator) | 2^28 sequential | **211M eval/s** (parallel) |
| 2b. CDCL bit-blast | Tseitin CNF encoding → splr SAT solver (in-process) | 1M vars, 5M clauses | sub-ms for 32-bit |
| 3. Byte-blast | Split widest variable's MSB byte; enumerate 256 × LSB | depth 4; 500ms timeout | — |
| 3b. Parallel blast | Parallel compiled evaluation for wider domains | 2^33 single-var, 2^32 multi-var | parallel (rayon) |
| 4. Theory oracle | External SMT solver (bitwuzla/z3) on residual | 5s per call | cached |

**Exhaustive search performance** (UNSAT `x²+1 ≡ 0 mod 2^n`, packed bytecode evaluator, 8-core Apple Silicon):

| Width | Domain | Wall time | Eval throughput | Parallelism |
|---|---|---|---|---|
| 12-bit | 4K | <0.01s | — | sequential |
| 20-bit | 1M | 0.04s | ~25M/s | sequential |
| 24-bit | 16M | 0.24s | ~67M/s | parallel (8 cores) |
| 28-bit | 268M | 1.27s | **211M/s** | parallel (8 cores) |
| 2 × 10-bit | 1M | 0.04s | ~25M/s | sequential |
| 3 × 8-bit | 16M | 0.32s | ~50M/s | parallel (8 cores) |

**Test suite**: 103 unit tests, 35/35 benchmarks correct (16 tiny BTOR2 + 19 perf BTOR2). Bitwuzla comparison via `benchmarks/compare_solvers.py`.

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
