# agent-bitr

**Hypothesis**: Do Bitvector Decision Diagrams (BVDDs) represent reasoning state efficiently and effectively enough to outperform the state of the art in SMT solving and bounded model checking on hardware and software verification benchmarks?

Inspired by yet unlike [agent-sat](https://github.com/iliazintchenko/agent-sat), which aims at demonstrating that AI agents may autonomously discover competitive solving techniques for a well-understood problem (SAT), agent-bitr tests whether agents can build a competitive solver around a **novel, unproven data structure** encoded as agent skill. The question is not just "can agents build a solver?" but "do BVDDs — where the decision diagram IS the complete solver state — provide a unified representation of the usually separate clause databases and assignment trails of conventional CDCL(T) and DPLL(T) solvers and bounded model checkers?". Similar to [agent-sat](https://github.com/iliazintchenko/agent-sat), success is determined through benchmarking against existing state-of-the-art tools.

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

Phase 0: Project scaffolding complete. BTOR2 parser and core type stubs implemented. Awaiting Phase 1 implementation (value sets + terms).

| Metric | bitr | bitwuzla | rIC3 |
|--------|------|----------|------|
| HW BV solved | — | — | — |
| HW Array solved | — | — | — |
| SW BV solved | — | — | — |
| Total time (s) | — | — | — |

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
