#[allow(dead_code)]
mod btor2;
#[allow(dead_code)]
mod lifter;
#[allow(dead_code)]
mod bitr;
#[allow(dead_code)]
mod blast;
mod oracle;
mod bmc;
mod smtlib2;
#[allow(dead_code)]
mod stats;

use std::env;
use std::fs;
use std::process;

use bvdd::types::SolveResult;
use bvdd::valueset::ValueSet;
use bvdd::bvdd::BvddManager;
use bvdd::solver::SolverContext;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: bitr [OPTIONS] <file.btor2>");
        eprintln!("Options:");
        eprintln!("  --verbose    Verbose output");
        eprintln!("  --stats      Print statistics");
        eprintln!("  --timeout N  Timeout in seconds (default: 300)");
        eprintln!("  --bound N    Maximum BMC bound (default: 100)");
        eprintln!("  --no-oracle  Disable external SMT oracle");
        process::exit(1);
    }

    let mut verbose = false;
    let mut print_stats = false;
    let mut timeout_s: f64 = 300.0;
    let mut max_bound: u32 = 100;
    let mut use_oracle = true;
    let mut filename = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--verbose" => verbose = true,
            "--stats" => print_stats = true,
            "--no-oracle" => use_oracle = false,
            "--timeout" => {
                i += 1;
                timeout_s = args[i].parse().unwrap_or(300.0);
            }
            "--bound" => {
                i += 1;
                max_bound = args[i].parse().unwrap_or(100);
            }
            arg if !arg.starts_with('-') => filename = Some(arg.to_string()),
            other => {
                eprintln!("Unknown option: {}", other);
                process::exit(1);
            }
        }
        i += 1;
    }

    let filename = match filename {
        Some(f) => f,
        None => {
            eprintln!("Error: no input file specified");
            process::exit(1);
        }
    };

    if verbose {
        eprintln!("bitr: loading {}", filename);
    }

    // Detect external SMT solver
    let solver_path = if use_oracle {
        oracle::find_solver()
    } else {
        None
    };
    if verbose {
        match &solver_path {
            Some(p) => eprintln!("bitr: oracle solver: {}", p),
            None => eprintln!("bitr: no oracle solver available"),
        }
    }

    // Read and parse BTOR2
    let input = match fs::read_to_string(&filename) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading {}: {}", filename, e);
            process::exit(1);
        }
    };

    // Detect format: SMT-LIB2 (.smt2) or BTOR2 (.btor2)
    let is_smt2 = filename.ends_with(".smt2") ||
        input.trim_start().starts_with('(') ||
        input.contains("set-logic");

    let overall_result = if is_smt2 {
        // SMT-LIB2 mode
        if verbose {
            eprintln!("bitr: SMT-LIB2 mode");
        }
        solve_smtlib2(&input, verbose, print_stats, solver_path.as_deref())
    } else {
        // BTOR2 mode
        solve_btor2(&input, verbose, print_stats, solver_path.as_deref(), max_bound, timeout_s)
    };

    match overall_result {
        SolveResult::Sat => println!("sat"),
        SolveResult::Unsat => println!("unsat"),
        SolveResult::Unknown => {
            println!("unknown");
            process::exit(1);
        }
    }
}

fn solve_smtlib2(
    input: &str,
    verbose: bool,
    print_stats: bool,
    solver_path: Option<&str>,
) -> SolveResult {
    let mut model = match smtlib2::parse_smtlib2(input) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("SMT-LIB2 parse error: {}", e);
            return SolveResult::Unknown;
        }
    };

    if verbose {
        eprintln!("bitr: {} assertions, {} variables",
            model.assertions.len(), model.var_map.len());
    }

    if model.assertions.is_empty() {
        return SolveResult::Sat; // No constraints = trivially SAT
    }

    // Conjoin all assertions: the conjunction must be satisfiable
    // Build term: AND(assert1, AND(assert2, ...))
    let mut conj_bvc = model.assertions[0];
    for &a in &model.assertions[1..] {
        conj_bvc = model.bm.apply(
            &mut model.tt, &mut model.ct, bvdd::types::OpKind::And,
            &[conj_bvc, a], 1,
        );
    }

    let mut mgr = BvddManager::new();
    let is_ground = model.bm.is_ground(&model.tt, conj_bvc);
    let terminal = mgr.make_terminal(conj_bvc, true, is_ground);
    let target = ValueSet::singleton(1);

    let mut smt_oracle = solver_path.map(|p| {
        let mut o = oracle::SmtOracle::new(p);
        o.set_timeout(5);
        o
    });

    let (result, solve_calls, canon_calls) = {
        let mut ctx = SolverContext::new(
            &mut model.tt,
            &mut model.ct,
            &mut model.bm,
            &mut mgr,
        );
        // SMT-LIB2 mode: set 5s timeout for fast oracle fallback
        ctx.solve_timeout_s = 5.0;
        if let Some(ref mut oracle) = smt_oracle {
            ctx.set_oracle(|tt, term, width, target| {
                oracle.check(tt, term, width, target)
            });
        }
        let result_bvdd = ctx.solve(terminal, target);
        let r = ctx.get_result(result_bvdd);
        (r, ctx.solve_calls, ctx.canonicalize_calls)
    };

    if verbose {
        eprintln!("bitr: result={:?} (solve={}, canon={})", result, solve_calls, canon_calls);
    }

    if print_stats {
        eprintln!("  Cache hits/misses: {}/{}", mgr.cache_hits, mgr.cache_misses);
    }

    // If BVDD solver returns Unknown, fall back to external solver on original input
    if result == SolveResult::Unknown {
        if let Some(path) = solver_path {
            if verbose {
                eprintln!("bitr: BVDD returned Unknown, falling back to oracle on raw SMT-LIB2");
            }
            // Write the original input to a temp file and solve directly
            let tmp = std::env::temp_dir().join("bitr_smt2_fallback.smt2");
            if std::fs::write(&tmp, input).is_ok() {
                let oracle_result = oracle::solve_smtlib2_file(path, tmp.to_str().unwrap_or(""));
                let _ = std::fs::remove_file(&tmp);
                if verbose {
                    eprintln!("bitr: oracle={:?}", oracle_result);
                }
                return oracle_result;
            }
        }
    }

    result
}

fn solve_btor2(
    input: &str,
    verbose: bool,
    print_stats: bool,
    solver_path: Option<&str>,
    max_bound: u32,
    timeout_s: f64,
) -> SolveResult {
    let model = match btor2::parse_btor2(input) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            return SolveResult::Unknown;
        }
    };

    if verbose {
        eprintln!("bitr: {} sorts, {} nodes, {} bad properties",
            model.sorts.len(), model.nodes.len(), model.bad_properties.len());
    }

    let mut lifted = match lifter::lift_btor2(&model) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("Lift error: {}", e);
            return SolveResult::Unknown;
        }
    };

    if verbose {
        eprintln!("bitr: lifted {} BVCs, {} states", lifted.bm.len(), lifted.states.len());
    }

    let is_sequential = lifted.states.iter().any(|(_, _, next)| next.is_some());

    if is_sequential {
        if verbose {
            eprintln!("bitr: sequential model, running BMC (max_bound={})", max_bound);
        }
        let state_vars: Vec<bmc::StateVar> = lifted.states.iter().map(|&(nid, init, next)| {
            let width = lifted.bm.get(
                *lifted.nid_to_bvc.get(&nid).unwrap_or(&bvdd::types::BvcId(0))
            ).width;
            bmc::StateVar { nid, width, init_bvc: init, next_bvc: next }
        }).collect();

        let bmc_config = bmc::BmcConfig {
            max_bound,
            timeout_s,
            verbose,
        };
        bmc::bmc_check(
            &bmc_config,
            &mut lifted.tt,
            &mut lifted.ct,
            &mut lifted.bm,
            &state_vars,
            &lifted.bad_properties,
            &lifted.constraints,
        )
    } else {
        if verbose {
            eprintln!("bitr: combinational model, solving directly");
        }
        solve_combinational(&mut lifted, verbose, print_stats, solver_path)
    }
}

fn solve_combinational(
    lifted: &mut lifter::LiftedModel,
    verbose: bool,
    print_stats: bool,
    solver_path: Option<&str>,
) -> SolveResult {
    let mut mgr = BvddManager::new();
    let mut overall_result = SolveResult::Unsat;

    // Set up oracle if available
    let mut smt_oracle = solver_path.map(|p| {
        let mut o = oracle::SmtOracle::new(p);
        o.set_timeout(5);
        o
    });

    for (i, &bad_bvc) in lifted.bad_properties.iter().enumerate() {
        let is_ground = lifted.bm.is_ground(&lifted.tt, bad_bvc);
        let terminal = mgr.make_terminal(bad_bvc, true, is_ground);
        let target = ValueSet::singleton(1);

        let (result, solve_calls, canon_calls, decide_calls, sat_w, unsat_t, restrict_c,
             oracle_calls, compiled_calls, witness) = {
            let mut ctx = SolverContext::new(
                &mut lifted.tt,
                &mut lifted.ct,
                &mut lifted.bm,
                &mut mgr,
            );
            // Wire oracle
            if let Some(ref mut oracle) = smt_oracle {
                ctx.set_oracle(|tt, term, width, target| {
                    oracle.check(tt, term, width, target)
                });
            }
            let result_bvdd = ctx.solve(terminal, target);
            let result = ctx.get_result(result_bvdd);
            let witness = if result == SolveResult::Sat {
                ctx.extract_witness(result_bvdd, target)
            } else {
                std::collections::HashMap::new()
            };
            (result, ctx.solve_calls, ctx.canonicalize_calls, ctx.decide_calls,
             ctx.sat_witnesses, ctx.unsat_terminals, ctx.restrict_calls,
             ctx.oracle_calls, ctx.compiled_blast_calls, witness)
        };

        if verbose {
            eprintln!("bitr: bad[{}] = {:?} (solve={}, canon={}, decide={}, oracle={}, compiled={})",
                i, result, solve_calls, canon_calls, decide_calls, oracle_calls, compiled_calls);
        }

        if print_stats {
            eprintln!("  SAT witnesses: {}", sat_w);
            eprintln!("  UNSAT terminals: {}", unsat_t);
            eprintln!("  Restrict calls: {}", restrict_c);
            eprintln!("  Cache hits/misses: {}/{}", mgr.cache_hits, mgr.cache_misses);
            if let Some(ref oracle) = smt_oracle {
                eprintln!("  Oracle calls/hits: {}/{}", oracle.calls, oracle.cache_hits);
            }
        }

        match result {
            SolveResult::Sat => {
                if verbose {
                    eprintln!("bitr: bad[{}] is reachable", i);
                    if !witness.is_empty() {
                        eprintln!("bitr: witness:");
                        let mut sorted: Vec<_> = witness.iter().collect();
                        sorted.sort_by_key(|(&k, _)| k);
                        for (&var_id, &val) in &sorted {
                            // Skip lifted variables (high range)
                            if var_id < 0x1000_0000 {
                                eprintln!("  v{} = {}", var_id, val);
                            }
                        }
                    }
                }
                return SolveResult::Sat;
            }
            SolveResult::Unsat => {
                if verbose {
                    eprintln!("bitr: bad[{}] is unreachable", i);
                }
            }
            SolveResult::Unknown => {
                overall_result = SolveResult::Unknown;
            }
        }
    }
    overall_result
}
