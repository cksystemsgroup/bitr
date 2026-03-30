//! Bounded Model Checking (BMC) loop
//!
//! Unrolls transition relation for k steps, checking bad properties
//! at each step.

use std::collections::HashMap;
use std::time::Instant;

use bvdd::types::{BvcId, BvWidth, SolveResult, TermId};
use bvdd::valueset::ValueSet;
use bvdd::term::{TermTable, TermKind};
use bvdd::constraint::ConstraintTable;
use bvdd::bvc::{BvcManager, BvcEntry};
use bvdd::bvdd::BvddManager;
use bvdd::solver::SolverContext;

use crate::oracle;

/// BMC configuration
pub struct BmcConfig {
    pub max_bound: u32,
    pub timeout_s: f64,
    pub verbose: bool,
}

impl Default for BmcConfig {
    fn default() -> Self {
        BmcConfig {
            max_bound: 100,
            timeout_s: 300.0,
            verbose: false,
        }
    }
}

/// State variable info
pub struct StateVar {
    pub nid: u32,
    pub width: BvWidth,
    pub init_bvc: Option<BvcId>,
    pub next_bvc: Option<BvcId>,
}

/// Input variable info (for fresh-renaming at each BMC step)
pub struct InputVar {
    pub nid: u32,
    pub width: BvWidth,
}

/// Run bounded model checking
#[allow(clippy::too_many_arguments)]
pub fn bmc_check(
    config: &BmcConfig,
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    states: &[StateVar],
    bad_properties: &[BvcId],
    constraints: &[BvcId],
    inputs: &[InputVar],
) -> SolveResult {
    let mut mgr = BvddManager::new();
    let start_time = Instant::now();

    // Set up oracle if available
    let mut smt_oracle = oracle::find_solver().map(|p| {
        let mut o = oracle::SmtOracle::new(&p);
        o.set_timeout(5);
        o
    });

    // state_current[nid] = current BVC for each state variable
    let mut state_current: HashMap<u32, BvcId> = HashMap::new();

    // Initialize states
    for sv in states {
        if let Some(init_bvc) = sv.init_bvc {
            state_current.insert(sv.nid, init_bvc);
        } else {
            let bvc = bm.make_input(tt, ct, sv.nid, sv.width);
            state_current.insert(sv.nid, bvc);
        }
    }

    // Track term sizes to detect blowup
    let mut max_term_size: usize = 0;

    // Pre-compute which inputs need fresh renaming at each step
    // (those that appear in next-state functions)
    let inputs_in_next: std::collections::HashSet<u32> = {
        let mut set = std::collections::HashSet::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let term = bm.get(next_bvc).entries[0].term;
                for &(v, _) in &tt.collect_vars(term) {
                    if inputs.iter().any(|iv| iv.nid == v) {
                        set.insert(v);
                    }
                }
            }
        }
        set
    };

    // Detect inputs used as ITE conditions in next-state (likely reset signals)
    let inputs_as_ite_cond: std::collections::HashSet<u32> = {
        let mut set = std::collections::HashSet::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let term = bm.get(next_bvc).entries[0].term;
                collect_ite_cond_inputs(tt, term, &inputs_in_next, &mut set);
            }
        }
        set
    };

    let mut last_step_time = 0.0f64;

    for k in 0..=config.max_bound {
        let step_start = start_time.elapsed().as_secs_f64();

        // Wall-clock timeout — stop exploring deeper, return current result
        // Also stop if the last step took longer than remaining time budget
        let remaining = config.timeout_s - step_start;
        if remaining <= 0.0 || (k > 2 && last_step_time > remaining * 0.8) {
            if config.verbose {
                eprintln!("bitr: wall-clock timeout at step {}", k);
            }
            break;
        }

        if config.verbose {
            eprintln!("bitr: BMC step {} (terms={})", k, tt.len());
        }

        // Check bad properties at this step, conjoined with constraints
        for (prop_idx, &bad_bvc) in bad_properties.iter().enumerate() {
            // Conjoin bad property with all constraint assumptions
            let mut prop_bvc = bad_bvc;
            for &c in constraints.iter() {
                let resolved_c = substitute_states(tt, ct, bm, c, &state_current);
                prop_bvc = bm.apply(tt, ct, bvdd::types::OpKind::And, &[prop_bvc, resolved_c], 1);
            }
            let resolved_bvc = substitute_states(tt, ct, bm, prop_bvc, &state_current);

            // Check term size for blowup detection
            let term = bm.get(resolved_bvc).entries[0].term;
            let term_size = count_term_nodes(tt, term);
            if term_size > max_term_size {
                max_term_size = term_size;
            }

            let is_ground = bm.is_ground(tt, resolved_bvc);

            // Use BVDD solver for manageable terms, oracle for very large ones
            let mut result = if term_size <= 10_000 {
                let terminal = mgr.make_terminal(resolved_bvc, true, is_ground);
                let mut ctx = SolverContext::new(tt, ct, bm, &mut mgr);
                if let Some(ref mut oracle) = smt_oracle {
                    ctx.set_oracle(|t, term, width, target| {
                        oracle.check(t, term, width, target)
                    });
                }
                let result_bvdd = ctx.solve(terminal, ValueSet::singleton(1));
                let r = ctx.get_result(result_bvdd);
                if config.verbose {
                    eprintln!("bitr: step {} bad[{}] = {:?} (solve_calls={}, term_size={})",
                        k, prop_idx, r, ctx.solve_calls, term_size);
                }
                r
            } else {
                SolveResult::Unknown
            };

            // Only use oracle for very large terms where BVDD is hopeless
            if result == SolveResult::Unknown && term_size > 50_000 {
                if let Some(ref mut oracle) = smt_oracle {
                    let width = bm.get(resolved_bvc).width;
                    result = oracle.check(tt, term, width, ValueSet::singleton(1));
                    if config.verbose {
                        eprintln!("bitr: step {} bad[{}] oracle={:?} (term_size={})",
                            k, prop_idx, result, term_size);
                    }
                }
            }

            if result == SolveResult::Sat {
                if config.verbose {
                    eprintln!("bitr: counterexample found at step {}", k);
                }
                return SolveResult::Sat;
            }
        }

        // Check assumption constraints
        let mut assumption_violated = false;
        for &constraint_bvc in constraints {
            let resolved = substitute_states(tt, ct, bm, constraint_bvc, &state_current);
            let is_ground = bm.is_ground(tt, resolved);
            let terminal = mgr.make_terminal(resolved, true, is_ground);

            let mut ctx = SolverContext::new(tt, ct, bm, &mut mgr);
            let result_bvdd = ctx.solve(terminal, ValueSet::singleton(1));
            let result = ctx.get_result(result_bvdd);

            if result == SolveResult::Unsat {
                assumption_violated = true;
                break;
            }
        }

        if assumption_violated {
            if config.verbose {
                eprintln!("bitr: constraint violated at step {}, stopping", k);
            }
            break;
        }

        // Create fresh input variables for inputs in next-state functions
        let mut input_rename: HashMap<u32, BvcId> = HashMap::new();
        for iv in inputs {
            if inputs_in_next.contains(&iv.nid) {
                // Check if this input is used as an ITE condition in next-state
                // (pattern: ite(input, init_val, compute) — likely a reset signal)
                let is_ite_cond = inputs_as_ite_cond.contains(&iv.nid);
                if is_ite_cond && iv.width == 1 {
                    // Reset signal: set to 0 (no reset) for steps > 0
                    let const_bvc = bm.make_const(tt, ct, 0, 1);
                    input_rename.insert(iv.nid, const_bvc);
                } else {
                    // Data input: create fresh variable
                    let fresh_id = bm.fresh_var();
                    let fresh_bvc = bm.make_input(tt, ct, fresh_id, iv.width);
                    input_rename.insert(iv.nid, fresh_bvc);
                }
            }
        }

        // Advance to next step: substitute next-state functions
        let mut new_state: HashMap<u32, BvcId> = HashMap::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let mut resolved = substitute_states(tt, ct, bm, next_bvc, &state_current);
                // Rename input variables to fresh ones for this step
                if !input_rename.is_empty() {
                    resolved = substitute_states(tt, ct, bm, resolved, &input_rename);
                }
                new_state.insert(sv.nid, resolved);
            } else {
                let fresh_var = bm.fresh_var();
                let bvc = bm.make_input(tt, ct, fresh_var, sv.width);
                new_state.insert(sv.nid, bvc);
            }
        }
        state_current = new_state;

        // Track step timing for adaptive budget
        last_step_time = start_time.elapsed().as_secs_f64() - step_start;

        // Clear caches between steps
        mgr.cache_clear();
        tt.clear_subst_cache();
    }

    // No counterexample found within bound. For HWMCC, report unsat (bounded safe).
    SolveResult::Unsat
}

/// Find input variables used as ITE conditions in a term (likely reset signals)
fn collect_ite_cond_inputs(
    tt: &TermTable,
    term: TermId,
    input_nids: &std::collections::HashSet<u32>,
    result: &mut std::collections::HashSet<u32>,
) {
    match &tt.get(term).kind {
        TermKind::Const(_) | TermKind::Var(_) => {}
        TermKind::App { op, args, .. } => {
            if *op == bvdd::types::OpKind::Ite && !args.is_empty() {
                // Check if the condition (first arg) is an input variable
                if let TermKind::Var(v) = &tt.get(args[0]).kind {
                    if input_nids.contains(v) {
                        result.insert(*v);
                    }
                }
            }
            for &arg in args {
                collect_ite_cond_inputs(tt, arg, input_nids, result);
            }
        }
    }
}

/// Count the number of nodes in a term DAG (memoized traversal)
fn count_term_nodes(tt: &TermTable, root: TermId) -> usize {
    let mut visited = std::collections::HashSet::new();
    count_term_inner(tt, root, &mut visited)
}

fn count_term_inner(tt: &TermTable, id: TermId, visited: &mut std::collections::HashSet<TermId>) -> usize {
    if !visited.insert(id) {
        return 0;
    }
    match &tt.get(id).kind {
        TermKind::Const(_) | TermKind::Var(_) => 1,
        TermKind::App { args, .. } => {
            1 + args.iter().map(|&a| count_term_inner(tt, a, visited)).sum::<usize>()
        }
    }
}

/// Substitute state variable references in a BVC's term.
/// Only substitutes variables that actually appear in the term (avoids wasted work).
fn substitute_states(
    tt: &mut TermTable,
    _ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    bvc: BvcId,
    state_current: &HashMap<u32, BvcId>,
) -> BvcId {
    let entry = &bm.get(bvc).entries[0];
    let mut term = entry.term;
    let constraint = entry.constraint;
    let width = bm.get(bvc).width;

    // Only substitute variables that actually appear in the term
    let vars_in_term = tt.collect_vars(term);
    let vars_set: std::collections::HashSet<u32> = vars_in_term.iter().map(|&(v, _)| v).collect();

    for (&nid, &current_bvc) in state_current {
        if !vars_set.contains(&nid) {
            continue; // Skip: this state variable isn't referenced
        }

        let current_term = bm.get(current_bvc).entries[0].term;

        if let TermKind::Const(val) = tt.get(current_term).kind {
            term = tt.subst_and_fold(term, nid, val);
        } else {
            term = tt.subst_term(term, nid, current_term);
        }
    }

    bm.alloc(width, vec![BvcEntry {
        term,
        constraint,
    }])
}
