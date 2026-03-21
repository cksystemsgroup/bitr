//! Bounded Model Checking (BMC) loop
//!
//! Unrolls transition relation for k steps, checking bad properties
//! at each step.

use std::collections::HashMap;

use bvdd::types::{BvcId, BvWidth, SolveResult};
use bvdd::valueset::ValueSet;
use bvdd::term::TermTable;
use bvdd::constraint::ConstraintTable;
use bvdd::bvc::{BvcManager, BvcEntry};
use bvdd::bvdd::BvddManager;
use bvdd::solver::SolverContext;

/// BMC configuration
pub struct BmcConfig {
    pub max_bound: u32,
    #[allow(dead_code)]
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

/// Run bounded model checking
pub fn bmc_check(
    config: &BmcConfig,
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    states: &[StateVar],
    bad_properties: &[BvcId],
    constraints: &[BvcId],
) -> SolveResult {
    let mut mgr = BvddManager::new();

    // For step 0: apply init values to state variables
    // state_current[nid] = current BVC for each state variable
    let mut state_current: HashMap<u32, BvcId> = HashMap::new();

    // Initialize states
    for sv in states {
        if let Some(init_bvc) = sv.init_bvc {
            state_current.insert(sv.nid, init_bvc);
        } else {
            // No init: unconstrained at step 0
            let bvc = bm.make_input(tt, ct, sv.nid, sv.width);
            state_current.insert(sv.nid, bvc);
        }
    }

    for k in 0..=config.max_bound {
        if config.verbose {
            eprintln!("bitr: BMC step {}", k);
        }

        // At step k, build the bad property BVCs by substituting
        // current state values into the expressions
        for (prop_idx, &bad_bvc) in bad_properties.iter().enumerate() {
            // Substitute state variable terms with their current BVC terms
            let resolved_bvc = substitute_states(tt, ct, bm, bad_bvc, &state_current);

            let is_ground = bm.is_ground(tt, resolved_bvc);
            let terminal = mgr.make_terminal(resolved_bvc, true, is_ground);

            let mut ctx = SolverContext::new(tt, ct, bm, &mut mgr);
            let result_bvdd = ctx.solve(terminal, ValueSet::singleton(1));
            let result = ctx.get_result(result_bvdd);

            if config.verbose {
                eprintln!("bitr: step {} bad[{}] = {:?} (solve_calls={})",
                    k, prop_idx, result, ctx.solve_calls);
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
                // Constraint can't be satisfied → this step is vacuously safe
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

        // Advance to next step: substitute next-state functions
        let mut new_state: HashMap<u32, BvcId> = HashMap::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                // Substitute current state values into the next-state expression
                let resolved = substitute_states(tt, ct, bm, next_bvc, &state_current);
                new_state.insert(sv.nid, resolved);
            } else {
                // No next-state function: create fresh input for this step
                let fresh_var = bm.fresh_var();
                let bvc = bm.make_input(tt, ct, fresh_var, sv.width);
                new_state.insert(sv.nid, bvc);
            }
        }
        state_current = new_state;

        // Clear caches between steps
        mgr.cache_clear();
        tt.clear_subst_cache();
    }

    // Reached max bound without finding SAT
    SolveResult::Unsat
}

/// Substitute state variable references in a BVC's term.
/// Replaces Var(state_nid) with the current state BVC's term.
/// Uses constant substitution when possible, term-for-term otherwise.
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

    // For each state variable, substitute its current value
    for (&nid, &current_bvc) in state_current {
        let current_term = bm.get(current_bvc).entries[0].term;

        if let bvdd::term::TermKind::Const(val) = tt.get(current_term).kind {
            // Constant: use fast subst_and_fold
            term = tt.subst_and_fold(term, nid, val);
        } else {
            // Symbolic: use term-for-term substitution
            term = tt.subst_term(term, nid, current_term);
        }
    }

    bm.alloc(width, vec![BvcEntry {
        term,
        constraint,
    }])
}
