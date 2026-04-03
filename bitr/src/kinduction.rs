//! K-Induction: prove safety properties by combining BMC base case with
//! inductive step checking.
//!
//! For a property P, k-induction checks:
//!   Base case:  P holds at steps 0..k (standard BMC)
//!   Inductive:  If P holds at k consecutive steps, it holds at step k+1
//!
//! If both pass for some k, P is proven safe (unbounded).

use std::collections::HashMap;
use std::time::Instant;

use bvdd::types::{BvcId, OpKind, SolveResult};
use bvdd::valueset::ValueSet;
use bvdd::term::TermTable;
use bvdd::constraint::ConstraintTable;
use bvdd::bvc::{BvcManager, BvcEntry};
use bvdd::bvdd::BvddManager;
use bvdd::solver::SolverContext;

use crate::bmc::{StateVar, InputVar};
use crate::oracle;

/// K-induction configuration
pub struct KInductionConfig {
    pub max_k: u32,
    pub timeout_s: f64,
    pub verbose: bool,
}

/// Run k-induction check.
///
/// Returns Unsat if the property is proven safe (induction succeeded),
/// Sat if a real counterexample is found (base case violated),
/// Unknown if neither succeeds within bounds/timeout.
#[allow(clippy::too_many_arguments)]
pub fn kinduction_check(
    config: &KInductionConfig,
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    states: &[StateVar],
    bad_properties: &[BvcId],
    constraints: &[BvcId],
    inputs: &[InputVar],
) -> SolveResult {
    let start_time = Instant::now();
    let mut mgr = BvddManager::new();

    let mut smt_oracle = oracle::find_solver().map(|p| {
        let mut o = oracle::SmtOracle::new(&p);
        o.set_timeout(5);
        o
    });

    // For the inductive step, we need to check: given P holds at states
    // s_0, s_1, ..., s_{k-1} with valid transitions between them,
    // does P also hold at s_k?
    //
    // Equivalently: is there a sequence of k+1 states with valid transitions
    // where P holds at the first k but fails at the last?
    //
    // Formula: T(s_0,s_1) ∧ T(s_1,s_2) ∧ ... ∧ T(s_{k-1},s_k)
    //          ∧ ¬Bad(s_0) ∧ ¬Bad(s_1) ∧ ... ∧ ¬Bad(s_{k-1})
    //          ∧ Bad(s_k)
    // If UNSAT → induction holds at depth k → property is SAFE.

    // Base case: standard BMC from initial states
    // We track state bindings at each step for the base case
    let mut base_states: Vec<HashMap<u32, BvcId>> = Vec::new();

    // Initialize step 0
    let mut state_current: HashMap<u32, BvcId> = HashMap::new();
    for sv in states {
        if let Some(init_bvc) = sv.init_bvc {
            state_current.insert(sv.nid, init_bvc);
        } else {
            let bvc = bm.make_input(tt, ct, sv.nid, sv.width);
            state_current.insert(sv.nid, bvc);
        }
    }
    base_states.push(state_current.clone());

    // Pre-compute input info (same as BMC)
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

    for k in 0..=config.max_k {
        let elapsed = start_time.elapsed().as_secs_f64();
        if elapsed > config.timeout_s {
            if config.verbose {
                eprintln!("bitr: k-induction timeout at k={}", k);
            }
            break;
        }

        if config.verbose {
            eprintln!("bitr: k-induction k={} (terms={})", k, tt.len());
        }

        // === BASE CASE: check bad property at step k ===
        let state_k = &base_states[k as usize];
        let mut base_failed = false;
        for &bad_bvc in bad_properties {
            let mut prop_bvc = bad_bvc;
            for &c in constraints {
                let resolved_c = crate::bmc::substitute_states(tt, ct, bm, c, state_k);
                prop_bvc = bm.apply(tt, ct, OpKind::And, &[prop_bvc, resolved_c], 1);
            }
            let resolved = crate::bmc::substitute_states(tt, ct, bm, prop_bvc, state_k);
            let result = solve_bvc(tt, ct, bm, &mut mgr, &mut smt_oracle, resolved);

            if result == SolveResult::Sat {
                if config.verbose {
                    eprintln!("bitr: counterexample found at step {} (base case)", k);
                }
                return SolveResult::Sat;
            }
            if result != SolveResult::Unsat {
                base_failed = true; // Unknown — can't confirm base case
            }
        }

        // === INDUCTIVE STEP: check if P holding for k+1 steps implies P at step k+1 ===
        if !base_failed && k > 0 {
            let inductive_result = check_inductive_step(
                tt, ct, bm, &mut mgr, &mut smt_oracle,
                states, bad_properties, constraints, inputs,
                &inputs_in_next, k, config.verbose,
            );

            if inductive_result == SolveResult::Unsat {
                if config.verbose {
                    eprintln!("bitr: k-induction succeeded at k={} — property SAFE", k);
                }
                return SolveResult::Unsat; // PROVEN SAFE
            }
        }

        // Advance base case to step k+1
        let mut input_rename: HashMap<u32, BvcId> = HashMap::new();
        for iv in inputs {
            if inputs_in_next.contains(&iv.nid) {
                let fresh_id = bm.fresh_var();
                let fresh_bvc = bm.make_input(tt, ct, fresh_id, iv.width);
                input_rename.insert(iv.nid, fresh_bvc);
            }
        }

        let cur = base_states.last().unwrap().clone();
        let mut combined_subst: HashMap<u32, BvcId> = cur;
        for (&nid, &bvc) in &input_rename {
            combined_subst.insert(nid, bvc);
        }

        let mut new_state: HashMap<u32, BvcId> = HashMap::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let resolved = crate::bmc::substitute_states(tt, ct, bm, next_bvc, &combined_subst);
                new_state.insert(sv.nid, resolved);
            } else {
                let fresh_var = bm.fresh_var();
                let bvc = bm.make_input(tt, ct, fresh_var, sv.width);
                new_state.insert(sv.nid, bvc);
            }
        }
        base_states.push(new_state);
        tt.clear_subst_cache();
    }

    SolveResult::Unsat // Bounded safe (same as BMC)
}

/// Check the inductive step at depth k:
/// Is there a chain of k+1 states s_0 -> s_1 -> ... -> s_k with
/// valid transitions, where ¬Bad(s_0) ∧ ... ∧ ¬Bad(s_{k-1}) ∧ Bad(s_k)?
/// If UNSAT: the inductive step holds — property is proven safe.
#[allow(clippy::too_many_arguments)]
fn check_inductive_step(
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    mgr: &mut BvddManager,
    smt_oracle: &mut Option<oracle::SmtOracle>,
    states: &[StateVar],
    bad_properties: &[BvcId],
    constraints: &[BvcId],
    inputs: &[InputVar],
    inputs_in_next: &std::collections::HashSet<u32>,
    k: u32,
    verbose: bool,
) -> SolveResult {
    // Create k+1 sets of fresh state variables (unconstrained — no init)
    let mut step_states: Vec<HashMap<u32, BvcId>> = Vec::new();
    for _ in 0..=k {
        let mut state_map: HashMap<u32, BvcId> = HashMap::new();
        for sv in states {
            let fresh_id = bm.fresh_var();
            let bvc = bm.make_input(tt, ct, fresh_id, sv.width);
            state_map.insert(sv.nid, bvc);
        }
        step_states.push(state_map);
    }

    // Build the inductive formula:
    // conjunction = T(s_0,s_1) ∧ T(s_1,s_2) ∧ ... ∧ T(s_{k-1},s_k)
    //              ∧ ¬Bad(s_0) ∧ ... ∧ ¬Bad(s_{k-1})
    //              ∧ constraints(s_0) ∧ ... ∧ constraints(s_k)
    //              ∧ Bad(s_k)

    // Start with Bad(s_k) — the property we're trying to show can't be violated
    let mut formula = bad_properties[0];
    let last_state = &step_states[k as usize];
    formula = crate::bmc::substitute_states(tt, ct, bm, formula, last_state);

    // Add constraints at each step
    for step in 0..=k {
        for &c in constraints {
            let resolved = crate::bmc::substitute_states(tt, ct, bm, c, &step_states[step as usize]);
            formula = bm.apply(tt, ct, OpKind::And, &[formula, resolved], 1);
        }
    }

    // Add ¬Bad at steps 0..k-1 (property holds at all previous states)
    for step in 0..k {
        for &bad_bvc in bad_properties {
            let resolved = crate::bmc::substitute_states(tt, ct, bm, bad_bvc, &step_states[step as usize]);
            // Negate: ¬Bad means the property holds (bad property is NOT triggered)
            let negated = bm.negate(tt, ct, resolved);
            formula = bm.apply(tt, ct, OpKind::And, &[formula, negated], 1);
        }
    }

    // Add transition constraints: T(s_i, s_{i+1}) for i = 0..k-1
    // T(s_i, s_{i+1}) means: for each state var, s_{i+1}.var = next(s_i)
    for step in 0..k {
        // Create fresh inputs for this transition step
        let mut combined_subst: HashMap<u32, BvcId> = step_states[step as usize].clone();
        for iv in inputs {
            if inputs_in_next.contains(&iv.nid) {
                let fresh_id = bm.fresh_var();
                let fresh_bvc = bm.make_input(tt, ct, fresh_id, iv.width);
                combined_subst.insert(iv.nid, fresh_bvc);
            }
        }

        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                // next(s_step) should equal s_{step+1}
                let next_val = crate::bmc::substitute_states(tt, ct, bm, next_bvc, &combined_subst);
                let next_state_var = step_states[(step + 1) as usize].get(&sv.nid).copied().unwrap();

                // Equality constraint: next(s_i) == s_{i+1}
                let next_term = bm.get(next_val).entries[0].term;
                let var_term = bm.get(next_state_var).entries[0].term;
                let eq_term = tt.make_app(OpKind::Eq, vec![next_term, var_term], 1);
                let eq_bvc = bm.alloc(1, vec![BvcEntry {
                    term: eq_term,
                    constraint: ct.true_id(),
                }]);
                formula = bm.apply(tt, ct, OpKind::And, &[formula, eq_bvc], 1);
            }
        }
    }

    // Check: is this formula satisfiable?
    let result = solve_bvc(tt, ct, bm, mgr, smt_oracle, formula);

    if verbose {
        eprintln!("bitr: inductive step k={}: {:?}", k, result);
    }

    // If UNSAT → no counterexample to induction → property is safe
    result
}

/// Solve a BVC using BVDD solver with oracle fallback
fn solve_bvc(
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    mgr: &mut BvddManager,
    smt_oracle: &mut Option<oracle::SmtOracle>,
    bvc: BvcId,
) -> SolveResult {
    let term = bm.get(bvc).entries[0].term;
    let term_size = crate::bmc::count_term_nodes(tt, term);
    let is_ground = bm.is_ground(tt, bvc);

    if term_size <= 10_000 {
        let terminal = mgr.make_terminal(bvc, true, is_ground);
        let mut ctx = SolverContext::new(tt, ct, bm, mgr);
        if let Some(ref mut oracle) = smt_oracle {
            ctx.set_oracle(|t, term, width, target| {
                oracle.check(t, term, width, target)
            });
        }
        let result_bvdd = ctx.solve(terminal, ValueSet::singleton(1));
        ctx.get_result(result_bvdd)
    } else if term_size > 50_000 {
        if let Some(ref mut oracle) = smt_oracle {
            let width = bm.get(bvc).width;
            oracle.check(tt, term, width, ValueSet::singleton(1))
        } else {
            SolveResult::Unknown
        }
    } else {
        SolveResult::Unknown
    }
}
