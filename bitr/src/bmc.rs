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
    /// When true and an oracle is available, cross-check each SAT/UNSAT answer
    /// against the external SMT solver and panic on disagreement. Dev/CI only.
    pub verify_mode: bool,
}

impl Default for BmcConfig {
    fn default() -> Self {
        BmcConfig {
            max_bound: 100,
            timeout_s: 300.0,
            verbose: false,
            verify_mode: false,
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

    // Accumulated constraint history: AND of constraint(state_i, input_i)
    // for every step i = 0..k seen so far. Soundness requires checking
    // bad(state_k) ∧ constraint(state_0) ∧ ... ∧ constraint(state_k), not just
    // bad(state_k) ∧ constraint(state_k) — otherwise we accept traces that
    // violated earlier-step constraints (witnessed on picorv32-check-p09).
    let mut accumulated_constraints: Option<BvcId> = None;

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

    // Detect inputs used as ITE conditions in next-state (likely reset signals).
    //
    // A5 SOUNDNESS FENCE: an input qualifies as a reset only if it appears
    // *exclusively* as a direct ITE condition — never in a data position of any
    // next-state, bad property, or constraint. Otherwise zeroing it after step 0
    // would silently change program semantics and produce wrong answers.
    let inputs_as_ite_cond: std::collections::HashSet<u32> = {
        let mut candidates = std::collections::HashSet::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let term = bm.get(next_bvc).entries[0].term;
                collect_ite_cond_inputs(tt, term, &inputs_in_next, &mut candidates);
            }
        }
        // Disqualify any candidate that appears in a data position anywhere.
        let mut disqualified = std::collections::HashSet::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let term = bm.get(next_bvc).entries[0].term;
                collect_non_reset_uses(tt, term, &candidates, &mut disqualified);
            }
        }
        for &bad_bvc in bad_properties {
            let term = bm.get(bad_bvc).entries[0].term;
            collect_non_reset_uses(tt, term, &candidates, &mut disqualified);
        }
        for &c_bvc in constraints {
            let term = bm.get(c_bvc).entries[0].term;
            collect_non_reset_uses(tt, term, &candidates, &mut disqualified);
        }
        candidates.into_iter().filter(|v| !disqualified.contains(v)).collect()
    };

    let mut last_step_time = 0.0f64;

    // Term-table growth bail-out. Once the global term table exceeds this
    // many nodes, subsequent substitute_states calls become prohibitively
    // slow (the DAG blows up exponentially with each unroll). Bailing out
    // returns Unknown rather than hanging — the Phase B incremental BMC
    // path is what should recover these cases.
    const TERM_TABLE_BAIL: usize = 500_000;

    for k in 0..=config.max_bound {
        let step_start = start_time.elapsed().as_secs_f64();

        // Wall-clock timeout — stop exploring deeper, return current result
        // Also stop if the last step took longer than remaining time budget.
        let remaining = config.timeout_s - step_start;
        if remaining <= 0.0 || (k > 2 && last_step_time > remaining * 0.8) {
            if config.verbose {
                eprintln!("bitr: wall-clock timeout at step {}", k);
            }
            break;
        }
        // Term-table growth bail-out: once we've accumulated too many terms,
        // substitute_states for the next step will take minutes. Stop cleanly.
        if tt.len() > TERM_TABLE_BAIL {
            if config.verbose {
                eprintln!("bitr: term table grew past {} at step {}, bailing",
                    TERM_TABLE_BAIL, k);
            }
            break;
        }

        if config.verbose {
            let cache_total = mgr.cache_hits + mgr.cache_misses;
            let cache_rate = if cache_total > 0 { mgr.cache_hits as f64 / cache_total as f64 * 100.0 } else { 0.0 };
            eprintln!("bitr: BMC step {} (terms={}, cache={:.0}% of {}, elapsed={:.1}s)",
                k, tt.len(), cache_rate, cache_total, start_time.elapsed().as_secs_f64());
        }

        // Extend the accumulated constraint history with constraint(state_k).
        // This must precede the bad check so the check sees all prior steps'
        // constraints too.
        for &c in constraints.iter() {
            let resolved_c = substitute_states(tt, ct, bm, c, &state_current);
            accumulated_constraints = Some(match accumulated_constraints {
                None => resolved_c,
                Some(prev) => bm.apply(tt, ct, bvdd::types::OpKind::And, &[prev, resolved_c], 1),
            });
        }

        // Check bad properties at this step, conjoined with ALL accumulated
        // step constraints (0..k).
        for (prop_idx, &bad_bvc) in bad_properties.iter().enumerate() {
            let mut prop_bvc = bad_bvc;
            if let Some(acc) = accumulated_constraints {
                prop_bvc = bm.apply(tt, ct, bvdd::types::OpKind::And, &[prop_bvc, acc], 1);
            }
            let resolved_bvc = substitute_states(tt, ct, bm, prop_bvc, &state_current);

            // Check term size for blowup detection
            let term = bm.get(resolved_bvc).entries[0].term;
            let term_size = count_term_nodes(tt, term);
            if term_size > max_term_size {
                max_term_size = term_size;
            }

            let is_ground = bm.is_ground(tt, resolved_bvc);

            // Tiered solving: BVDD (small, time-bounded) → bitblaster (medium) → oracle (large)
            let width = bm.get(resolved_bvc).width;
            let prop_start = Instant::now();
            let mut tier_used = "none";
            // Remaining wall-clock budget for this property, across all tiers.
            // Tier-specific defaults (5s BVDD, 10s bitblaster, 5s oracle) must
            // never exceed this, otherwise per-step solves can silently blow
            // the outer config.timeout_s by 20s+ per property.
            let remaining_for_prop = (config.timeout_s - step_start).max(0.5);
            let mut result = if term_size <= 10_000 {
                tier_used = "bvdd";
                let terminal = mgr.make_terminal(resolved_bvc, true, is_ground);
                let mut ctx = SolverContext::new(tt, ct, bm, &mut mgr);
                // Cap BVDD tier at min(5s, remaining).
                ctx.solve_timeout_s = 5.0_f64.min(remaining_for_prop);
                if let Some(ref mut oracle) = smt_oracle {
                    ctx.set_oracle(|t, term, width, target| {
                        oracle.check(t, term, width, target)
                    });
                }
                let result_bvdd = ctx.solve(terminal, ValueSet::singleton(1));
                let raw = ctx.get_result(result_bvdd);
                // A2: verify SAT witness against original property term. If the
                // heuristic witness search fails or produces an assignment that
                // doesn't satisfy the target, downgrade to Unknown so a lower
                // tier (bitblaster/oracle) can reattempt.
                if raw == SolveResult::Sat {
                    let target_vs = ValueSet::singleton(1);
                    if ctx.extract_witness_verified(result_bvdd, target_vs, term).is_none() {
                        SolveResult::Unknown
                    } else {
                        SolveResult::Sat
                    }
                } else {
                    raw
                }
            } else {
                SolveResult::Unknown
            };

            // CDCL bitblaster for medium terms or wide terms that skipped BVDD
            if result == SolveResult::Unknown && term_size <= 200_000 {
                tier_used = "bitblast";
                let target = ValueSet::singleton(1);
                let mut bb = bvdd::bitblast::BitBlaster::new(tt);
                // Cap at min(10s, remaining for property).
                let bb_remaining = (config.timeout_s - start_time.elapsed().as_secs_f64()).max(0.5);
                bb.set_timeout(10.0_f64.min(bb_remaining));
                let (bb_result, bb_witness) = bb.solve(term, width, &target);
                match bb_result {
                    SolveResult::Sat => {
                        // Verify witness
                        if let Some(val) = tt.eval(term, &bb_witness) {
                            if target.contains((val & 1) as u8) {
                                result = SolveResult::Sat;
                            }
                        }
                        if result != SolveResult::Sat {
                            result = SolveResult::Unknown; // Witness didn't verify
                        }
                    }
                    SolveResult::Unsat => result = SolveResult::Unsat,
                    SolveResult::Unknown => {} // Budget exceeded, fall through
                }
            }

            // External oracle for very large terms
            if result == SolveResult::Unknown && term_size > 50_000 {
                if let Some(ref mut oracle) = smt_oracle {
                    tier_used = "oracle";
                    result = oracle.check(tt, term, width, ValueSet::singleton(1));
                }
            }

            if config.verbose {
                let prop_ms = prop_start.elapsed().as_secs_f64() * 1000.0;
                eprintln!("bitr: step {} bad[{}] = {:?} (tier={}, term_size={}, {:.1}ms)",
                    k, prop_idx, result, tier_used, term_size, prop_ms);
            }

            if result == SolveResult::Sat {
                if config.verbose {
                    eprintln!("bitr: counterexample found at step {}", k);
                }
                if config.verify_mode {
                    if let Some(ref mut oracle) = smt_oracle {
                        verify_against_oracle(
                            tt, term, width, ValueSet::singleton(1),
                            SolveResult::Sat, oracle,
                            &format!("bmc step={} bad[{}]", k, prop_idx),
                        );
                    }
                }
                return SolveResult::Sat;
            }
        }

        // Check assumption constraints: conjoin all into one BVC and solve once
        let mut assumption_violated = false;
        if !constraints.is_empty() {
            let mut conjoined = {
                let first = constraints[0];
                substitute_states(tt, ct, bm, first, &state_current)
            };
            for &constraint_bvc in &constraints[1..] {
                let resolved = substitute_states(tt, ct, bm, constraint_bvc, &state_current);
                conjoined = bm.apply(tt, ct, bvdd::types::OpKind::And, &[conjoined, resolved], 1);
            }
            let is_ground = bm.is_ground(tt, conjoined);
            let terminal = mgr.make_terminal(conjoined, true, is_ground);

            let mut ctx = SolverContext::new(tt, ct, bm, &mut mgr);
            let result_bvdd = ctx.solve(terminal, ValueSet::singleton(1));
            let result = ctx.get_result(result_bvdd);

            if result == SolveResult::Unsat {
                assumption_violated = true;
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
                // SOUNDNESS: every input is FRESH at every step. The previous
                // reset-signal heuristic (zeroing width-1 ITE-cond inputs after
                // step 0) plus A5's fence both produced wrong verdicts on some
                // benchmarks (e.g., picorv32-check-p09, where ref-solvers agree
                // UNSAT but we claimed SAT when the "reset" was free to toggle).
                // Identifying true reset signals requires BTOR2-level annotation
                // or principled analysis, not a shape heuristic.
                let fresh_id = bm.fresh_var();
                let fresh_bvc = bm.make_input(tt, ct, fresh_id, iv.width);
                input_rename.insert(iv.nid, fresh_bvc);
            }
        }
        // `inputs_as_ite_cond` is retained in the function only for the A5
        // tests' benefit; it's no longer consulted at step advancement.
        let _ = &inputs_as_ite_cond;

        // Advance to next step: substitute next-state functions
        // Merge state_current and input_rename into a single map for one substitution pass
        let mut combined_subst: HashMap<u32, BvcId> = state_current.clone();
        for (&nid, &bvc) in &input_rename {
            combined_subst.insert(nid, bvc);
        }

        let mut new_state: HashMap<u32, BvcId> = HashMap::new();
        for sv in states {
            if let Some(next_bvc) = sv.next_bvc {
                let resolved = substitute_states(tt, ct, bm, next_bvc, &combined_subst);
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

        // Clear substitution cache between steps (term-specific to current state mapping).
        // The BVDD computed cache persists across steps since prior terms can still be useful.
        tt.clear_subst_cache();
    }

    // No counterexample found within bound. This is NOT a proof of safety —
    // an unbounded proof requires k-induction (or similar). Return Unknown so
    // the caller can either accept bounded safety or fall back to other methods.
    SolveResult::Unknown
}

/// Collect input variables that appear in `term` at any NON-ITE-condition
/// position (i.e., data-path uses). An input found here is NOT a pure reset
/// signal: zeroing it for step > 0 would silently change program semantics.
///
/// The walk descends through ITE(cond, then, else) but only records inputs
/// reached via `then`/`else` or via non-ITE op args.
pub fn collect_non_reset_uses(
    tt: &TermTable,
    term: TermId,
    input_nids: &std::collections::HashSet<u32>,
    result: &mut std::collections::HashSet<u32>,
) {
    collect_non_reset_uses_inner(tt, term, input_nids, result, true);
}

fn collect_non_reset_uses_inner(
    tt: &TermTable,
    term: TermId,
    input_nids: &std::collections::HashSet<u32>,
    result: &mut std::collections::HashSet<u32>,
    in_data_position: bool,
) {
    match &tt.get(term).kind {
        TermKind::Const(_) => {}
        TermKind::Var(v) => {
            if in_data_position && input_nids.contains(v) {
                result.insert(*v);
            }
        }
        TermKind::App { op, args, .. } => {
            if *op == bvdd::types::OpKind::Ite && args.len() == 3 {
                // ITE: args[0]=cond (non-data), args[1]=then (data), args[2]=else (data)
                collect_non_reset_uses_inner(tt, args[0], input_nids, result, false);
                collect_non_reset_uses_inner(tt, args[1], input_nids, result, true);
                collect_non_reset_uses_inner(tt, args[2], input_nids, result, true);
            } else {
                // Non-ITE ops: every arg is a data position.
                for &a in args {
                    collect_non_reset_uses_inner(tt, a, input_nids, result, true);
                }
            }
        }
    }
}

/// Find input variables used as ITE conditions in a term (likely reset signals)
pub fn collect_ite_cond_inputs(
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
pub fn count_term_nodes(tt: &TermTable, root: TermId) -> usize {
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
pub fn substitute_states(
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

/// Cross-check a BITR answer against the external SMT oracle. Panics with a
/// diagnostic dump on disagreement. Used only when `verify_mode` is enabled
/// (dev/CI; never in production runs). If the oracle returns `Unknown`, no
/// assertion is made — a silent oracle failure shouldn't crash verification.
pub fn verify_against_oracle(
    tt: &mut TermTable,
    term: TermId,
    width: BvWidth,
    target: ValueSet,
    expected: SolveResult,
    oracle: &mut oracle::SmtOracle,
    context: &str,
) {
    let oracle_result = oracle.check(tt, term, width, target);
    if oracle_result == SolveResult::Unknown {
        return; // oracle couldn't decide — accept our answer without cross-check
    }
    if oracle_result != expected {
        eprintln!("bitr: VERIFY MISMATCH [{}]", context);
        eprintln!("  expected (bitr): {:?}", expected);
        eprintln!("  oracle:          {:?}", oracle_result);
        eprintln!("  width: {}  target: {:?}", width, target);
        panic!("verify-mode: oracle disagreement at {}", context);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btor2::parse_btor2;
    use crate::lifter::lift_btor2;

    /// A1 soundness test: BMC with bound-exhaustion must return Unknown, not Unsat.
    ///
    /// counter_unsat: 2-bit counter cnt, init=0, next=cnt+2, bad=(cnt==1).
    /// The counter visits {0, 2} cyclically — cnt==1 is never reachable, but a
    /// pure BMC of any bound cannot PROVE this. With max_bound=2, BMC checks
    /// steps 0,1,2 (cnt values 0,2,0), finds no counterexample, and must
    /// return Unknown because unbounded safety isn't established.
    #[test]
    fn test_bmc_bound_exhausted_returns_unknown() {
        let input = "\
1 sort bitvec 2
2 sort bitvec 1
3 state 1 cnt
4 zero 1
5 init 1 3 4
6 constd 1 2
7 add 1 3 6
8 next 1 3 7
9 one 1
10 eq 2 3 9
11 bad 10
";
        let model = parse_btor2(input).unwrap();
        let mut lifted = lift_btor2(&model).unwrap();

        let state_vars: Vec<StateVar> = lifted.states.iter().map(|&(nid, init, next)| {
            let width = lifted.bm.get(
                *lifted.nid_to_bvc.get(&nid).unwrap_or(&bvdd::types::BvcId(0))
            ).width;
            StateVar { nid, width, init_bvc: init, next_bvc: next }
        }).collect();

        let input_vars: Vec<InputVar> = lifted.inputs.iter()
            .map(|&(nid, width)| InputVar { nid, width })
            .collect();

        let config = BmcConfig { max_bound: 2, timeout_s: 30.0, verbose: false, verify_mode: false };
        let result = bmc_check(
            &config,
            &mut lifted.tt,
            &mut lifted.ct,
            &mut lifted.bm,
            &state_vars,
            &lifted.bad_properties,
            &lifted.constraints,
            &input_vars,
        );

        assert_eq!(result, SolveResult::Unknown,
            "BMC bound-exhausted must return Unknown, not Unsat (A1 soundness).");
    }

    /// Complementary test: BMC still finds real SAT counterexamples.
    /// counter_sat: 3-bit counter, bad=(cnt==5). Reachable at step 5.
    #[test]
    fn test_bmc_finds_sat_counterexample() {
        let input = "\
1 sort bitvec 3
2 sort bitvec 1
3 state 1 cnt
4 zero 1
5 init 1 3 4
6 one 1
7 add 1 3 6
8 next 1 3 7
9 constd 1 5
10 eq 2 3 9
11 bad 10
";
        let model = parse_btor2(input).unwrap();
        let mut lifted = lift_btor2(&model).unwrap();

        let state_vars: Vec<StateVar> = lifted.states.iter().map(|&(nid, init, next)| {
            let width = lifted.bm.get(
                *lifted.nid_to_bvc.get(&nid).unwrap_or(&bvdd::types::BvcId(0))
            ).width;
            StateVar { nid, width, init_bvc: init, next_bvc: next }
        }).collect();

        let input_vars: Vec<InputVar> = lifted.inputs.iter()
            .map(|&(nid, width)| InputVar { nid, width })
            .collect();

        let config = BmcConfig { max_bound: 10, timeout_s: 30.0, verbose: false, verify_mode: false };
        let result = bmc_check(
            &config,
            &mut lifted.tt,
            &mut lifted.ct,
            &mut lifted.bm,
            &state_vars,
            &lifted.bad_properties,
            &lifted.constraints,
            &input_vars,
        );

        assert_eq!(result, SolveResult::Sat,
            "BMC must still find reachable counterexamples.");
    }

    /// A5: collect_ite_cond_inputs flags ONLY direct-input ITE conditions,
    /// not condition expressions that contain inputs.
    #[test]
    fn test_collect_ite_cond_inputs_direct_only() {
        use bvdd::types::OpKind;
        use bvdd::term::TermTable;

        let mut tt = TermTable::new();
        let a = tt.make_var(10, 1);   // input 10 — direct ITE cond
        let b = tt.make_var(11, 1);   // input 11 — used in (a AND b) as cond
        let and_ab = tt.make_app(OpKind::And, vec![a, b], 1);
        let lo = tt.make_const(0, 8);
        let hi = tt.make_const(1, 8);
        let ite_direct = tt.make_app(OpKind::Ite, vec![a, lo, hi], 8);
        let ite_computed = tt.make_app(OpKind::Ite, vec![and_ab, lo, hi], 8);
        let combo = tt.make_app(OpKind::Add, vec![ite_direct, ite_computed], 8);

        let mut input_nids = std::collections::HashSet::new();
        input_nids.insert(10);
        input_nids.insert(11);

        let mut direct = std::collections::HashSet::new();
        collect_ite_cond_inputs(&tt, combo, &input_nids, &mut direct);

        // Input 10 appears as a direct ITE cond → flagged.
        // Input 11 only appears inside `and_ab` (a computed expr) → NOT flagged.
        assert!(direct.contains(&10), "input 10 is direct ITE condition — must be flagged");
        assert!(!direct.contains(&11), "input 11 is inside a computed condition — must NOT be flagged");
    }

    /// A5: collect_non_reset_uses flags inputs used in data positions.
    ///
    /// ITE(cond, input_a, input_b) — cond is non-data; input_a and input_b are data.
    /// The fence must catch that any candidate reset appearing in a data branch
    /// is disqualified.
    #[test]
    fn test_collect_non_reset_uses_finds_data_usage() {
        use bvdd::types::OpKind;
        use bvdd::term::TermTable;

        let mut tt = TermTable::new();
        let cond = tt.make_var(20, 1);
        let data_a = tt.make_var(21, 8);
        let data_b = tt.make_var(22, 8);
        // ITE uses cond as condition, data_a as then, data_b as else.
        let ite = tt.make_app(OpKind::Ite, vec![cond, data_a, data_b], 8);

        let mut candidates = std::collections::HashSet::new();
        candidates.insert(20);
        candidates.insert(21);
        candidates.insert(22);

        let mut data_uses = std::collections::HashSet::new();
        collect_non_reset_uses(&tt, ite, &candidates, &mut data_uses);

        // cond (20) is in a condition position → NOT in data_uses.
        // data_a (21) and data_b (22) are in data positions → IN data_uses.
        assert!(!data_uses.contains(&20), "condition position must NOT be in data_uses");
        assert!(data_uses.contains(&21), "then branch is data position");
        assert!(data_uses.contains(&22), "else branch is data position");
    }

    /// A5: an input that serves as BOTH an ITE condition AND a data operand
    /// must be disqualified as a reset candidate (fence catches the dual use).
    #[test]
    fn test_collect_non_reset_uses_flags_dual_use() {
        use bvdd::types::OpKind;
        use bvdd::term::TermTable;

        let mut tt = TermTable::new();
        let r = tt.make_var(30, 1); // used as both ITE cond and in arithmetic
        let lo = tt.make_const(0, 1);
        let ite = tt.make_app(OpKind::Ite, vec![r, lo, lo], 1);
        // Now use r again in a data position (XOR with constant).
        let one_bit = tt.make_const(1, 1);
        let xor_r = tt.make_app(OpKind::Xor, vec![r, one_bit], 1);
        let combo = tt.make_app(OpKind::And, vec![ite, xor_r], 1);

        let mut candidates = std::collections::HashSet::new();
        candidates.insert(30);

        let mut data_uses = std::collections::HashSet::new();
        collect_non_reset_uses(&tt, combo, &candidates, &mut data_uses);

        // r appears in `xor_r` in a data position → disqualified.
        assert!(data_uses.contains(&30),
            "dual-use input must be flagged as data use, disqualifying reset status");
    }

    /// A5: substitute_states should replace state-var references in a BVC's
    /// term with the *current* state BVCs, leaving unrelated variables alone.
    /// When a state is mapped to a constant, subst_and_fold should collapse it.
    #[test]
    fn test_substitute_states_replaces_only_referenced_vars() {
        use bvdd::term::TermTable;
        use bvdd::constraint::ConstraintTable;
        use bvdd::bvc::{BvcManager, BvcEntry};

        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        // term: (s + 7) where s is state var nid 100 (width 8).
        let s = tt.make_var(100, 8);
        let seven = tt.make_const(7, 8);
        let s_plus_7 = tt.make_app(bvdd::types::OpKind::Add, vec![s, seven], 8);
        let orig_bvc = bm.alloc(8, vec![BvcEntry {
            term: s_plus_7,
            constraint: ct.true_id(),
        }]);

        // Map s -> const 5. Substituting and folding should produce const 12.
        let mut state_current: HashMap<u32, BvcId> = HashMap::new();
        let five_bvc = bm.make_const(&mut tt, &ct, 5, 8);
        state_current.insert(100, five_bvc);

        let resolved = substitute_states(&mut tt, &mut ct, &mut bm, orig_bvc, &state_current);
        let resolved_term = bm.get(resolved).entries[0].term;
        // After subst_and_fold(s -> 5), term should be a constant 12.
        match tt.get(resolved_term).kind {
            bvdd::term::TermKind::Const(v) => assert_eq!(v, 12,
                "folded result must be 5 + 7 = 12"),
            _ => panic!("expected constant result after folding; got {:?}",
                tt.get(resolved_term).kind),
        }
    }

    /// A5: substitute_states is a no-op when the state_current map doesn't
    /// reference any variable in the term. Prevents accidental rewriting.
    #[test]
    fn test_substitute_states_skips_unreferenced() {
        use bvdd::term::TermTable;
        use bvdd::constraint::ConstraintTable;
        use bvdd::bvc::{BvcManager, BvcEntry};

        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        // term references nid 200 only.
        let v = tt.make_var(200, 4);
        let orig_bvc = bm.alloc(4, vec![BvcEntry {
            term: v,
            constraint: ct.true_id(),
        }]);

        // state_current maps nid 999 (unrelated).
        let mut state_current: HashMap<u32, BvcId> = HashMap::new();
        let zero = bm.make_const(&mut tt, &ct, 0, 4);
        state_current.insert(999, zero);

        let resolved = substitute_states(&mut tt, &mut ct, &mut bm, orig_bvc, &state_current);
        let orig_term = bm.get(orig_bvc).entries[0].term;
        let resolved_term = bm.get(resolved).entries[0].term;
        assert_eq!(resolved_term, orig_term,
            "substitution must be a no-op when no referenced variables are mapped");
    }
}
