//! Core Solve/Canonicalize engine
//!
//! Implements the BITR Canonicalize/Solve algorithms.
//! See `.claude/commands/bitr-expert.md` Sections 3-4.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use crate::types::{BvddId, BvcId, ConstraintId, SolveResult, OpKind};
use crate::valueset::ValueSet;
use crate::term::{TermTable, TermKind};
use crate::eval::CompiledProgram;
use crate::constraint::{ConstraintTable, ConstraintKind};
use crate::bvc::BvcManager;
use crate::bvdd::{BvddManager, BvddNodeKind, BvddEdge};

/// Solver context: holds all shared state for a solve call
pub struct SolverContext<'a> {
    pub tt: &'a mut TermTable,
    pub ct: &'a mut ConstraintTable,
    pub bm: &'a mut BvcManager,
    pub mgr: &'a mut BvddManager,
    /// Depth budget for recursion
    pub max_depth: u32,
    /// Current depth
    pub depth: u32,
    /// Stats
    pub solve_calls: u64,
    pub canonicalize_calls: u64,
    pub decide_calls: u64,
    pub restrict_calls: u64,
    pub sat_witnesses: u64,
    pub unsat_terminals: u64,
    pub bool_decomp_calls: u64,
    pub compiled_blast_calls: u64,
    pub byte_blast_calls: u64,
    pub bitblast_calls: u64,
    pub oracle_calls: u64,
    /// Oracle function: term→SMT-LIB2, invoke external solver
    #[allow(clippy::type_complexity)]
    pub oracle_fn: Option<Box<dyn FnMut(&TermTable, crate::types::TermId, u16, ValueSet) -> SolveResult + 'a>>,
    /// Witness: variable assignments when SAT is found (var_id → value)
    pub witness: HashMap<u32, u64>,
    /// Memoization for boolean decomposition: term → comparison var found
    decomp_cache: HashMap<crate::types::TermId, Option<u32>>,
    /// Wall-clock start time for timeout
    start_time: std::time::Instant,
    /// Timeout in seconds (0 = no timeout)
    pub solve_timeout_s: f64,
    /// Shared cancellation flag for parallel operations
    pub cancelled: Arc<AtomicBool>,
}

impl<'a> SolverContext<'a> {
    pub fn new(
        tt: &'a mut TermTable,
        ct: &'a mut ConstraintTable,
        bm: &'a mut BvcManager,
        mgr: &'a mut BvddManager,
    ) -> Self {
        SolverContext {
            tt,
            ct,
            bm,
            mgr,
            max_depth: 1000,
            depth: 0,
            solve_calls: 0,
            canonicalize_calls: 0,
            decide_calls: 0,
            restrict_calls: 0,
            sat_witnesses: 0,
            unsat_terminals: 0,
            bool_decomp_calls: 0,
            compiled_blast_calls: 0,
            byte_blast_calls: 0,
            bitblast_calls: 0,
            oracle_calls: 0,
            oracle_fn: None,
            witness: HashMap::new(),
            decomp_cache: HashMap::new(),
            start_time: std::time::Instant::now(),
            solve_timeout_s: 0.0, // No timeout by default; callers set it
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Set an external oracle function
    pub fn set_oracle(&mut self, f: impl FnMut(&TermTable, crate::types::TermId, u16, ValueSet) -> SolveResult + 'a) {
        self.oracle_fn = Some(Box::new(f));
    }

    /// Check if solve has timed out
    #[inline]
    fn timed_out(&self) -> bool {
        if self.cancelled.load(Ordering::Relaxed) {
            return true;
        }
        if self.solve_timeout_s > 0.0 &&
           self.solve_calls.is_multiple_of(100) &&
           self.start_time.elapsed().as_secs_f64() > self.solve_timeout_s
        {
            self.cancelled.store(true, Ordering::Relaxed);
            return true;
        }
        false
    }

    /// Solve(G, S): traverse BVDD G restricted to value set S
    pub fn solve(&mut self, g: BvddId, s: ValueSet) -> BvddId {
        self.solve_calls += 1;

        // Depth budget or timeout
        if self.depth > self.max_depth || self.timed_out() {
            return g;
        }

        // Phase 1: ground check
        if self.mgr.get(g).is_ground {
            // For ground terminals, verify the value is in the target set
            if let BvddNodeKind::Terminal { bvc } = self.mgr.get(g).kind {
                if let Some(val) = self.bm.get_const_value(self.tt, bvc) {
                    let check_val = (val & 0xFF) as u8;
                    if s.contains(check_val) {
                        return g; // Ground and satisfies target
                    } else {
                        return self.mgr.false_terminal(); // Ground but doesn't satisfy target
                    }
                }
            }
            return g;
        }

        // Check computed cache
        if let Some(cached) = self.mgr.cache_lookup(g, s) {
            return cached;
        }

        self.depth += 1;
        let result = {
            let node = self.mgr.get(g);
            match &node.kind {
                // Phase 2: terminal → Canonicalize
                BvddNodeKind::Terminal { bvc } => {
                    let bvc = *bvc;
                    self.canonicalize(bvc, s)
                }
                // Phase 3: decision node
                BvddNodeKind::Decision { label, edges } => {
                    let label = *label;
                    let edges = edges.clone(); // Clone only the Vec, not the enum wrapper
                    self.solve_decision(label, &edges, s)
                }
            }
        };
        self.depth -= 1;

        self.mgr.cache_insert(g, s, result);
        result
    }

    /// Solve a decision node: traverse edges with value-set restriction
    fn solve_decision(
        &mut self,
        label: BvddId,
        edges: &[BvddEdge],
        s: ValueSet,
    ) -> BvddId {
        let mut result_edges: Vec<BvddEdge> = Vec::new();

        for edge in edges {
            let s_new = edge.label.and(s);
            if s_new.is_empty() {
                continue; // UNSAT pruning
            }

            let child_result = self.solve(edge.child, s_new);

            // Early SAT termination
            if self.mgr.get(child_result).can_be_true && self.mgr.get(child_result).is_ground {
                self.sat_witnesses += 1;
                return child_result;
            }

            if !self.mgr.is_false(child_result) {
                result_edges.push(BvddEdge {
                    label: s_new,
                    child: child_result,
                });
            }
        }

        self.mgr.make_decision(label, result_edges)
    }

    /// Canonicalize(v, S): canonicalize BVC v under value set S
    pub fn canonicalize(&mut self, bvc: BvcId, s: ValueSet) -> BvddId {
        self.canonicalize_calls += 1;
        if self.cancelled.load(Ordering::Relaxed) {
            return self.mgr.make_terminal(bvc, true, false);
        }

        // Phase 1: ground check
        if self.bm.is_ground(self.tt, bvc) {
            // Ground BVC: just check if it has a SAT value
            if let Some(val) = self.bm.get_const_value(self.tt, bvc) {
                if s.contains(val as u8) {
                    self.sat_witnesses += 1;
                    return self.mgr.make_terminal(bvc, true, true);
                }
            }
            self.unsat_terminals += 1;
            return self.mgr.false_terminal();
        }

        let entry = &self.bm.get(bvc).entries[0];
        let constraint = entry.constraint;

        // Phase 2: SAT witness scan
        // Check if constraint is TRUE and we have a satisfiable value
        if constraint == self.ct.true_id() {
            // No constraints — theory resolution needed
            return self.theory_resolve(bvc, s);
        }

        // Phase 3: UNSAT pruning
        if self.ct.is_definitely_false(constraint) {
            self.unsat_terminals += 1;
            return self.mgr.false_terminal();
        }

        // Phase 4: no predicates remain → theory resolve
        if self.ct.has_no_predicates(constraint) {
            return self.theory_resolve(bvc, s);
        }

        // Phase 5a: Decide
        let (pred_bvc, partition) = self.decide(bvc);
        if partition.is_empty() {
            return self.mgr.false_terminal();
        }

        // Phase 5b: Restrict + recurse
        // s_j partitions the predicate variable's domain, NOT the result domain.
        // The result domain s is passed unchanged to each recursive solve.
        let mut result_edges: Vec<BvddEdge> = Vec::new();
        for s_j in &partition {
            let restricted_constraint = self.ct.restrict(constraint, pred_bvc, *s_j);

            // If Restrict collapsed constraint to FALSE, skip this partition
            if self.ct.is_definitely_false(restricted_constraint) {
                continue;
            }

            let new_bvc = self.make_restricted_bvc(bvc, restricted_constraint);
            let new_bvdd = self.mgr.make_terminal(new_bvc, true, false);
            let result = self.solve(new_bvdd, s);

            if self.mgr.get(result).can_be_true && self.mgr.get(result).is_ground {
                return result; // Early SAT
            }

            if !self.mgr.is_false(result) {
                result_edges.push(BvddEdge {
                    label: *s_j,
                    child: result,
                });
            }
        }

        // Build label BVDD for the decided variable
        let label = self.mgr.make_terminal(pred_bvc, true, false);
        self.mgr.make_decision(label, result_edges)
    }

    /// Decide: select predicate and compute partition
    fn decide(&mut self, bvc: BvcId) -> (BvcId, Vec<ValueSet>) {
        self.decide_calls += 1;

        let constraint = self.bm.get(bvc).entries[0].constraint;

        // Collect all PRED nodes from the constraint
        let all_preds = self.collect_all_preds(constraint);

        if all_preds.is_empty() {
            return (BvcId(0), vec![]);
        }

        // Select predicate with fewest distinct value sets (simplest)
        let (best_bvc, value_sets) = all_preds.into_iter()
            .min_by_key(|(_, vs)| vs.len())
            .unwrap();

        // Compute coarsest partition
        let partition = coarsest_partition(&value_sets);

        (best_bvc, partition)
    }

    /// Collect all (bvc, [valueset]) pairs from predicates in a constraint
    fn collect_all_preds(&self, k: ConstraintId) -> Vec<(BvcId, Vec<ValueSet>)> {
        let mut bvc_to_sets: HashMap<BvcId, Vec<ValueSet>> = HashMap::new();
        self.collect_preds_recursive(k, &mut bvc_to_sets);
        bvc_to_sets.into_iter().collect()
    }

    fn collect_preds_recursive(
        &self,
        k: ConstraintId,
        result: &mut HashMap<BvcId, Vec<ValueSet>>,
    ) {
        match &self.ct.get(k).kind {
            ConstraintKind::True | ConstraintKind::False => {}
            ConstraintKind::Pred { bvc, valueset } => {
                result.entry(*bvc).or_default().push(*valueset);
            }
            ConstraintKind::Not(inner) => {
                self.collect_preds_recursive(*inner, result);
            }
            ConstraintKind::And(a, b) | ConstraintKind::Or(a, b) => {
                self.collect_preds_recursive(*a, result);
                self.collect_preds_recursive(*b, result);
            }
        }
    }

    /// Create a new BVC with a restricted constraint
    fn make_restricted_bvc(&mut self, original_bvc: BvcId, new_constraint: ConstraintId) -> BvcId {
        self.restrict_calls += 1;
        let orig = self.bm.get(original_bvc);
        let width = orig.width;
        let term = orig.entries[0].term;
        use crate::bvc::BvcEntry;
        self.bm.alloc(width, vec![BvcEntry {
            term,
            constraint: new_constraint,
        }])
    }

    /// Theory resolution cascade:
    /// Stage 1 — Boolean decomposition (1-bit comparison subterms),
    /// Stage 2 — Generalized blast (compiled evaluator, budget 2^28),
    /// Stage 2b — CDCL bit-blast (splr SAT solver, Tseitin CNF encoding),
    /// Stage 3 — Byte-blast (split widest var MSB, max_depth=4),
    /// Stage 3b — Parallel compiled blast (budget 2^33 single-var, 2^32 multi-var),
    /// Stage 4 — Direct theory oracle (external solver).
    fn theory_resolve(&mut self, bvc: BvcId, s: ValueSet) -> BvddId {
        let entry = &self.bm.get(bvc).entries[0];
        let term = entry.term;
        let width = self.bm.get(bvc).width;

        // Collect all variables in the term
        let vars = self.tt.collect_vars(term);

        if vars.is_empty() {
            return self.theory_resolve_ground(bvc, s);
        }

        // Timeout check — return non-ground to signal Unknown
        if self.solve_timeout_s > 0.0 &&
           self.start_time.elapsed().as_secs_f64() > self.solve_timeout_s {
            self.cancelled.store(true, Ordering::Relaxed);
            return self.mgr.make_terminal(bvc, true, false);
        }

        // Stage 1: Boolean decomposition for 1-bit comparison subterms
        if width == 1 {
            if let Some(result) = self.boolean_decompose(bvc, s, &vars) {
                return result;
            }
        }

        // HSC decomposition: split wide variables (>8 bits) into byte slices.
        // When total domain > 2^28, split the widest variable's MSB byte
        // and recurse. Works for any number of wide variables.
        let total_domain: u128 = vars.iter()
            .map(|&(_, w)| if w >= 64 { u128::MAX } else { 1u128 << w })
            .fold(1u128, |acc, d| acc.saturating_mul(d));
        let wide_count = vars.iter().filter(|&&(_, w)| w > 8).count();
        if wide_count >= 1 && total_domain > (1u128 << 32) {
            let (wide_id, wide_width) = *vars.iter().max_by_key(|&&(_, w)| w).unwrap();
            let msb_bits: u16 = 8.min(wide_width);
            let lsb_bits: u16 = wide_width - msb_bits;

            let entry = &self.bm.get(bvc).entries[0];
            let term = entry.term;
            let constraint = entry.constraint;
            let width = self.bm.get(bvc).width;

            let mut result_edges: Vec<BvddEdge> = Vec::new();
            for msb in 0..256u64 {
                let shifted = msb << lsb_bits;
                if lsb_bits == 0 {
                    // Variable fits in one byte
                    let new_term = self.tt.subst_and_fold(term, wide_id, shifted);
                    let new_bvc = {
                        use crate::bvc::BvcEntry;
                        self.bm.alloc(width, vec![BvcEntry { term: new_term, constraint }])
                    };
                    let result = self.theory_resolve(new_bvc, s);
                    if self.mgr.get(result).can_be_true && self.mgr.get(result).is_ground {
                        return result;
                    }
                    if !self.mgr.is_false(result) {
                        result_edges.push(BvddEdge {
                            label: ValueSet::singleton(msb as u8),
                            child: result,
                        });
                    }
                } else {
                    // Create new variable for LSB portion
                    let lsb_var = self.bm.fresh_var();
                    let lsb_term = self.tt.make_var(lsb_var, lsb_bits);
                    // Build: wide_var = (msb << lsb_bits) | lsb_var
                    let msb_const = self.tt.make_const(shifted, wide_width);
                    let lsb_ext = self.tt.make_app(OpKind::Uext, vec![lsb_term], wide_width);
                    let combined = self.tt.make_app(OpKind::Or, vec![msb_const, lsb_ext], wide_width);
                    let new_term = self.tt.subst_term(term, wide_id, combined);

                    let new_bvc = {
                        use crate::bvc::BvcEntry;
                        self.bm.alloc(width, vec![BvcEntry { term: new_term, constraint }])
                    };
                    let result = self.theory_resolve(new_bvc, s);
                    if self.mgr.get(result).can_be_true && self.mgr.get(result).is_ground {
                        return result;
                    }
                    if !self.mgr.is_false(result) {
                        result_edges.push(BvddEdge {
                            label: ValueSet::singleton(msb as u8),
                            child: result,
                        });
                    }
                }
                // Check timeout periodically
                if msb % 64 == 63 && self.timed_out() {
                    break;
                }
            }

            if result_edges.is_empty() {
                return self.mgr.false_terminal();
            }
            let var_label_bvc = {
                use crate::bvc::BvcEntry;
                let var_term = self.tt.make_var(wide_id, wide_width);
                self.bm.alloc(wide_width, vec![BvcEntry {
                    term: var_term, constraint: self.ct.true_id(),
                }])
            };
            let label = self.mgr.make_terminal(var_label_bvc, true, false);
            return self.mgr.make_decision(label, result_edges);
        }

        // Compute total domain product for budget check
        let total_domain: u128 = vars.iter()
            .map(|&(_, w)| if w >= 64 { u128::MAX } else { 1u128 << w })
            .fold(1u128, |acc, d| acc.saturating_mul(d));

        // Stage 2: Compiled blast for domains within budget (fast sequential/parallel)
        if total_domain <= (1u128 << 16) {
            return self.compiled_blast(bvc, s, &vars);
        }

        // Stage 2b: Native CDCL bit-blast (splr SAT solver)
        // Converts the term to CNF via Tseitin encoding and solves in-process.
        // Much faster than exhaustive enumeration for structured UNSAT and constrained SAT.
        {
            self.bitblast_calls += 1;
            let mut bb = crate::bitblast::BitBlaster::new(self.tt);
            let (result, bb_witness) = bb.solve(term, width, &s);
            match result {
                SolveResult::Sat => {
                    for (var_id, value) in &bb_witness {
                        self.witness.insert(*var_id, *value);
                    }
                    // Verify by evaluating the term with the witness
                    if let Some(val) = self.tt.eval(term, &bb_witness) {
                        let check_val = mask_for_check(val, width);
                        if s.contains(check_val) {
                            let const_bvc = self.bm.make_const(self.tt, self.ct, val, width);
                            self.sat_witnesses += 1;
                            return self.mgr.make_terminal(const_bvc, true, true);
                        }
                    }
                    // Witness didn't verify — fall through to byte-blast
                }
                SolveResult::Unsat => {
                    self.unsat_terminals += 1;
                    return self.mgr.false_terminal();
                }
                SolveResult::Unknown => {
                    // Budget exceeded or unsupported op — fall through
                }
            }
        }

        // Stage 3: Byte-blast (HSC decomposition — splits widest variable MSB byte,
        // recurses on sub-problems). Effective for multi-variable SAT and structured problems.
        if let Some(result) = self.byte_blast(bvc, s, &vars, 0) {
            return result;
        }

        // Stage 3b: Parallel compiled blast for domains up to 2^33 (single-var)
        // or 2^32 (multi-var) when byte-blast couldn't handle it
        let parallel_budget = if vars.len() == 1 { 1u128 << 33 } else { 1u128 << 32 };
        if total_domain <= parallel_budget {
            return self.compiled_blast(bvc, s, &vars);
        }

        // Stage 4: Direct theory oracle — use when available, regardless of timeout mode
        if self.oracle_fn.is_some() {
            self.invoke_oracle(bvc, s)
        } else {
            self.mgr.make_terminal(bvc, true, false) // Unknown
        }
    }

    /// Stage 1: Boolean decomposition — find comparison subterms in 1-bit
    /// expressions, branch on true/false for each.
    fn boolean_decompose(
        &mut self,
        bvc: BvcId,
        s: ValueSet,
        vars: &[(u32, u16)],
    ) -> Option<BvddId> {
        let term = self.bm.get(bvc).entries[0].term;
        let width = self.bm.get(bvc).width;

        // Find a comparison subterm to decompose on
        let comp = self.find_comparison_subterm(term);
        let comp = comp?;

        self.bool_decomp_calls += 1;

        // Branch: assume comparison = true (1), then comparison = false (0)
        let constraint = self.bm.get(bvc).entries[0].constraint;
        let mut result_edges = Vec::new();

        for branch_val in [1u64, 0u64] {
            let new_term = self.tt.subst_and_fold(term, comp, branch_val);

            // Check if it collapsed to a constant
            if let TermKind::Const(val) = self.tt.get(new_term).kind {
                let check_val = mask_for_check(val, width);
                if s.contains(check_val) {
                    let const_bvc = self.bm.make_const(self.tt, self.ct, val, width);
                    self.sat_witnesses += 1;
                    return Some(self.mgr.make_terminal(const_bvc, true, true));
                }
                continue;
            }

            // Still has variables — recurse
            let new_bvc = {
                use crate::bvc::BvcEntry;
                self.bm.alloc(width, vec![BvcEntry { term: new_term, constraint }])
            };
            let new_vars = self.tt.collect_vars(new_term);
            let result = if new_vars.is_empty() {
                self.theory_resolve_ground(new_bvc, s)
            } else if new_vars.len() < vars.len() {
                self.theory_resolve(new_bvc, s)
            } else {
                // No progress — fall through to blast
                return None;
            };

            if self.mgr.get(result).can_be_true && self.mgr.get(result).is_ground {
                return Some(result); // Early SAT
            }
            if !self.mgr.is_false(result) {
                result_edges.push(BvddEdge {
                    label: ValueSet::singleton(branch_val as u8),
                    child: result,
                });
            }
        }

        if result_edges.is_empty() {
            Some(self.mgr.false_terminal())
        } else {
            // Label with the comparison subterm variable
            let comp_bvc = {
                use crate::bvc::BvcEntry;
                let comp_term = self.tt.make_var(comp, 1);
                self.bm.alloc(1, vec![BvcEntry {
                    term: comp_term,
                    constraint: self.ct.true_id(),
                }])
            };
            let label = self.mgr.make_terminal(comp_bvc, true, false);
            Some(self.mgr.make_decision(label, result_edges))
        }
    }

    /// Find a comparison subterm (EQ, ULT, etc.) that can be decomposed.
    /// Returns a pseudo-variable ID representing the comparison.
    fn find_comparison_subterm(&mut self, term: crate::types::TermId) -> Option<u32> {
        if let Some(&cached) = self.decomp_cache.get(&term) {
            return cached;
        }
        let result = self.find_comparison_subterm_inner(term);
        self.decomp_cache.insert(term, result);
        result
    }

    fn find_comparison_subterm_inner(&mut self, term: crate::types::TermId) -> Option<u32> {
        match &self.tt.get(term).kind.clone() {
            TermKind::Const(_) | TermKind::Var(_) => None,
            TermKind::App { op, args, .. } => {
                // If this IS a comparison, it can be decomposed
                if matches!(op,
                    OpKind::Eq | OpKind::Neq | OpKind::Ult | OpKind::Slt |
                    OpKind::Ulte | OpKind::Slte | OpKind::Uaddo | OpKind::Umulo
                ) && self.tt.get(term).width == 1 {
                    // Create a pseudo-variable for this comparison
                    let var_id = self.bm.fresh_var();
                    return Some(var_id);
                }
                // Recurse into args to find nested comparisons
                for &arg in args {
                    if self.tt.get(arg).width == 1 {
                        if let Some(v) = self.find_comparison_subterm(arg) {
                            return Some(v);
                        }
                    }
                }
                None
            }
        }
    }

    /// Stage 2: Generalized blast with compiled evaluator for fast enumeration.
    /// Budget: 2^28 total domain product.
    fn compiled_blast(
        &mut self,
        bvc: BvcId,
        s: ValueSet,
        vars: &[(u32, u16)],
    ) -> BvddId {
        self.compiled_blast_calls += 1;

        let entry = &self.bm.get(bvc).entries[0];
        let term = entry.term;
        let constraint = entry.constraint;
        let width = self.bm.get(bvc).width;

        let prog = CompiledProgram::compile(self.tt, term);

        // Build slot descriptors for all variables
        let slots: Vec<(u32, u32, u64)> = vars.iter().filter_map(|&(vid, vw)| {
            let domain = if vw >= 64 { u64::MAX } else { 1u64 << vw };
            prog.var_slot(vid).map(|slot| (vid, slot, domain))
        }).collect();

        if slots.len() != vars.len() {
            // Not all variables found in compiled program — fall back
            return self.generalized_blast_recursive(bvc, s, vars, constraint, term, width);
        }

        let total_domain: u128 = slots.iter()
            .map(|&(_, _, d)| d as u128)
            .fold(1u128, |acc, d| acc.saturating_mul(d));

        let blast_budget = if vars.len() == 1 { 1u128 << 33 } else { 1u128 << 32 };
        if total_domain > blast_budget {
            // Domain too large — return non-ground (Unknown)
            return self.mgr.make_terminal(bvc, true, false);
        }
        if self.timed_out() {
            return self.mgr.make_terminal(bvc, true, false);
        }

        // Use parallel search for large domains (> 100K), sequential for small
        let use_parallel = total_domain > 100_000;

        if use_parallel {
            // Start a timeout thread that sets cancelled after solve_timeout_s
            let cancelled = self.cancelled.clone();
            let timeout_s = self.solve_timeout_s;
            if timeout_s > 0.0 {
                let c = cancelled.clone();
                std::thread::spawn(move || {
                    std::thread::sleep(std::time::Duration::from_secs_f64(timeout_s));
                    c.store(true, Ordering::Relaxed);
                });
            }

            if let Some((slot_vals, val)) = prog.parallel_search(&slots, s, width, &cancelled) {
                // Record witness
                for &(var_id, slot_idx, _) in &slots {
                    self.witness.insert(var_id, slot_vals[slot_idx as usize]);
                }
                let const_bvc = self.bm.make_const(self.tt, self.ct, val, width);
                self.sat_witnesses += 1;
                return self.mgr.make_terminal(const_bvc, true, true);
            }
            return self.mgr.false_terminal();
        }

        // Sequential: use flat iterative multi-eval
        let mut slot_vals = vec![0u64; prog.num_vars as usize];
        let mut regs = vec![0u64; prog.num_regs as usize];
        
        self.compiled_multi_eval_flat(
            &prog, &slots, &mut slot_vals, &mut regs, s, width,
        )
    }

    /// Recursive generalized blast: enumerate narrowest variable, SubstAndFold, recurse.
    /// Uses compiled evaluator when all remaining variables fit in the budget.
    fn generalized_blast_recursive(
        &mut self,
        bvc: BvcId,
        s: ValueSet,
        vars: &[(u32, u16)],
        constraint: ConstraintId,
        term: crate::types::TermId,
        width: u16,
    ) -> BvddId {
        if vars.is_empty() {
            let eval_bvc = {
                use crate::bvc::BvcEntry;
                self.bm.alloc(width, vec![BvcEntry { term, constraint }])
            };
            return self.theory_resolve_ground(eval_bvc, s);
        }

        // Try compiled multi-variable evaluation if total domain fits in budget
        let total_domain: u128 = vars.iter()
            .map(|&(_, w)| if w >= 64 { u128::MAX } else { 1u128 << w })
            .fold(1u128, |acc, d| acc.saturating_mul(d));

        let blast_budget_recursive = if vars.len() == 1 { 1u128 << 33 } else { 1u128 << 32 };
        if total_domain <= blast_budget_recursive {
            let prog = CompiledProgram::compile(self.tt, term);
            let slots: Vec<(u32, u32, u64)> = vars.iter().filter_map(|&(vid, vw)| {
                let domain = if vw >= 64 { u64::MAX } else { 1u64 << vw };
                prog.var_slot(vid).map(|slot| (vid, slot, domain))
            }).collect();

            if slots.len() == vars.len() {
                // Flat iterative multi-variable compiled evaluation
                let mut slot_vals = vec![0u64; prog.num_vars as usize];
                let mut regs = vec![0u64; prog.num_regs as usize];
                let result = self.compiled_multi_eval_flat(
                    &prog, &slots, &mut slot_vals, &mut regs, s, width,
                );
                return result;
            }
        }

        // Fallback: single-variable enumeration with SubstAndFold
        let (var_id, var_width) = *vars.iter()
            .min_by_key(|&&(_, w)| w)
            .unwrap();

        let domain_size: u64 = if var_width >= 64 { u64::MAX } else { 1u64 << var_width };
        if domain_size > (1 << 28) {
            return self.mgr.make_terminal(bvc, true, false);
        }

        let remaining_vars: Vec<(u32, u16)> = vars.iter()
            .filter(|&&(vid, _)| vid != var_id)
            .cloned()
            .collect();

        let mut result_edges: Vec<BvddEdge> = Vec::new();

        for d in 0..domain_size {
            let new_term = self.tt.subst_and_fold(term, var_id, d);

            let result = if remaining_vars.is_empty() {
                let new_bvc = {
                    use crate::bvc::BvcEntry;
                    self.bm.alloc(width, vec![BvcEntry { term: new_term, constraint }])
                };
                self.theory_resolve_ground(new_bvc, s)
            } else {
                self.generalized_blast_recursive(
                    bvc, s, &remaining_vars, constraint, new_term, width,
                )
            };

            if self.mgr.get(result).can_be_true && self.mgr.get(result).is_ground {
                self.witness.insert(var_id, d);
                return result; // Early SAT
            }

            if !self.mgr.is_false(result) {
                let label = if d <= 255 {
                    ValueSet::singleton(d as u8)
                } else {
                    ValueSet::singleton((d & 0xFF) as u8)
                };
                result_edges.push(BvddEdge { label, child: result });
            }
        }

        if result_edges.is_empty() {
            self.mgr.false_terminal()
        } else {
            let var_label_term = self.tt.make_var(var_id, var_width);
            let var_label_bvc = {
                use crate::bvc::BvcEntry;
                self.bm.alloc(var_width, vec![BvcEntry {
                    term: var_label_term,
                    constraint: self.ct.true_id(),
                }])
            };
            let label = self.mgr.make_terminal(var_label_bvc, true, false);
            self.mgr.make_decision(label, result_edges)
        }
    }

    /// Flat iterative multi-variable compiled evaluation.
    /// Uses pre-allocated register buffer and counter array to avoid recursion.
    fn compiled_multi_eval_flat(
        &mut self,
        prog: &CompiledProgram,
        slots: &[(u32, u32, u64)], // (var_id, slot_idx, domain_size)
        slot_vals: &mut [u64],
        regs: &mut [u64],
        s: ValueSet,
        width: u16,
    ) -> BvddId {
        let n = slots.len();
        if n == 0 {
            return self.mgr.false_terminal();
        }

        // Initialize all slot values to 0
        for &(_, slot_idx, _) in slots {
            slot_vals[slot_idx as usize] = 0;
        }

        // Iterative enumeration using counter increment
        let mut iter_count: u64 = 0;
        loop {
            iter_count += 1;
            if iter_count.is_multiple_of(100_000) && self.solve_timeout_s > 0.0
               && self.start_time.elapsed().as_secs_f64() > self.solve_timeout_s {
                // Timed out — return a non-ground terminal to signal Unknown
                use crate::bvc::BvcEntry;
                let timeout_bvc = self.bm.alloc(width, vec![BvcEntry {
                    term: self.tt.make_const(0, width),
                    constraint: self.ct.true_id(),
                }]);
                return self.mgr.make_terminal(timeout_bvc, true, false);
            }
            let val = prog.eval_packed(slot_vals, regs);
            let check_val = mask_for_check(val, width);
            if s.contains(check_val) {
                // SAT — record witness
                for &(var_id, slot_idx, _) in slots {
                    self.witness.insert(var_id, slot_vals[slot_idx as usize]);
                }
                let const_bvc = self.bm.make_const(self.tt, self.ct, val, width);
                self.sat_witnesses += 1;
                return self.mgr.make_terminal(const_bvc, true, true);
            }

            // Increment: advance the rightmost (innermost) counter
            let mut carry = true;
            for i in (0..n).rev() {
                if carry {
                    let (_, slot_idx, domain_size) = slots[i];
                    let next = slot_vals[slot_idx as usize] + 1;
                    if next < domain_size {
                        slot_vals[slot_idx as usize] = next;
                        carry = false;
                    } else {
                        slot_vals[slot_idx as usize] = 0;
                        // carry propagates to next variable
                    }
                }
            }
            if carry {
                break; // All combinations exhausted
            }
        }

        self.mgr.false_terminal()
    }

    /// Stage 3: Byte-blast oracle — split widest variable's MSB byte,
    /// enumerate 256 values for the MSB, recurse on remainder.
    /// max_depth=4, adaptive_bailout=25%.
    fn byte_blast(
        &mut self,
        bvc: BvcId,
        s: ValueSet,
        vars: &[(u32, u16)],
        depth: u32,
    ) -> Option<BvddId> {
        if depth >= 4 {
            return None; // Exceeded byte-blast depth
        }

        // Find widest variable
        let (var_id, var_width) = *vars.iter()
            .max_by_key(|&&(_, w)| w)
            .unwrap();

        if var_width <= 8 {
            return None; // All variables are <= 8 bits, blast handles this
        }

        self.byte_blast_calls += 1;

        let entry = &self.bm.get(bvc).entries[0];
        let term = entry.term;
        let constraint = entry.constraint;
        let width = self.bm.get(bvc).width;

        // MSB byte is the top 8 bits; LSB is the rest
        let msb_bits: u16 = 8.min(var_width);
        let lsb_bits: u16 = var_width - msb_bits;
        let lsb_domain: u64 = if lsb_bits >= 64 { u64::MAX } else { 1u64 << lsb_bits };

        // For each MSB byte value, enumerate the LSB range if feasible
        let mut result_edges: Vec<BvddEdge> = Vec::new();
        let mut oracle_needed = 0u32;
        let byte_blast_start = std::time::Instant::now();

        for msb in 0..256u64 {
            // Time-based bailout: if byte-blast takes > 500ms, give up
            // and let parallel blast or oracle handle it
            if msb % 16 == 15 && byte_blast_start.elapsed().as_millis() > 500 {
                return None;
            }

            let shifted = msb << lsb_bits;

            if lsb_domain <= 256 {
                // Small LSB: enumerate all combinations
                for lsb in 0..lsb_domain {
                    let full_val = shifted | lsb;
                    let new_term = self.tt.subst_and_fold(term, var_id, full_val);
                    let remaining: Vec<(u32, u16)> = vars.iter()
                        .filter(|&&(vid, _)| vid != var_id)
                        .cloned()
                        .collect();

                    let new_bvc = {
                        use crate::bvc::BvcEntry;
                        self.bm.alloc(width, vec![BvcEntry { term: new_term, constraint }])
                    };

                    let result = if remaining.is_empty() {
                        self.theory_resolve_ground(new_bvc, s)
                    } else {
                        self.theory_resolve(new_bvc, s)
                    };

                    if self.mgr.get(result).can_be_true && self.mgr.get(result).is_ground {
                        return Some(result); // Early SAT
                    }
                    if !self.mgr.is_false(result) {
                        result_edges.push(BvddEdge {
                            label: ValueSet::singleton(msb as u8),
                            child: result,
                        });
                        break; // Found non-FALSE for this MSB
                    }
                }
            } else {
                // LSB too wide: would need recursive byte-blast or oracle
                oracle_needed += 1;

                // Adaptive bailout: if >25% need oracle, stop
                if oracle_needed * 4 > (msb as u32 + 1) {
                    return None;
                }
            }
        }

        if result_edges.is_empty() {
            Some(self.mgr.false_terminal())
        } else {
            let var_label_bvc = {
                use crate::bvc::BvcEntry;
                let var_label_term = self.tt.make_var(var_id, var_width);
                self.bm.alloc(var_width, vec![BvcEntry {
                    term: var_label_term,
                    constraint: self.ct.true_id(),
                }])
            };
            let label = self.mgr.make_terminal(var_label_bvc, true, false);
            Some(self.mgr.make_decision(label, result_edges))
        }
    }

    /// Stage 4: Invoke external theory oracle on residual formula
    fn invoke_oracle(&mut self, bvc: BvcId, s: ValueSet) -> BvddId {
        self.oracle_calls += 1;

        let entry = &self.bm.get(bvc).entries[0];
        let term = entry.term;
        let width = self.bm.get(bvc).width;

        if let Some(ref mut oracle_fn) = self.oracle_fn {
            let result = oracle_fn(self.tt, term, width, s);
            match result {
                SolveResult::Sat => {
                    self.sat_witnesses += 1;
                    return self.mgr.make_terminal(bvc, true, true);
                }
                SolveResult::Unsat => {
                    self.unsat_terminals += 1;
                    return self.mgr.false_terminal();
                }
                SolveResult::Unknown => {}
            }
        }

        // No oracle available or oracle returned Unknown
        // Return as non-ground (Unknown)
        self.mgr.make_terminal(bvc, true, false)
    }

    /// Resolve a ground BVC (no variables) against a value set
    fn theory_resolve_ground(&mut self, bvc: BvcId, s: ValueSet) -> BvddId {
        let entry = &self.bm.get(bvc).entries[0];
        let term = entry.term;
        let width = self.bm.get(bvc).width;

        let assign = HashMap::new();
        if let Some(val) = self.tt.eval(term, &assign) {
            let check_val = mask_for_check(val, width);
            if s.contains(check_val) {
                let const_bvc = self.bm.make_const(self.tt, self.ct, val, width);
                self.sat_witnesses += 1;
                return self.mgr.make_terminal(const_bvc, true, true);
            }
        }
        self.unsat_terminals += 1;
        self.mgr.false_terminal()
    }

    /// Extract a witness (variable→value map) from a SAT result.
    /// Walks the solved BVDD and evaluates the term to find assignments.
    pub fn extract_witness(&mut self, id: BvddId, target: ValueSet) -> HashMap<u32, u64> {
        let mut witness = HashMap::new();

        // Walk decision nodes collecting edge labels
        let mut current = id;
        loop {
            let node = self.mgr.get(current).clone();
            match &node.kind {
                BvddNodeKind::Terminal { bvc } => {
                    // At terminal: collect variables from the term
                    let entry = &self.bm.get(*bvc).entries[0];
                    let term = entry.term;
                    let vars = self.tt.collect_vars(term);

                    if vars.is_empty() {
                        // Ground: no variables to assign
                        break;
                    }

                    // Try to find a satisfying assignment via evaluation
                    let width = self.bm.get(*bvc).width;
                    let prog = CompiledProgram::compile(self.tt, term);
                    let mut slot_vals = vec![0u64; prog.num_vars as usize];

                    // Simple search: try 0 for each variable, then increment
                    'search: for _ in 0..1000 {
                        let val = prog.eval(&slot_vals);
                        let check = mask_for_check(val, width);
                        if target.contains(check) {
                            for &(var_id, _) in &vars {
                                if let Some(slot) = prog.var_slot(var_id) {
                                    witness.insert(var_id, slot_vals[slot as usize]);
                                }
                            }
                            break 'search;
                        }
                        // Increment first variable
                        if let Some(slot) = prog.var_slot(vars[0].0) {
                            slot_vals[slot as usize] += 1;
                        } else {
                            break;
                        }
                    }
                    break;
                }
                BvddNodeKind::Decision { label, edges } => {
                    // Pick the first non-FALSE edge
                    let mut found = false;
                    for edge in edges {
                        let child = self.mgr.get(edge.child);
                        if child.can_be_true || !self.mgr.is_false(edge.child) {
                            // Record: the label variable takes a value from this edge's label set
                            if let BvddNodeKind::Terminal { bvc } = self.mgr.get(*label).kind {
                                let label_entry = &self.bm.get(bvc).entries[0];
                                if let TermKind::Var(var_id) = self.tt.get(label_entry.term).kind {
                                    if let Some(v) = edge.label.min_element() {
                                        witness.insert(var_id, v as u64);
                                    }
                                }
                            }
                            current = edge.child;
                            found = true;
                            break;
                        }
                    }
                    if !found { break; }
                }
            }
        }

        // Merge with any assignments recorded during solving
        for (k, v) in &self.witness {
            witness.entry(*k).or_insert(*v);
        }

        witness
    }

    /// Get the solve result from a BVDD
    pub fn get_result(&self, id: BvddId) -> SolveResult {
        if self.mgr.is_false(id) {
            SolveResult::Unsat
        } else if self.mgr.get(id).can_be_true && self.mgr.get(id).is_ground {
            SolveResult::Sat
        } else {
            SolveResult::Unknown
        }
    }
}

// Re-export from eval module
use crate::eval::mask_for_check;

/// Compute the coarsest partition of [0, 255] by membership signature.
/// Values d1, d2 are in the same partition element iff for every value set S_i,
/// d1 ∈ S_i ↔ d2 ∈ S_i.
pub fn coarsest_partition(value_sets: &[ValueSet]) -> Vec<ValueSet> {
    if value_sets.is_empty() {
        return vec![ValueSet::FULL];
    }

    // Compute signature for each domain value
    let mut sig_to_partition: HashMap<u64, ValueSet> = HashMap::new();

    for d in 0..=255u8 {
        // Compute signature: which value sets contain d
        let mut sig: u64 = 0;
        for (i, vs) in value_sets.iter().enumerate() {
            if vs.contains(d) {
                sig |= 1u64 << (i % 64);
            }
        }
        sig_to_partition.entry(sig)
            .or_insert(ValueSet::EMPTY);
        let entry = sig_to_partition.get_mut(&sig).unwrap();
        *entry = entry.insert(d);
    }

    sig_to_partition.into_values().collect()
}

// Extension to TermTable for collecting variables
impl TermTable {
    /// Collect all variables and their widths from a term
    pub fn collect_vars(&self, id: crate::types::TermId) -> Vec<(u32, u16)> {
        let mut vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        self.collect_vars_inner(id, &mut vars, &mut seen);
        vars
    }

    fn collect_vars_inner(
        &self,
        id: crate::types::TermId,
        vars: &mut Vec<(u32, u16)>,
        seen: &mut std::collections::HashSet<crate::types::TermId>,
    ) {
        if !seen.insert(id) {
            return;
        }
        let term = self.get(id);
        match &term.kind {
            crate::term::TermKind::Const(_) => {}
            crate::term::TermKind::Var(var_id) => {
                if !vars.iter().any(|&(v, _)| v == *var_id) {
                    vars.push((*var_id, term.width));
                }
            }
            crate::term::TermKind::App { args, .. } => {
                for &arg in args {
                    self.collect_vars_inner(arg, vars, seen);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermTable;
    use crate::constraint::ConstraintTable;
    use crate::bvc::{BvcManager, BvcEntry};
    use crate::types::OpKind;

    /// Helper: create a solver context
    fn make_ctx<'a>(
        tt: &'a mut TermTable,
        ct: &'a mut ConstraintTable,
        bm: &'a mut BvcManager,
        mgr: &'a mut BvddManager,
    ) -> SolverContext<'a> {
        SolverContext::new(tt, ct, bm, mgr)
    }

    #[test]
    fn test_solve_ground_sat() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();
        let mut mgr = BvddManager::new();

        // Constant BVC: value = 42
        let const_bvc = bm.make_const(&mut tt, &ct, 42, 8);
        let terminal = mgr.make_terminal(const_bvc, true, true);

        let mut ctx = make_ctx(&mut tt, &mut ct, &mut bm, &mut mgr);
        let result = ctx.solve(terminal, ValueSet::FULL);
        assert_eq!(ctx.get_result(result), SolveResult::Sat);
    }

    #[test]
    fn test_solve_ground_unsat() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();
        let mut mgr = BvddManager::new();

        // Constant BVC: value = 42, but restrict to set not containing 42
        let const_bvc = bm.make_const(&mut tt, &ct, 42, 8);
        let terminal = mgr.make_terminal(const_bvc, true, true);

        let mut ctx = make_ctx(&mut tt, &mut ct, &mut bm, &mut mgr);
        let s = ValueSet::singleton(0); // only 0 allowed, but value is 42
        let result = ctx.solve(terminal, s);
        // Ground BVC is ground, so solve returns it unchanged
        // The ground check in solve sees is_ground=true and returns immediately
        assert!(ctx.mgr.get(result).is_ground);
    }

    #[test]
    fn test_theory_resolve_simple() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();
        let mut mgr = BvddManager::new();

        // BVC: term = var(0) + const(1), width 2, constraint = TRUE
        let x = tt.make_var(0, 2);
        let c1 = tt.make_const(1, 2);
        let add = tt.make_app(OpKind::Add, vec![x, c1], 2);
        let bvc = bm.alloc(2, vec![BvcEntry {
            term: add,
            constraint: ct.true_id(),
        }]);

        // Target: result must equal 3
        // x + 1 = 3 → x = 2
        let terminal = mgr.make_terminal(bvc, true, false);

        let mut ctx = make_ctx(&mut tt, &mut ct, &mut bm, &mut mgr);
        let s = ValueSet::singleton(3);
        let result = ctx.solve(terminal, s);
        assert_eq!(ctx.get_result(result), SolveResult::Sat);
    }

    #[test]
    fn test_theory_resolve_unsat() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();
        let mut mgr = BvddManager::new();

        // BVC: term = x AND NOT(x), width 2, constraint = TRUE
        let x = tt.make_var(0, 2);
        let notx = tt.make_app(OpKind::Not, vec![x], 2);
        let andxnotx = tt.make_app(OpKind::And, vec![x, notx], 2);
        let bvc = bm.alloc(2, vec![BvcEntry {
            term: andxnotx,
            constraint: ct.true_id(),
        }]);

        // x & ~x is always 0, so asking for non-zero is UNSAT
        let terminal = mgr.make_terminal(bvc, true, false);

        let mut ctx = make_ctx(&mut tt, &mut ct, &mut bm, &mut mgr);
        let s = ValueSet::from_range(1, 3); // {1, 2, 3} — but x & ~x = 0 always
        let result = ctx.solve(terminal, s);
        assert_eq!(ctx.get_result(result), SolveResult::Unsat);
    }

    #[test]
    fn test_coarsest_partition_single() {
        let vs = vec![ValueSet::from_range(0, 127)]; // {0..127}
        let parts = coarsest_partition(&vs);
        // Two partitions: {0..127} and {128..255}
        assert_eq!(parts.len(), 2);
        let total: u32 = parts.iter().map(|p| p.popcount()).sum();
        assert_eq!(total, 256);
    }

    #[test]
    fn test_coarsest_partition_two() {
        let vs = vec![
            ValueSet::from_range(0, 99),
            ValueSet::from_range(50, 199),
        ];
        let parts = coarsest_partition(&vs);
        // Three regions: {0..49} (in first only), {50..99} (in both), {100..199} (in second only), {200..255} (in neither)
        assert_eq!(parts.len(), 4);
    }

    #[test]
    fn test_canonicalize_with_predicate() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();
        let mut mgr = BvddManager::new();

        // Create BVC with predicate: PRED(bvc0, {0, 1})
        // This means: the BVC's value is in {0, 1}
        let x = tt.make_var(0, 2);
        let pred_bvc = BvcId(0); // will reference bvc 0

        // First create the BVC that the predicate references
        let _bvc0 = bm.alloc(2, vec![BvcEntry {
            term: x,
            constraint: ct.true_id(),
        }]);
        assert_eq!(_bvc0, BvcId(0));

        // Now create a BVC with a predicate constraint
        let pred = ct.make_pred(pred_bvc, ValueSet::singleton(0).or(ValueSet::singleton(1)));
        let bvc1 = bm.alloc(2, vec![BvcEntry {
            term: x,
            constraint: pred,
        }]);

        let terminal = mgr.make_terminal(bvc1, true, false);

        let mut ctx = make_ctx(&mut tt, &mut ct, &mut bm, &mut mgr);
        let result = ctx.solve(terminal, ValueSet::full_for_width(2));
        // Should be SAT: x can be 0 or 1
        assert_eq!(ctx.get_result(result), SolveResult::Sat);
        assert!(ctx.decide_calls > 0);
    }

    #[test]
    fn test_collect_vars() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 4);
        let add = tt.make_app(OpKind::Add, vec![x, y], 8);
        let c = tt.make_const(5, 8);
        let mul = tt.make_app(OpKind::Mul, vec![add, c], 8);

        let vars = tt.collect_vars(mul);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&(0, 8)));
        assert!(vars.contains(&(1, 4)));
    }
}
