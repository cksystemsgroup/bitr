use crate::types::{BvcId, TermId, ConstraintId, BvWidth, OpKind};
use crate::term::{TermTable, TermKind};
use crate::constraint::ConstraintTable;
use crate::valueset::ValueSet;

/// Compute the value set of domain values `d` that make `op(d, const_val)` true.
/// If `swapped`, computes for `op(const_val, d)` instead.
fn compute_comparison_valueset(op: OpKind, const_val: u64, width: BvWidth, swapped: bool) -> ValueSet {
    let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
    let cv = const_val & mask;

    ValueSet::from_fn(|d| {
        let dv = (d as u64) & mask;
        let (a, b) = if swapped { (cv, dv) } else { (dv, cv) };

        match op {
            OpKind::Eq => a == b,
            OpKind::Neq => a != b,
            OpKind::Ult => a < b,
            OpKind::Ulte => a <= b,
            OpKind::Slt => {
                let sa = sign_ext(a, width);
                let sb = sign_ext(b, width);
                sa < sb
            }
            OpKind::Slte => {
                let sa = sign_ext(a, width);
                let sb = sign_ext(b, width);
                sa <= sb
            }
            _ => true, // For non-comparison ops, don't constrain
        }
    })
}

/// Sign-extend for comparison value set computation
fn sign_ext(val: u64, width: BvWidth) -> i64 {
    if width == 0 { return 0; }
    if width >= 64 { return val as i64; }
    let sign_bit = 1u64 << (width - 1);
    if val & sign_bit != 0 {
        (val | !((1u64 << width) - 1)) as i64
    } else {
        val as i64
    }
}

/// A single BVC entry: (term, constraint)
#[derive(Debug, Clone)]
pub struct BvcEntry {
    pub term: TermId,
    pub constraint: ConstraintId,
}

/// A Bitvector Constraint: set of constrained terms
#[derive(Debug, Clone)]
pub struct Bvc {
    pub id: BvcId,
    pub width: BvWidth,
    pub entries: Vec<BvcEntry>,
}

/// BVC manager: arena for all BVCs with lifted variable support
#[derive(Clone)]
pub struct BvcManager {
    bvcs: Vec<Bvc>,
    /// Next fresh variable ID for lifted definitions
    next_lifted_var: u32,
}

impl Default for BvcManager {
    fn default() -> Self { Self::new() }
}

impl BvcManager {
    pub fn new() -> Self {
        BvcManager {
            bvcs: Vec::new(),
            next_lifted_var: 0x1000_0000, // High range to avoid collision with BTOR2 nids
        }
    }

    pub fn get(&self, id: BvcId) -> &Bvc {
        &self.bvcs[id.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.bvcs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bvcs.is_empty()
    }

    pub fn alloc(&mut self, width: BvWidth, entries: Vec<BvcEntry>) -> BvcId {
        let id = BvcId(self.bvcs.len() as u32);
        self.bvcs.push(Bvc { id, width, entries });
        id
    }

    /// Allocate a fresh lifted variable ID
    pub fn fresh_var(&mut self) -> u32 {
        let v = self.next_lifted_var;
        self.next_lifted_var += 1;
        v
    }

    /// Create a BVC for an unconstrained input/state variable
    pub fn make_input(
        &mut self,
        tt: &mut TermTable,
        ct: &ConstraintTable,
        var_id: u32,
        width: BvWidth,
    ) -> BvcId {
        let term = tt.make_var(var_id, width);
        self.alloc(width, vec![BvcEntry {
            term,
            constraint: ct.true_id(),
        }])
    }

    /// Create a BVC for a constant value
    pub fn make_const(
        &mut self,
        tt: &mut TermTable,
        ct: &ConstraintTable,
        val: u64,
        width: BvWidth,
    ) -> BvcId {
        let term = tt.make_const(val, width);
        self.alloc(width, vec![BvcEntry {
            term,
            constraint: ct.true_id(),
        }])
    }

    /// Apply a structural operator: keeps the actual operator term.
    ///
    /// For comparisons (EQ, ULT, etc.) where one operand is a narrow BVC
    /// (≤8 bits), generates PRED constraints to enable Decide/Restrict
    /// interval blasting. The PRED asserts which values the operand can
    /// take to make the comparison true.
    pub fn apply_structural(
        &mut self,
        tt: &mut TermTable,
        ct: &mut ConstraintTable,
        op: OpKind,
        operands: &[BvcId],
        result_width: BvWidth,
    ) -> BvcId {
        // Build the operator term from operand terms
        let arg_terms: Vec<TermId> = operands.iter()
            .map(|&bvc_id| self.get(bvc_id).entries[0].term)
            .collect();

        // The result term is the actual operator application
        let result_term = tt.make_app(op, arg_terms, result_width);

        // Collect constraints from operands (conjunction)
        let mut combined_constraint = ct.true_id();
        for &bvc_id in operands {
            let entry_constraint = self.get(bvc_id).entries[0].constraint;
            combined_constraint = ct.make_and(combined_constraint, entry_constraint);
        }

        // For binary comparisons on narrow operands, generate PRED constraints.
        // PRED(operand_bvc, S) where S = {values that make comparison true}
        // This enables Decide/Restrict to partition the domain by S boundaries.
        if operands.len() == 2 && result_width == 1 {
            let aw = self.get(operands[0]).width;
            let bw = self.get(operands[1]).width;

            // Only generate PREDs for narrow operands (≤8 bits) where we can
            // compute the value set exactly. For wider operands, theory resolution
            // handles it via enumeration.
            if aw <= 8 || bw <= 8 {
                // Check if either operand is a constant
                let a_const = self.get_const_value(tt, operands[0]);
                let b_const = self.get_const_value(tt, operands[1]);

                if let Some(cv) = b_const {
                    // RHS is constant: PRED on LHS BVC
                    if aw <= 8 {
                        let vs = compute_comparison_valueset(op, cv, aw, false);
                        if !vs.is_full() {
                            let pred = ct.make_pred(operands[0], vs);
                            combined_constraint = ct.make_and(combined_constraint, pred);
                        }
                    }
                } else if let Some(cv) = a_const {
                    // LHS is constant: PRED on RHS BVC
                    if bw <= 8 {
                        let vs = compute_comparison_valueset(op, cv, bw, true);
                        if !vs.is_full() {
                            let pred = ct.make_pred(operands[1], vs);
                            combined_constraint = ct.make_and(combined_constraint, pred);
                        }
                    }
                }
            }
        }

        self.alloc(result_width, vec![BvcEntry {
            term: result_term,
            constraint: combined_constraint,
        }])
    }

    /// Apply a non-structural operator: keeps the actual operator term.
    ///
    /// Currently identical to apply_structural(). Lazy lifting to fresh
    /// variables requires encoding f == op(args) as a predicate, which
    /// needs the Decide loop to enumerate f's domain. This is deferred
    /// until the solver can properly resolve lifted equality predicates.
    pub fn apply_lifted(
        &mut self,
        tt: &mut TermTable,
        ct: &mut ConstraintTable,
        op: OpKind,
        operands: &[BvcId],
        result_width: BvWidth,
    ) -> BvcId {
        self.apply_structural(tt, ct, op, operands, result_width)
    }

    /// Apply an operator — keeps the actual operator term for all ops.
    pub fn apply(
        &mut self,
        tt: &mut TermTable,
        ct: &mut ConstraintTable,
        op: OpKind,
        operands: &[BvcId],
        result_width: BvWidth,
    ) -> BvcId {
        self.apply_structural(tt, ct, op, operands, result_width)
    }

    /// Negate a 1-bit BVC: XOR with 1
    pub fn negate(
        &mut self,
        tt: &mut TermTable,
        ct: &mut ConstraintTable,
        id: BvcId,
    ) -> BvcId {
        let one = self.make_const(tt, ct, 1, 1);
        self.apply(tt, ct, OpKind::Xor, &[id, one], 1)
    }

    /// Check if a BVC is ground (all entries have constant terms and TRUE constraints)
    pub fn is_ground(&self, tt: &TermTable, id: BvcId) -> bool {
        let bvc = self.get(id);
        bvc.entries.iter().all(|e| matches!(tt.get(e.term).kind, TermKind::Const(_)))
    }

    /// Get the concrete value if this is a ground BVC with a single constant entry
    pub fn get_const_value(&self, tt: &TermTable, id: BvcId) -> Option<u64> {
        let bvc = self.get(id);
        if bvc.entries.len() == 1 {
            if let TermKind::Const(v) = tt.get(bvc.entries[0].term).kind {
                return Some(v);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_make_input() {
        let mut tt = TermTable::new();
        let ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        let bvc = bm.make_input(&mut tt, &ct, 0, 8);
        assert_eq!(bm.get(bvc).width, 8);
        assert_eq!(bm.get(bvc).entries.len(), 1);
        assert_eq!(bm.get(bvc).entries[0].constraint, ct.true_id());
    }

    #[test]
    fn test_make_const() {
        let mut tt = TermTable::new();
        let ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        let bvc = bm.make_const(&mut tt, &ct, 42, 8);
        assert!(bm.is_ground(&tt, bvc));
        assert_eq!(bm.get_const_value(&tt, bvc), Some(42));
    }

    #[test]
    fn test_apply_structural() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        let x = bm.make_input(&mut tt, &ct, 0, 8);
        let y = bm.make_input(&mut tt, &ct, 1, 8);
        let eq = bm.apply_structural(&mut tt, &mut ct, OpKind::Eq, &[x, y], 1);

        assert_eq!(bm.get(eq).width, 1);
        // The term should be the actual Eq application
        let term = bm.get(eq).entries[0].term;
        match &tt.get(term).kind {
            TermKind::App { op: OpKind::Eq, .. } => {} // correct
            other => panic!("expected Eq app, got {:?}", other),
        }
    }

    #[test]
    fn test_apply_lifted() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        let x = bm.make_input(&mut tt, &ct, 0, 8);
        let y = bm.make_input(&mut tt, &ct, 1, 8);
        let add = bm.apply_lifted(&mut tt, &mut ct, OpKind::Add, &[x, y], 8);

        assert_eq!(bm.get(add).width, 8);
        // The term should be the actual Add application
        match &tt.get(bm.get(add).entries[0].term).kind {
            TermKind::App { op: OpKind::Add, .. } => {} // good: actual term
            other => panic!("expected Add app, got {:?}", other),
        }
    }

    #[test]
    fn test_apply_dispatches() {
        let mut tt = TermTable::new();
        let mut ct = ConstraintTable::new();
        let mut bm = BvcManager::new();

        let x = bm.make_input(&mut tt, &ct, 0, 8);
        let y = bm.make_input(&mut tt, &ct, 1, 8);

        // Eq is structural
        let eq = bm.apply(&mut tt, &mut ct, OpKind::Eq, &[x, y], 1);
        assert_eq!(bm.get(eq).width, 1);

        // Add is non-structural (at width 8)
        let add = bm.apply(&mut tt, &mut ct, OpKind::Add, &[x, y], 8);
        assert_eq!(bm.get(add).width, 8);
    }

    #[test]
    fn test_fresh_var_uniqueness() {
        let mut bm = BvcManager::new();
        let v1 = bm.fresh_var();
        let v2 = bm.fresh_var();
        assert_ne!(v1, v2);
    }
}
