use std::collections::HashMap;
use crate::types::{ConstraintId, BvcId};
use crate::valueset::ValueSet;

/// A constraint is a Boolean formula over predicates phi restricted to S
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstraintKind {
    True,
    False,
    /// Predicate: BVC phi has value in set S
    Pred { bvc: BvcId, valueset: ValueSet },
    Not(ConstraintId),
    And(ConstraintId, ConstraintId),
    Or(ConstraintId, ConstraintId),
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub kind: ConstraintKind,
}

/// Constraint table with hash-consing and simplification
#[derive(Clone)]
pub struct ConstraintTable {
    constraints: Vec<Constraint>,
    /// Unique table: kind -> ConstraintId
    unique: HashMap<ConstraintKind, ConstraintId>,
}

impl Default for ConstraintTable {
    fn default() -> Self { Self::new() }
}

impl ConstraintTable {
    pub fn new() -> Self {
        let mut ct = ConstraintTable {
            constraints: Vec::new(),
            unique: HashMap::new(),
        };
        // Pre-allocate TRUE and FALSE at known indices
        let _true_id = ct.intern(ConstraintKind::True);   // index 0
        let _false_id = ct.intern(ConstraintKind::False);  // index 1
        ct
    }

    pub fn true_id(&self) -> ConstraintId { ConstraintId(0) }
    pub fn false_id(&self) -> ConstraintId { ConstraintId(1) }

    pub fn get(&self, id: ConstraintId) -> &Constraint {
        &self.constraints[id.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Intern a constraint kind, returning an existing ID if structurally identical
    fn intern(&mut self, kind: ConstraintKind) -> ConstraintId {
        if let Some(&id) = self.unique.get(&kind) {
            return id;
        }
        let id = ConstraintId(self.constraints.len() as u32);
        self.constraints.push(Constraint { kind: kind.clone() });
        self.unique.insert(kind, id);
        id
    }

    /// Create a predicate constraint with hash consing
    pub fn make_pred(&mut self, bvc: BvcId, valueset: ValueSet) -> ConstraintId {
        // Empty valueset → FALSE (can never be satisfied)
        if valueset.is_empty() {
            return self.false_id();
        }
        // Full valueset → TRUE (always satisfied)
        if valueset.is_full() {
            return self.true_id();
        }
        self.intern(ConstraintKind::Pred { bvc, valueset })
    }

    /// Boolean AND with simplification + hash consing
    pub fn make_and(&mut self, a: ConstraintId, b: ConstraintId) -> ConstraintId {
        if a == self.true_id() { return b; }
        if b == self.true_id() { return a; }
        if a == self.false_id() || b == self.false_id() { return self.false_id(); }
        if a == b { return a; }
        // Normalize: smaller ID first for better hash consing
        let (a, b) = if a.0 <= b.0 { (a, b) } else { (b, a) };
        self.intern(ConstraintKind::And(a, b))
    }

    /// Boolean OR with simplification + hash consing
    pub fn make_or(&mut self, a: ConstraintId, b: ConstraintId) -> ConstraintId {
        if a == self.false_id() { return b; }
        if b == self.false_id() { return a; }
        if a == self.true_id() || b == self.true_id() { return self.true_id(); }
        if a == b { return a; }
        let (a, b) = if a.0 <= b.0 { (a, b) } else { (b, a) };
        self.intern(ConstraintKind::Or(a, b))
    }

    /// Boolean NOT with simplification + hash consing
    pub fn make_not(&mut self, a: ConstraintId) -> ConstraintId {
        if a == self.true_id() { return self.false_id(); }
        if a == self.false_id() { return self.true_id(); }
        // Double negation
        if let ConstraintKind::Not(inner) = self.get(a).kind {
            return inner;
        }
        self.intern(ConstraintKind::Not(a))
    }

    /// Restrict constraint `k` given that predicate on `bvc` takes values in `s_j`.
    ///
    /// From the expert doc:
    /// - PRED(phi', S'): if phi' != phi → unchanged
    ///   if S_j subset S' → TRUE
    ///   if S_j inter S' == empty → FALSE
    ///   else → PRED(phi, S_j inter S')
    /// - NOT(K1) → NOT(Restrict(K1))
    /// - AND(K1, K2) → short-circuit AND of Restrict(K1), Restrict(K2)
    /// - OR(K1, K2) → short-circuit OR of Restrict(K1), Restrict(K2)
    pub fn restrict(&mut self, k: ConstraintId, bvc: BvcId, s_j: ValueSet) -> ConstraintId {
        match self.get(k).kind.clone() {
            ConstraintKind::True | ConstraintKind::False => k,
            ConstraintKind::Pred { bvc: pred_bvc, valueset: s_prime } => {
                if pred_bvc != bvc {
                    return k; // Unrelated predicate
                }
                if s_j.is_subset_of(s_prime) {
                    return self.true_id();
                }
                let inter = s_j.and(s_prime);
                if inter.is_empty() {
                    return self.false_id();
                }
                self.make_pred(bvc, inter)
            }
            ConstraintKind::Not(inner) => {
                let r = self.restrict(inner, bvc, s_j);
                self.make_not(r)
            }
            ConstraintKind::And(a, b) => {
                let ra = self.restrict(a, bvc, s_j);
                // Short-circuit: if first is FALSE, result is FALSE
                if ra == self.false_id() {
                    return self.false_id();
                }
                let rb = self.restrict(b, bvc, s_j);
                self.make_and(ra, rb)
            }
            ConstraintKind::Or(a, b) => {
                let ra = self.restrict(a, bvc, s_j);
                // Short-circuit: if first is TRUE, result is TRUE
                if ra == self.true_id() {
                    return self.true_id();
                }
                let rb = self.restrict(b, bvc, s_j);
                self.make_or(ra, rb)
            }
        }
    }

    /// Collect all PRED nodes referencing a given BVC
    pub fn collect_preds(&self, k: ConstraintId, bvc: BvcId) -> Vec<ValueSet> {
        let mut result = Vec::new();
        self.collect_preds_inner(k, bvc, &mut result);
        result
    }

    fn collect_preds_inner(&self, k: ConstraintId, bvc: BvcId, result: &mut Vec<ValueSet>) {
        match &self.get(k).kind {
            ConstraintKind::True | ConstraintKind::False => {}
            ConstraintKind::Pred { bvc: pred_bvc, valueset } => {
                if *pred_bvc == bvc {
                    result.push(*valueset);
                }
            }
            ConstraintKind::Not(inner) => {
                self.collect_preds_inner(*inner, bvc, result);
            }
            ConstraintKind::And(a, b) | ConstraintKind::Or(a, b) => {
                self.collect_preds_inner(*a, bvc, result);
                self.collect_preds_inner(*b, bvc, result);
            }
        }
    }

    /// Check if a constraint is satisfiable under value set S
    /// (conservative: returns true if possibly satisfiable)
    pub fn is_definitely_false(&self, k: ConstraintId) -> bool {
        k == self.false_id()
    }

    /// Check if a constraint has no predicates (all TRUE/FALSE)
    pub fn has_no_predicates(&self, k: ConstraintId) -> bool {
        match &self.get(k).kind {
            ConstraintKind::True | ConstraintKind::False => true,
            ConstraintKind::Pred { .. } => false,
            ConstraintKind::Not(inner) => self.has_no_predicates(*inner),
            ConstraintKind::And(a, b) | ConstraintKind::Or(a, b) => {
                self.has_no_predicates(*a) && self.has_no_predicates(*b)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplification() {
        let mut ct = ConstraintTable::new();
        let t = ct.true_id();
        let f = ct.false_id();

        assert_eq!(ct.make_and(t, f), f);
        assert_eq!(ct.make_and(t, t), t);
        assert_eq!(ct.make_or(f, t), t);
        assert_eq!(ct.make_not(t), f);
        assert_eq!(ct.make_not(f), t);
    }

    #[test]
    fn test_hash_consing() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        let vs = ValueSet::singleton(42);

        let p1 = ct.make_pred(bvc, vs);
        let p2 = ct.make_pred(bvc, vs);
        assert_eq!(p1, p2); // same predicate → same ID

        let a1 = ct.make_and(p1, p1);
        // AND(p, p) simplifies to p
        assert_eq!(a1, p1);
    }

    #[test]
    fn test_and_or_normalization() {
        let mut ct = ConstraintTable::new();
        let p1 = ct.make_pred(BvcId(0), ValueSet::singleton(1));
        let p2 = ct.make_pred(BvcId(1), ValueSet::singleton(2));

        // AND(p1, p2) == AND(p2, p1) due to normalization
        let and1 = ct.make_and(p1, p2);
        let and2 = ct.make_and(p2, p1);
        assert_eq!(and1, and2);

        let or1 = ct.make_or(p1, p2);
        let or2 = ct.make_or(p2, p1);
        assert_eq!(or1, or2);
    }

    #[test]
    fn test_pred_simplification() {
        let mut ct = ConstraintTable::new();
        // Empty valueset → FALSE
        assert_eq!(ct.make_pred(BvcId(0), ValueSet::EMPTY), ct.false_id());
        // Full valueset → TRUE
        assert_eq!(ct.make_pred(BvcId(0), ValueSet::FULL), ct.true_id());
    }

    #[test]
    fn test_restrict_subset() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        // PRED(bvc, {0..100})
        let s_prime = ValueSet::from_range(0, 100);
        let pred = ct.make_pred(bvc, s_prime);

        // Restrict with S_j = {10..20} ⊂ {0..100} → TRUE
        let s_j = ValueSet::from_range(10, 20);
        let r = ct.restrict(pred, bvc, s_j);
        assert_eq!(r, ct.true_id());
    }

    #[test]
    fn test_restrict_disjoint() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        let s_prime = ValueSet::from_range(0, 10);
        let pred = ct.make_pred(bvc, s_prime);

        // Restrict with S_j = {200..255} disjoint from {0..10} → FALSE
        let s_j = ValueSet::from_range(200, 255);
        let r = ct.restrict(pred, bvc, s_j);
        assert_eq!(r, ct.false_id());
    }

    #[test]
    fn test_restrict_partial() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        let s_prime = ValueSet::from_range(5, 15);
        let pred = ct.make_pred(bvc, s_prime);

        // Restrict with S_j = {10..20} → PRED(bvc, {10..15})
        let s_j = ValueSet::from_range(10, 20);
        let r = ct.restrict(pred, bvc, s_j);
        let expected_vs = ValueSet::from_range(10, 15);
        assert_eq!(ct.get(r).kind, ConstraintKind::Pred { bvc, valueset: expected_vs });
    }

    #[test]
    fn test_restrict_unrelated() {
        let mut ct = ConstraintTable::new();
        let pred = ct.make_pred(BvcId(0), ValueSet::singleton(5));

        // Restrict on different BVC → unchanged
        let r = ct.restrict(pred, BvcId(1), ValueSet::FULL);
        assert_eq!(r, pred);
    }

    #[test]
    fn test_restrict_and_short_circuit() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        let p1 = ct.make_pred(bvc, ValueSet::from_range(0, 10));
        let p2 = ct.make_pred(bvc, ValueSet::from_range(20, 30));
        let conj = ct.make_and(p1, p2);

        // Restrict with S_j = {5..8}: p1 becomes TRUE (subset), p2 becomes FALSE (disjoint)
        // AND(TRUE, FALSE) = FALSE
        let s_j = ValueSet::from_range(5, 8);
        let r = ct.restrict(conj, bvc, s_j);
        assert_eq!(r, ct.false_id());
    }

    #[test]
    fn test_restrict_or_short_circuit() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        let p1 = ct.make_pred(bvc, ValueSet::from_range(0, 100));
        let p2 = ct.make_pred(bvc, ValueSet::from_range(50, 200));
        let disj = ct.make_or(p1, p2);

        // Restrict with S_j = {10..20}: p1 becomes TRUE (subset) → short-circuit
        let s_j = ValueSet::from_range(10, 20);
        let r = ct.restrict(disj, bvc, s_j);
        assert_eq!(r, ct.true_id());
    }

    #[test]
    fn test_has_no_predicates() {
        let mut ct = ConstraintTable::new();
        assert!(ct.has_no_predicates(ct.true_id()));
        assert!(ct.has_no_predicates(ct.false_id()));

        let pred = ct.make_pred(BvcId(0), ValueSet::singleton(5));
        assert!(!ct.has_no_predicates(pred));

        let and = ct.make_and(ct.true_id(), ct.true_id());
        assert!(ct.has_no_predicates(and));
    }

    #[test]
    fn test_collect_preds() {
        let mut ct = ConstraintTable::new();
        let bvc = BvcId(0);
        let vs1 = ValueSet::from_range(0, 10);
        let vs2 = ValueSet::from_range(20, 30);
        let p1 = ct.make_pred(bvc, vs1);
        let p2 = ct.make_pred(bvc, vs2);
        let p3 = ct.make_pred(BvcId(1), ValueSet::singleton(5)); // different BVC
        let inner = ct.make_and(p2, p3);
        let conj = ct.make_and(p1, inner);

        let preds = ct.collect_preds(conj, bvc);
        assert_eq!(preds.len(), 2);
        assert!(preds.contains(&vs1));
        assert!(preds.contains(&vs2));
    }
}
