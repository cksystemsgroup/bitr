use std::collections::HashMap;
use crate::types::{TermId, OpKind, BvWidth};

/// Maximum number of arguments per operator application
pub const TERM_MAX_ARGS: usize = 3;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    /// Domain constant value
    Const(u64),
    /// Variable (var_id from BTOR2)
    Var(u32),
    /// Operator application
    App {
        op: OpKind,
        args: Vec<TermId>,
        /// For OP_SLICE: upper and lower bit indices
        slice_upper: u16,
        slice_lower: u16,
    },
}

#[derive(Debug, Clone)]
pub struct Term {
    pub kind: TermKind,
    pub width: BvWidth,
}

/// Hash-consed term table: all terms stored uniquely
#[derive(Clone)]
pub struct TermTable {
    terms: Vec<Term>,
    /// Unique table: (kind, width) -> TermId
    unique: HashMap<(TermKind, BvWidth), TermId>,
    /// Substitution cache: (term, var, val) -> result
    subst_cache: HashMap<(TermId, u32, u64), TermId>,
    /// Term-for-term substitution cache
    subst_term_cache: HashMap<(TermId, u32, TermId), TermId>,
}

impl Default for TermTable {
    fn default() -> Self { Self::new() }
}

impl TermTable {
    pub fn new() -> Self {
        TermTable {
            terms: Vec::new(),
            unique: HashMap::new(),
            subst_cache: HashMap::new(),
            subst_term_cache: HashMap::new(),
        }
    }

    /// Clear substitution caches (e.g., between BMC steps)
    pub fn clear_subst_cache(&mut self) {
        self.subst_cache.clear();
        self.subst_term_cache.clear();
    }

    pub fn get(&self, id: TermId) -> &Term {
        &self.terms[id.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Intern a term, returning its unique ID
    pub fn intern(&mut self, kind: TermKind, width: BvWidth) -> TermId {
        let key = (kind.clone(), width);
        if let Some(&id) = self.unique.get(&key) {
            return id;
        }
        let id = TermId(self.terms.len() as u32);
        self.terms.push(Term { kind: kind.clone(), width });
        self.unique.insert(key, id);
        id
    }

    /// Create a constant term
    pub fn make_const(&mut self, val: u64, width: BvWidth) -> TermId {
        self.intern(TermKind::Const(val), width)
    }

    /// Create a variable term
    pub fn make_var(&mut self, var_id: u32, width: BvWidth) -> TermId {
        self.intern(TermKind::Var(var_id), width)
    }

    /// Create an operator application term
    pub fn make_app(&mut self, op: OpKind, args: Vec<TermId>, width: BvWidth) -> TermId {
        self.intern(TermKind::App { op, args, slice_upper: 0, slice_lower: 0 }, width)
    }

    /// Create a slice term
    pub fn make_slice(&mut self, arg: TermId, upper: u16, lower: u16) -> TermId {
        let width = upper - lower + 1;
        self.intern(
            TermKind::App {
                op: OpKind::Slice,
                args: vec![arg],
                slice_upper: upper,
                slice_lower: lower,
            },
            width,
        )
    }

    /// Recursively evaluate a term given a complete variable assignment.
    /// Returns None if a variable is missing from the assignment.
    pub fn eval(&self, id: TermId, assign: &HashMap<u32, u64>) -> Option<u64> {
        let term = self.get(id);
        let width = term.width;
        match &term.kind {
            TermKind::Const(v) => Some(mask(*v, width)),
            TermKind::Var(var_id) => assign.get(var_id).map(|&v| mask(v, width)),
            TermKind::App { op, args, slice_upper, slice_lower } => {
                let vals: Option<Vec<u64>> = args.iter().map(|&a| self.eval(a, assign)).collect();
                let vals = vals?;
                let arg_widths: Vec<BvWidth> = args.iter().map(|&a| self.get(a).width).collect();
                Some(eval_op(*op, &vals, &arg_widths, width, *slice_upper, *slice_lower))
            }
        }
    }

    /// Substitute variable `var` with constant `val` and fold constants.
    /// Returns a new (possibly simplified) term. Results are memoized.
    pub fn subst_and_fold(&mut self, id: TermId, var: u32, val: u64) -> TermId {
        // Cache lookup
        let cache_key = (id, var, val);
        if let Some(&cached) = self.subst_cache.get(&cache_key) {
            return cached;
        }
        let result = self.subst_and_fold_inner(id, var, val);
        self.subst_cache.insert(cache_key, result);
        result
    }

    fn subst_and_fold_inner(&mut self, id: TermId, var: u32, val: u64) -> TermId {
        let term = self.get(id).clone();
        match &term.kind {
            TermKind::Const(_) => id,
            TermKind::Var(v) => {
                if *v == var {
                    self.make_const(mask(val, term.width), term.width)
                } else {
                    id
                }
            }
            TermKind::App { op, args, slice_upper, slice_lower } => {
                let op = *op;
                let su = *slice_upper;
                let sl = *slice_lower;
                let width = term.width;
                let new_args: Vec<TermId> = args.iter()
                    .map(|&a| self.subst_and_fold(a, var, val))
                    .collect();

                // Check if all args are now constants → fold
                let all_const: Option<Vec<u64>> = new_args.iter().map(|&a| {
                    if let TermKind::Const(v) = self.get(a).kind { Some(v) } else { None }
                }).collect();

                if let Some(const_vals) = all_const {
                    let arg_widths: Vec<BvWidth> = new_args.iter()
                        .map(|&a| self.get(a).width)
                        .collect();
                    let result = eval_op(op, &const_vals, &arg_widths, width, su, sl);
                    self.make_const(result, width)
                } else {
                    self.intern(
                        TermKind::App { op, args: new_args, slice_upper: su, slice_lower: sl },
                        width,
                    )
                }
            }
        }
    }

    /// Substitute variable `var` with another term `replacement`.
    /// If the replacement causes all args to become constants, folds the result.
    pub fn subst_term(&mut self, id: TermId, var: u32, replacement: TermId) -> TermId {
        let cache_key = (id, var, replacement);
        if let Some(&cached) = self.subst_term_cache.get(&cache_key) {
            return cached;
        }
        let result = self.subst_term_inner(id, var, replacement);
        self.subst_term_cache.insert(cache_key, result);
        result
    }

    fn subst_term_inner(&mut self, id: TermId, var: u32, replacement: TermId) -> TermId {
        let term = self.get(id).clone();
        match &term.kind {
            TermKind::Const(_) => id,
            TermKind::Var(v) => {
                if *v == var { replacement } else { id }
            }
            TermKind::App { op, args, slice_upper, slice_lower } => {
                let op = *op;
                let su = *slice_upper;
                let sl = *slice_lower;
                let width = term.width;
                let new_args: Vec<TermId> = args.iter()
                    .map(|&a| self.subst_term(a, var, replacement))
                    .collect();

                // Try constant folding
                let all_const: Option<Vec<u64>> = new_args.iter().map(|&a| {
                    if let TermKind::Const(v) = self.get(a).kind { Some(v) } else { None }
                }).collect();

                if let Some(const_vals) = all_const {
                    let arg_widths: Vec<BvWidth> = new_args.iter()
                        .map(|&a| self.get(a).width)
                        .collect();
                    let result = eval_op(op, &const_vals, &arg_widths, width, su, sl);
                    self.make_const(result, width)
                } else {
                    self.intern(
                        TermKind::App { op, args: new_args, slice_upper: su, slice_lower: sl },
                        width,
                    )
                }
            }
        }
    }
}

/// Mask a value to `width` bits
fn mask(val: u64, width: BvWidth) -> u64 {
    if width >= 64 { val } else { val & ((1u64 << width) - 1) }
}

/// Sign-extend a `width`-bit value to i64
fn sign_extend(val: u64, width: BvWidth) -> i64 {
    if width == 0 { return 0; }
    if width >= 64 { return val as i64; }
    let sign_bit = 1u64 << (width - 1);
    if val & sign_bit != 0 {
        // Negative: fill upper bits with 1s
        (val | !((1u64 << width) - 1)) as i64
    } else {
        val as i64
    }
}

/// Evaluate an operator on concrete values, returning a masked result.
fn eval_op(
    op: OpKind,
    vals: &[u64],
    arg_widths: &[BvWidth],
    result_width: BvWidth,
    slice_upper: u16,
    slice_lower: u16,
) -> u64 {
    let m = |v: u64| mask(v, result_width);
    let a = vals[0];
    let b = if vals.len() > 1 { vals[1] } else { 0 };
    let aw = if !arg_widths.is_empty() { arg_widths[0] } else { result_width };

    match op {
        // Comparisons (result width 1)
        OpKind::Eq => if a == b { 1 } else { 0 },
        OpKind::Neq => if a != b { 1 } else { 0 },
        OpKind::Ult => if a < b { 1 } else { 0 },
        OpKind::Ulte => if a <= b { 1 } else { 0 },
        OpKind::Slt => {
            let sa = sign_extend(a, aw);
            let sb = sign_extend(b, aw);
            if sa < sb { 1 } else { 0 }
        }
        OpKind::Slte => {
            let sa = sign_extend(a, aw);
            let sb = sign_extend(b, aw);
            if sa <= sb { 1 } else { 0 }
        }

        // Overflow detection (result width 1)
        OpKind::Uaddo => {
            let sum = a.wrapping_add(b);
            if mask(sum, aw) != sum { 1 } else { 0 }
        }
        OpKind::Umulo => {
            let prod = (a as u128) * (b as u128);
            let max = if aw >= 64 { u64::MAX as u128 } else { (1u128 << aw) - 1 };
            if prod > max { 1 } else { 0 }
        }

        // Reductions (result width 1)
        OpKind::Redand => {
            let full = mask(u64::MAX, aw);
            if a == full { 1 } else { 0 }
        }
        OpKind::Redor => if a != 0 { 1 } else { 0 },
        OpKind::Redxor => m((a.count_ones() % 2) as u64),

        // Arithmetic
        OpKind::Add => m(a.wrapping_add(b)),
        OpKind::Sub => m(a.wrapping_sub(b)),
        OpKind::Mul => m(a.wrapping_mul(b)),
        OpKind::Udiv => m(if b == 0 { mask(u64::MAX, result_width) } else { a / b }),
        OpKind::Urem => m(if b == 0 { a } else { a % b }),
        OpKind::Sdiv => {
            if b == 0 {
                // SMT-LIB: sdiv by 0 is defined as -1 if dividend >= 0, 1 if negative
                let sa = sign_extend(a, aw);
                m(if sa >= 0 { mask(u64::MAX, result_width) } else { 1 })
            } else {
                let sa = sign_extend(a, aw);
                let sb = sign_extend(b, aw);
                m(sa.wrapping_div(sb) as u64)
            }
        }
        OpKind::Srem => {
            if b == 0 { m(a) }
            else {
                let sa = sign_extend(a, aw);
                let sb = sign_extend(b, aw);
                m(sa.wrapping_rem(sb) as u64)
            }
        }
        OpKind::Smod => {
            if b == 0 { m(a) }
            else {
                let sa = sign_extend(a, aw);
                let sb = sign_extend(b, aw);
                let rem = sa.wrapping_rem(sb);
                let result = if rem == 0 || (rem > 0) == (sb > 0) {
                    rem
                } else {
                    rem.wrapping_add(sb)
                };
                m(result as u64)
            }
        }

        // Bitwise
        OpKind::And => m(a & b),
        OpKind::Or => m(a | b),
        OpKind::Xor => m(a ^ b),
        OpKind::Not => m(!a),
        OpKind::Neg => m(a.wrapping_neg()),

        // Shifts
        OpKind::Sll => m(if b >= aw as u64 { 0 } else { a << b }),
        OpKind::Srl => m(if b >= aw as u64 { 0 } else { a >> b }),
        OpKind::Sra => {
            if b >= aw as u64 {
                // Shift all: fill with sign bit
                if sign_extend(a, aw) < 0 { mask(u64::MAX, result_width) } else { 0 }
            } else {
                m(sign_extend(a, aw).wrapping_shr(b as u32) as u64)
            }
        }

        // Slice: extract bits [upper:lower]
        OpKind::Slice => {
            m((a >> slice_lower) & mask(u64::MAX, slice_upper - slice_lower + 1))
        }

        // Extension
        OpKind::Uext => m(a), // zero extension: upper bits already 0 after mask
        OpKind::Sext => m(sign_extend(a, aw) as u64),

        // Concat: a is the high part, b is the low part
        OpKind::Concat => {
            let bw = if arg_widths.len() > 1 { arg_widths[1] } else { 0 };
            m((a << bw) | b)
        }

        // ITE: vals[0] is condition, vals[1] is then, vals[2] is else
        OpKind::Ite => {
            let c = vals[0];
            let then_v = vals[1];
            let else_v = if vals.len() > 2 { vals[2] } else { 0 };
            m(if c != 0 { then_v } else { else_v })
        }

        // Memory ops shouldn't appear in term evaluation
        OpKind::Read | OpKind::Write => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_consing() {
        let mut tt = TermTable::new();
        let x1 = tt.make_var(0, 8);
        let x2 = tt.make_var(0, 8);
        assert_eq!(x1, x2); // same variable -> same ID
        let y = tt.make_var(1, 8);
        assert_ne!(x1, y);
    }

    #[test]
    fn test_const() {
        let mut tt = TermTable::new();
        let c1 = tt.make_const(42, 8);
        let c2 = tt.make_const(42, 8);
        assert_eq!(c1, c2);
        let c3 = tt.make_const(43, 8);
        assert_ne!(c1, c3);
    }

    #[test]
    fn test_eval_arithmetic() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let add = tt.make_app(OpKind::Add, vec![x, y], 8);

        let mut assign = HashMap::new();
        assign.insert(0, 100u64);
        assign.insert(1, 50u64);
        assert_eq!(tt.eval(add, &assign), Some(150));

        // Overflow wraps
        assign.insert(0, 200);
        assign.insert(1, 100);
        assert_eq!(tt.eval(add, &assign), Some(44)); // (300 & 0xFF) = 44
    }

    #[test]
    fn test_eval_comparisons() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let eq = tt.make_app(OpKind::Eq, vec![x, y], 1);
        let ult = tt.make_app(OpKind::Ult, vec![x, y], 1);

        let mut assign = HashMap::new();
        assign.insert(0, 5u64);
        assign.insert(1, 5u64);
        assert_eq!(tt.eval(eq, &assign), Some(1));
        assert_eq!(tt.eval(ult, &assign), Some(0));

        assign.insert(1, 10);
        assert_eq!(tt.eval(eq, &assign), Some(0));
        assert_eq!(tt.eval(ult, &assign), Some(1));
    }

    #[test]
    fn test_eval_signed() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let slt = tt.make_app(OpKind::Slt, vec![x, y], 1);

        let mut assign = HashMap::new();
        // -1 (0xFF) < 1 in signed
        assign.insert(0, 0xFF);
        assign.insert(1, 1);
        assert_eq!(tt.eval(slt, &assign), Some(1));
    }

    #[test]
    fn test_eval_bitwise() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let and_t = tt.make_app(OpKind::And, vec![x, y], 8);
        let or_t = tt.make_app(OpKind::Or, vec![x, y], 8);
        let not_t = tt.make_app(OpKind::Not, vec![x], 8);

        let mut assign = HashMap::new();
        assign.insert(0, 0xF0u64);
        assign.insert(1, 0x0Fu64);
        assert_eq!(tt.eval(and_t, &assign), Some(0x00));
        assert_eq!(tt.eval(or_t, &assign), Some(0xFF));
        assert_eq!(tt.eval(not_t, &assign), Some(0x0F));
    }

    #[test]
    fn test_eval_shifts() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let amt = tt.make_const(2, 8);
        let sll = tt.make_app(OpKind::Sll, vec![x, amt], 8);
        let srl = tt.make_app(OpKind::Srl, vec![x, amt], 8);

        let mut assign = HashMap::new();
        assign.insert(0, 0b00001111u64);
        assert_eq!(tt.eval(sll, &assign), Some(0b00111100));
        assert_eq!(tt.eval(srl, &assign), Some(0b00000011));
    }

    #[test]
    fn test_eval_slice() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let sl = tt.make_slice(x, 5, 2); // bits [5:2] → 4-bit result

        let mut assign = HashMap::new();
        assign.insert(0, 0b11_1010_11u64); // bits[5:2] = 1010 = 10
        assert_eq!(tt.eval(sl, &assign), Some(0b1010));
    }

    #[test]
    fn test_eval_concat() {
        let mut tt = TermTable::new();
        let hi = tt.make_var(0, 4);
        let lo = tt.make_var(1, 4);
        let cat = tt.make_app(OpKind::Concat, vec![hi, lo], 8);

        let mut assign = HashMap::new();
        assign.insert(0, 0xAu64);
        assign.insert(1, 0x5u64);
        assert_eq!(tt.eval(cat, &assign), Some(0xA5));
    }

    #[test]
    fn test_eval_ite() {
        let mut tt = TermTable::new();
        let cond = tt.make_var(0, 1);
        let then_v = tt.make_const(42, 8);
        let else_v = tt.make_const(99, 8);
        let ite = tt.make_app(OpKind::Ite, vec![cond, then_v, else_v], 8);

        let mut assign = HashMap::new();
        assign.insert(0, 1u64);
        assert_eq!(tt.eval(ite, &assign), Some(42));
        assign.insert(0, 0);
        assert_eq!(tt.eval(ite, &assign), Some(99));
    }

    #[test]
    fn test_eval_reductions() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let redand = tt.make_app(OpKind::Redand, vec![x], 1);
        let redor = tt.make_app(OpKind::Redor, vec![x], 1);

        let mut assign = HashMap::new();
        assign.insert(0, 0xFFu64);
        assert_eq!(tt.eval(redand, &assign), Some(1));
        assert_eq!(tt.eval(redor, &assign), Some(1));

        assign.insert(0, 0u64);
        assert_eq!(tt.eval(redand, &assign), Some(0));
        assert_eq!(tt.eval(redor, &assign), Some(0));

        assign.insert(0, 1u64);
        assert_eq!(tt.eval(redand, &assign), Some(0));
        assert_eq!(tt.eval(redor, &assign), Some(1));
    }

    #[test]
    fn test_eval_missing_var() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let assign = HashMap::new(); // empty
        assert_eq!(tt.eval(x, &assign), None);
    }

    #[test]
    fn test_subst_and_fold_const() {
        let mut tt = TermTable::new();
        let c = tt.make_const(42, 8);
        let result = tt.subst_and_fold(c, 0, 100);
        assert_eq!(result, c); // constants unchanged
    }

    #[test]
    fn test_subst_and_fold_var() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);

        let result = tt.subst_and_fold(x, 0, 42);
        assert_eq!(tt.get(result).kind, TermKind::Const(42));

        let result2 = tt.subst_and_fold(y, 0, 42);
        assert_eq!(result2, y); // different var, unchanged
    }

    #[test]
    fn test_subst_and_fold_app() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let add = tt.make_app(OpKind::Add, vec![x, y], 8);

        // Substitute x=10 → Add(10, y) — not fully constant, stays as App
        let partial = tt.subst_and_fold(add, 0, 10);
        match &tt.get(partial).kind {
            TermKind::App { .. } => {} // still an app
            other => panic!("expected App, got {:?}", other),
        }

        // Now substitute y=20 → should fold to const 30
        let full = tt.subst_and_fold(partial, 1, 20);
        assert_eq!(tt.get(full).kind, TermKind::Const(30));
    }

    #[test]
    fn test_subst_and_fold_nested() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let c5 = tt.make_const(5, 8);
        let add = tt.make_app(OpKind::Add, vec![x, c5], 8);
        let c100 = tt.make_const(100, 8);
        let mul = tt.make_app(OpKind::Mul, vec![add, c100], 8);

        // x=10 → (10+5)*100 = 1500, masked to 8 bits = 1500 & 0xFF = 220
        let result = tt.subst_and_fold(mul, 0, 10);
        assert_eq!(tt.get(result).kind, TermKind::Const(220));
    }

    #[test]
    fn test_eval_sext() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 4); // 4-bit value
        let sext = tt.make_app(OpKind::Sext, vec![x], 8); // sign-extend to 8 bits

        let mut assign = HashMap::new();
        // 0b1010 = -6 in 4-bit signed → 0b11111010 = 0xFA in 8-bit
        assign.insert(0, 0b1010u64);
        assert_eq!(tt.eval(sext, &assign), Some(0xFA));

        // 0b0101 = 5 in 4-bit signed → 0b00000101 = 5 in 8-bit
        assign.insert(0, 0b0101u64);
        assert_eq!(tt.eval(sext, &assign), Some(5));
    }
}
