//! Bit-blasting: convert bitvector terms to CNF and solve with native CDCL SAT solver (splr).
//!
//! Converts BVDD terms into a Boolean circuit via Tseitin encoding, then invokes
//! the splr SAT solver. This replaces the external oracle (bitwuzla) for many
//! benchmarks, eliminating subprocess overhead.

use std::collections::HashMap;
use crate::types::{TermId, OpKind, SolveResult};
use crate::term::{TermTable, TermKind};
use crate::valueset::ValueSet;

/// Maximum SAT variables before bailing out
const MAX_SAT_VARS: i32 = 1_000_000;
/// Maximum clauses before bailing out
const MAX_CLAUSES: usize = 5_000_000;

/// Bit-blaster: converts bitvector terms to CNF and solves via splr.
pub struct BitBlaster<'a> {
    tt: &'a TermTable,
    /// Next SAT variable to allocate (1-based, DIMACS convention)
    next_var: i32,
    /// CNF clause database
    clauses: Vec<Vec<i32>>,
    /// Memoization: term ID -> vector of SAT literals for each output bit (LSB first)
    term_bits: HashMap<TermId, Vec<i32>>,
    /// Gate memoization: (min_lit, max_lit, op_tag) -> output literal
    /// op_tag: 0=AND, 1=OR, 2=XOR
    gate_cache: HashMap<(i32, i32, u8), i32>,
    /// Constant-true literal (variable 1, forced true)
    true_lit: i32,
    /// Budget exceeded flag
    exceeded: bool,
    /// Wall-clock timeout for encoding (seconds, 0 = no timeout)
    timeout_s: f64,
    /// Start time for timeout
    start_time: std::time::Instant,
}

impl<'a> BitBlaster<'a> {
    pub fn new(tt: &'a TermTable) -> Self {
        let mut bb = BitBlaster {
            tt,
            next_var: 2, // variable 1 reserved for true_lit
            clauses: Vec::with_capacity(4096),
            term_bits: HashMap::new(),
            gate_cache: HashMap::new(),
            true_lit: 1,
            exceeded: false,
            timeout_s: 0.0,
            start_time: std::time::Instant::now(),
        };
        // Force variable 1 = true
        bb.clauses.push(vec![1]);
        bb
    }

    /// Set a wall-clock timeout for encoding (seconds)
    pub fn set_timeout(&mut self, timeout_s: f64) {
        self.timeout_s = timeout_s;
        self.start_time = std::time::Instant::now();
    }

    /// Check if encoding has timed out
    #[inline]
    fn check_timeout(&mut self) {
        if self.timeout_s > 0.0 && self.next_var % 1000 == 0
            && self.start_time.elapsed().as_secs_f64() > self.timeout_s
        {
            self.exceeded = true;
        }
    }

    /// Number of SAT variables allocated so far
    pub fn num_vars(&self) -> i32 {
        self.next_var - 1
    }

    /// Number of clauses generated so far
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    fn fresh_var(&mut self) -> i32 {
        if self.next_var >= MAX_SAT_VARS {
            self.exceeded = true;
            return self.true_lit;
        }
        self.check_timeout();
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn fresh_vars(&mut self, n: u16) -> Vec<i32> {
        (0..n).map(|_| self.fresh_var()).collect()
    }

    fn add_clause(&mut self, clause: Vec<i32>) {
        if self.clauses.len() >= MAX_CLAUSES {
            self.exceeded = true;
            return;
        }
        self.clauses.push(clause);
    }

    // ==================== Tseitin gate encodings ====================

    /// c <-> (a AND b)
    fn and_gate(&mut self, a: i32, b: i32) -> i32 {
        // Constant propagation
        if a == self.true_lit { return b; }
        if b == self.true_lit { return a; }
        if a == -self.true_lit || b == -self.true_lit { return -self.true_lit; }
        if a == b { return a; }
        if a == -b { return -self.true_lit; }

        let key = (a.min(b), a.max(b), 0u8);
        if let Some(&c) = self.gate_cache.get(&key) { return c; }

        let c = self.fresh_var();
        self.add_clause(vec![-a, -b, c]);
        self.add_clause(vec![a, -c]);
        self.add_clause(vec![b, -c]);
        self.gate_cache.insert(key, c);
        c
    }

    /// c <-> (a OR b)
    fn or_gate(&mut self, a: i32, b: i32) -> i32 {
        if a == -self.true_lit { return b; }
        if b == -self.true_lit { return a; }
        if a == self.true_lit || b == self.true_lit { return self.true_lit; }
        if a == b { return a; }
        if a == -b { return self.true_lit; }

        let key = (a.min(b), a.max(b), 1u8);
        if let Some(&c) = self.gate_cache.get(&key) { return c; }

        let c = self.fresh_var();
        self.add_clause(vec![a, b, -c]);
        self.add_clause(vec![-a, c]);
        self.add_clause(vec![-b, c]);
        self.gate_cache.insert(key, c);
        c
    }

    /// c <-> (a XOR b)
    fn xor_gate(&mut self, a: i32, b: i32) -> i32 {
        if a == -self.true_lit { return b; }
        if b == -self.true_lit { return a; }
        if a == self.true_lit { return -b; }
        if b == self.true_lit { return -a; }
        if a == b { return -self.true_lit; }
        if a == -b { return self.true_lit; }

        let key = (a.min(b), a.max(b), 2u8);
        if let Some(&c) = self.gate_cache.get(&key) { return c; }

        let c = self.fresh_var();
        self.add_clause(vec![-a, -b, -c]);
        self.add_clause(vec![a, b, -c]);
        self.add_clause(vec![a, -b, c]);
        self.add_clause(vec![-a, b, c]);
        self.gate_cache.insert(key, c);
        c
    }

    /// c <-> ITE(s, t, e)
    fn ite_gate(&mut self, s: i32, t: i32, e: i32) -> i32 {
        if s == self.true_lit { return t; }
        if s == -self.true_lit { return e; }
        if t == e { return t; }

        let c = self.fresh_var();
        self.add_clause(vec![-s, -t, c]);
        self.add_clause(vec![-s, t, -c]);
        self.add_clause(vec![s, -e, c]);
        self.add_clause(vec![s, e, -c]);
        c
    }

    /// Full adder: (sum, carry_out) given a, b, carry_in
    fn full_adder(&mut self, a: i32, b: i32, cin: i32) -> (i32, i32) {
        let t = self.xor_gate(a, b);
        let sum = self.xor_gate(t, cin);
        let g1 = self.and_gate(a, b);
        let g2 = self.and_gate(cin, t);
        let cout = self.or_gate(g1, g2);
        (sum, cout)
    }

    // ==================== Bitwise vector operations ====================

    fn and_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        a.iter().zip(b.iter()).map(|(&ai, &bi)| self.and_gate(ai, bi)).collect()
    }

    fn or_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        a.iter().zip(b.iter()).map(|(&ai, &bi)| self.or_gate(ai, bi)).collect()
    }

    fn xor_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        a.iter().zip(b.iter()).map(|(&ai, &bi)| self.xor_gate(ai, bi)).collect()
    }

    fn not_bits(&self, a: &[i32]) -> Vec<i32> {
        a.iter().map(|&ai| -ai).collect()
    }

    // ==================== Arithmetic ====================

    /// N-bit ripple-carry adder, returns (sum_bits, carry_out)
    fn adder(&mut self, a: &[i32], b: &[i32], carry_in: i32) -> (Vec<i32>, i32) {
        let n = a.len();
        let mut sum = Vec::with_capacity(n);
        let mut carry = carry_in;
        for i in 0..n {
            let (s, c) = self.full_adder(a[i], b[i], carry);
            sum.push(s);
            carry = c;
        }
        (sum, carry)
    }

    fn add_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        let (sum, _) = self.adder(a, b, -self.true_lit);
        sum
    }

    fn sub_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        let not_b = self.not_bits(b);
        let (sum, _) = self.adder(a, &not_b, self.true_lit);
        sum
    }

    fn neg_bits(&mut self, a: &[i32]) -> Vec<i32> {
        let n = a.len();
        let zero: Vec<i32> = vec![-self.true_lit; n];
        self.sub_bits(&zero, a)
    }

    /// N-bit multiplication via shift-and-add, truncated to n bits
    fn mul_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        let n = a.len();
        let false_lit = -self.true_lit;

        let mut result: Vec<i32> = vec![false_lit; n];

        for i in 0..n {
            // Partial product: a[j] AND b[i] for j = 0..n-i
            let mut shifted = vec![false_lit; n];
            for j in 0..n {
                if i + j < n {
                    shifted[i + j] = self.and_gate(a[j], b[i]);
                }
            }
            result = self.add_bits(&result, &shifted);

            if self.exceeded { break; }
        }
        result
    }

    // ==================== Division ====================

    /// Unsigned N-bit division via restoring division circuit.
    /// Returns (quotient, remainder). Division by zero: quotient = all-ones, remainder = dividend.
    fn udivrem_bits(&mut self, a: &[i32], b: &[i32]) -> (Vec<i32>, Vec<i32>) {
        let n = a.len();
        let false_lit = -self.true_lit;
        let true_lit = self.true_lit;

        // Check if divisor is zero (for BTOR2 semantics)
        let b_is_zero = {
            let b_or = self.redor_bits(b);
            -b_or // b_is_zero = NOT(any bit set)
        };

        // Restoring division: work with (n+1)-bit remainder to detect overflow
        // Initialize remainder to 0
        let mut rem: Vec<i32> = vec![false_lit; n];
        let mut quot: Vec<i32> = vec![false_lit; n];

        // Process from MSB to LSB
        for i in (0..n).rev() {
            if self.exceeded { break; }

            // Shift remainder left by 1, bring in next dividend bit
            for j in (1..n).rev() {
                rem[j] = rem[j - 1];
            }
            rem[0] = a[i];

            // Trial subtraction: rem - b
            let not_b = self.not_bits(b);
            let (diff, carry) = self.adder(&rem, &not_b, true_lit);
            // carry = 1 means rem >= b (no borrow)
            let rem_ge_b = carry;

            // Quotient bit = rem >= b
            quot[i] = rem_ge_b;

            // If rem >= b, use diff (rem - b); else keep rem
            for j in 0..n {
                rem[j] = self.ite_gate(rem_ge_b, diff[j], rem[j]);
            }
        }

        // Apply division-by-zero semantics: if b == 0, quot = all-ones, rem = a
        for i in 0..n {
            quot[i] = self.ite_gate(b_is_zero, true_lit, quot[i]);
            rem[i] = self.ite_gate(b_is_zero, a[i], rem[i]);
        }

        (quot, rem)
    }

    // ==================== Comparisons ====================

    /// Unsigned less-than: true iff a < b
    fn ult_bits(&mut self, a: &[i32], b: &[i32]) -> i32 {
        // a < b iff borrow out of a - b (carry-out of a + ~b + 1 is 0)
        let not_b = self.not_bits(b);
        let (_, carry) = self.adder(a, &not_b, self.true_lit);
        -carry // NOT carry = borrow = (a < b)
    }

    /// Signed less-than: flip MSBs, then unsigned compare
    fn slt_bits(&mut self, a: &[i32], b: &[i32]) -> i32 {
        let n = a.len();
        if n == 0 { return -self.true_lit; }
        let mut af = a.to_vec();
        let mut bf = b.to_vec();
        af[n - 1] = -af[n - 1];
        bf[n - 1] = -bf[n - 1];
        self.ult_bits(&af, &bf)
    }

    /// Equality: true iff a == b (all bits match)
    fn eq_bits(&mut self, a: &[i32], b: &[i32]) -> i32 {
        if a.is_empty() { return self.true_lit; }
        // XNOR each pair, AND all together
        let mut result = self.true_lit;
        for i in 0..a.len() {
            let diff = self.xor_gate(a[i], b[i]);
            result = self.and_gate(result, -diff);
        }
        result
    }

    // ==================== Shifts (barrel shifter) ====================

    fn sll_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        let n = a.len();
        let false_lit = -self.true_lit;
        let mut result = a.to_vec();

        for (k, &bk) in b.iter().enumerate() {
            let shift_amt = 1usize << k;
            if shift_amt >= n {
                result = result.iter().map(|&r| self.ite_gate(bk, false_lit, r)).collect();
                continue;
            }
            let mut shifted = vec![false_lit; n];
            shifted[shift_amt..n].copy_from_slice(&result[..(n - shift_amt)]);
            result = result.iter().zip(shifted.iter())
                .map(|(&r, &s)| self.ite_gate(bk, s, r))
                .collect();
        }
        result
    }

    fn srl_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        let n = a.len();
        let false_lit = -self.true_lit;
        let mut result = a.to_vec();

        for (k, &bk) in b.iter().enumerate() {
            let shift_amt = 1usize << k;
            if shift_amt >= n {
                result = result.iter().map(|&r| self.ite_gate(bk, false_lit, r)).collect();
                continue;
            }
            let mut shifted = vec![false_lit; n];
            shifted[..(n - shift_amt)].copy_from_slice(&result[shift_amt..n]);
            result = result.iter().zip(shifted.iter())
                .map(|(&r, &s)| self.ite_gate(bk, s, r))
                .collect();
        }
        result
    }

    fn sra_bits(&mut self, a: &[i32], b: &[i32]) -> Vec<i32> {
        let n = a.len();
        if n == 0 { return vec![]; }
        let sign = a[n - 1];
        let mut result = a.to_vec();

        for (k, &bk) in b.iter().enumerate() {
            let shift_amt = 1usize << k;
            if shift_amt >= n {
                result = result.iter().map(|&r| self.ite_gate(bk, sign, r)).collect();
                continue;
            }
            let mut shifted = vec![sign; n];
            shifted[..(n - shift_amt)].copy_from_slice(&result[shift_amt..n]);
            result = result.iter().zip(shifted.iter())
                .map(|(&r, &s)| self.ite_gate(bk, s, r))
                .collect();
        }
        result
    }

    // ==================== Reductions ====================

    fn redand_bits(&mut self, a: &[i32]) -> i32 {
        let mut r = self.true_lit;
        for &ai in a { r = self.and_gate(r, ai); }
        r
    }

    fn redor_bits(&mut self, a: &[i32]) -> i32 {
        let mut r = -self.true_lit;
        for &ai in a { r = self.or_gate(r, ai); }
        r
    }

    fn redxor_bits(&mut self, a: &[i32]) -> i32 {
        let mut r = -self.true_lit;
        for &ai in a { r = self.xor_gate(r, ai); }
        r
    }

    // ==================== Term bit-blasting ====================

    /// Bit-blast a term, returning SAT literals for each output bit (LSB first).
    /// Returns None if budget exceeded or unsupported operator encountered.
    pub fn blast_term(&mut self, id: TermId) -> Option<Vec<i32>> {
        if let Some(bits) = self.term_bits.get(&id) {
            return Some(bits.clone());
        }
        if self.exceeded { return None; }

        let term = self.tt.get(id);
        let width = term.width;
        let kind = term.kind.clone();

        let bits = match kind {
            TermKind::Const(v) => {
                let mut bits = Vec::with_capacity(width as usize);
                for i in 0..width {
                    if (v >> i) & 1 == 1 {
                        bits.push(self.true_lit);
                    } else {
                        bits.push(-self.true_lit);
                    }
                }
                bits
            }
            TermKind::Var(_) => {
                self.fresh_vars(width)
            }
            TermKind::App { op, args, slice_upper, slice_lower } => {
                // Recursively blast arguments
                let mut arg_bits: Vec<Vec<i32>> = Vec::with_capacity(args.len());
                for &arg in &args {
                    match self.blast_term(arg) {
                        Some(bits) => arg_bits.push(bits),
                        None => return None,
                    }
                }
                if self.exceeded { return None; }

                match op {
                    // Bitwise
                    OpKind::And => self.and_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Or => self.or_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Xor => self.xor_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Not => self.not_bits(&arg_bits[0]),

                    // Arithmetic
                    OpKind::Add => self.add_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Sub => self.sub_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Mul => {
                        // Bail on wide multiplies (> 32 bits creates O(n^2) gates)
                        if arg_bits[0].len() > 32 { return None; }
                        self.mul_bits(&arg_bits[0], &arg_bits[1])
                    }
                    OpKind::Neg => self.neg_bits(&arg_bits[0]),

                    // Comparisons (1-bit result)
                    OpKind::Eq => vec![self.eq_bits(&arg_bits[0], &arg_bits[1])],
                    OpKind::Neq => {
                        let eq = self.eq_bits(&arg_bits[0], &arg_bits[1]);
                        vec![-eq]
                    }
                    OpKind::Ult => vec![self.ult_bits(&arg_bits[0], &arg_bits[1])],
                    OpKind::Ulte => {
                        let lt = self.ult_bits(&arg_bits[1], &arg_bits[0]);
                        vec![-lt]
                    }
                    OpKind::Slt => vec![self.slt_bits(&arg_bits[0], &arg_bits[1])],
                    OpKind::Slte => {
                        let lt = self.slt_bits(&arg_bits[1], &arg_bits[0]);
                        vec![-lt]
                    }

                    // Reductions
                    OpKind::Redand => vec![self.redand_bits(&arg_bits[0])],
                    OpKind::Redor => vec![self.redor_bits(&arg_bits[0])],
                    OpKind::Redxor => vec![self.redxor_bits(&arg_bits[0])],

                    // ITE: per-bit mux
                    OpKind::Ite => {
                        let cond = arg_bits[0][0];
                        arg_bits[1].iter().zip(arg_bits[2].iter())
                            .map(|(&t, &e)| self.ite_gate(cond, t, e))
                            .collect()
                    }

                    // Data movement
                    OpKind::Concat => {
                        // BTOR2: concat(upper, lower) => lower bits ++ upper bits
                        let mut bits = arg_bits[1].clone();
                        bits.extend_from_slice(&arg_bits[0]);
                        bits
                    }
                    OpKind::Slice => {
                        arg_bits[0][slice_lower as usize..=slice_upper as usize].to_vec()
                    }
                    OpKind::Uext => {
                        let mut bits = arg_bits[0].clone();
                        let false_lit = -self.true_lit;
                        bits.resize(width as usize, false_lit);
                        bits
                    }
                    OpKind::Sext => {
                        let msb = *arg_bits[0].last().unwrap_or(&(-self.true_lit));
                        let mut bits = arg_bits[0].clone();
                        bits.resize(width as usize, msb);
                        bits
                    }

                    // Shifts
                    OpKind::Sll => self.sll_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Srl => self.srl_bits(&arg_bits[0], &arg_bits[1]),
                    OpKind::Sra => self.sra_bits(&arg_bits[0], &arg_bits[1]),

                    // Overflow detection
                    OpKind::Uaddo => {
                        let false_lit = -self.true_lit;
                        let (_, carry) = self.adder(&arg_bits[0], &arg_bits[1], false_lit);
                        vec![carry]
                    }
                    OpKind::Umulo => {
                        // Full double-width multiply to check overflow — bail for now
                        return None;
                    }

                    // Unsigned division/remainder
                    OpKind::Udiv => {
                        if arg_bits[0].len() > 32 { return None; }
                        let (quot, _) = self.udivrem_bits(&arg_bits[0], &arg_bits[1]);
                        quot
                    }
                    OpKind::Urem => {
                        if arg_bits[0].len() > 32 { return None; }
                        let (_, rem) = self.udivrem_bits(&arg_bits[0], &arg_bits[1]);
                        rem
                    }
                    // Signed division: convert to unsigned, divide, adjust sign
                    // BTOR2: sdiv rounds toward zero, srem sign matches dividend
                    OpKind::Sdiv => {
                        if arg_bits[0].len() > 32 { return None; }
                        let n = arg_bits[0].len();
                        let a_sign = arg_bits[0][n - 1];
                        let b_sign = arg_bits[1][n - 1];
                        // Absolute values
                        let abs_a = {
                            let neg = self.neg_bits(&arg_bits[0]);
                            (0..n).map(|i| self.ite_gate(a_sign, neg[i], arg_bits[0][i])).collect::<Vec<_>>()
                        };
                        let abs_b = {
                            let neg = self.neg_bits(&arg_bits[1]);
                            (0..n).map(|i| self.ite_gate(b_sign, neg[i], arg_bits[1][i])).collect::<Vec<_>>()
                        };
                        let (quot, _) = self.udivrem_bits(&abs_a, &abs_b);
                        // Negate result if signs differ
                        let neg_quot = self.neg_bits(&quot);
                        let diff_sign = self.xor_gate(a_sign, b_sign);
                        (0..n).map(|i| self.ite_gate(diff_sign, neg_quot[i], quot[i])).collect()
                    }
                    OpKind::Srem => {
                        if arg_bits[0].len() > 32 { return None; }
                        let n = arg_bits[0].len();
                        let a_sign = arg_bits[0][n - 1];
                        let b_sign = arg_bits[1][n - 1];
                        let abs_a = {
                            let neg = self.neg_bits(&arg_bits[0]);
                            (0..n).map(|i| self.ite_gate(a_sign, neg[i], arg_bits[0][i])).collect::<Vec<_>>()
                        };
                        let abs_b = {
                            let neg = self.neg_bits(&arg_bits[1]);
                            (0..n).map(|i| self.ite_gate(b_sign, neg[i], arg_bits[1][i])).collect::<Vec<_>>()
                        };
                        let (_, rem) = self.udivrem_bits(&abs_a, &abs_b);
                        // Remainder sign matches dividend
                        let neg_rem = self.neg_bits(&rem);
                        (0..n).map(|i| self.ite_gate(a_sign, neg_rem[i], rem[i])).collect()
                    }
                    // Signed modulo: result sign matches divisor
                    OpKind::Smod => {
                        if arg_bits[0].len() > 32 { return None; }
                        let n = arg_bits[0].len();
                        let a_sign = arg_bits[0][n - 1];
                        let b_sign = arg_bits[1][n - 1];
                        let abs_a = {
                            let neg = self.neg_bits(&arg_bits[0]);
                            (0..n).map(|i| self.ite_gate(a_sign, neg[i], arg_bits[0][i])).collect::<Vec<_>>()
                        };
                        let abs_b = {
                            let neg = self.neg_bits(&arg_bits[1]);
                            (0..n).map(|i| self.ite_gate(b_sign, neg[i], arg_bits[1][i])).collect::<Vec<_>>()
                        };
                        let (_, rem) = self.udivrem_bits(&abs_a, &abs_b);
                        // Check if remainder is zero
                        let rem_zero = {
                            let r = self.redor_bits(&rem);
                            -r
                        };
                        // If remainder is zero, result is zero
                        // Otherwise: if signs differ, result = b - rem; else result = rem
                        // (smod adjusts so result sign matches divisor)
                        let neg_rem = self.neg_bits(&rem);
                        let signed_rem: Vec<i32> = (0..n).map(|i| self.ite_gate(a_sign, neg_rem[i], rem[i])).collect();
                        let adjusted = self.add_bits(&signed_rem, &arg_bits[1]);
                        let diff_sign = self.xor_gate(a_sign, b_sign);
                        let need_adjust = self.and_gate(diff_sign, -rem_zero);
                        (0..n).map(|i| {
                            let v = self.ite_gate(need_adjust, adjusted[i], rem[i]);
                            self.ite_gate(rem_zero, -self.true_lit, v)
                        }).collect()
                    }

                    // Unsupported: memory
                    OpKind::Read | OpKind::Write => return None,
                }
            }
        };

        debug_assert_eq!(bits.len(), width as usize,
            "blast_term width mismatch: expected {}, got {} for {:?}",
            width, bits.len(), self.tt.get(id).kind);

        self.term_bits.insert(id, bits.clone());
        Some(bits)
    }

    /// Add target constraint: result bits must encode a value in the target set.
    fn add_target_constraint(&mut self, result_bits: &[i32], width: u16, target: &ValueSet) {
        if target.is_full() { return; }
        if target.is_empty() {
            // Force UNSAT
            self.add_clause(vec![self.true_lit, -self.true_lit]);
            self.add_clause(vec![-self.true_lit]);
            self.add_clause(vec![self.true_lit]);
            return;
        }

        // Constrain the lower min(width, 8) bits via blocking clauses
        let eff_w = width.min(8) as u32;
        let max_val = 1u32 << eff_w;

        for v in 0..max_val {
            if !target.contains(v as u8) {
                // Block value v: at least one bit must differ
                let mut clause = Vec::with_capacity(eff_w as usize);
                for i in 0..eff_w {
                    if (v >> i) & 1 == 1 {
                        clause.push(-result_bits[i as usize]);
                    } else {
                        clause.push(result_bits[i as usize]);
                    }
                }
                self.add_clause(clause);
            }
        }
    }

    /// Main entry point: bit-blast a term and solve.
    /// Returns (SolveResult, witness) where witness maps var_id -> concrete value.
    pub fn solve(
        &mut self,
        term: TermId,
        width: u16,
        target: &ValueSet,
    ) -> (SolveResult, HashMap<u32, u64>) {
        // Phase 1: Bit-blast the term DAG into CNF
        let result_bits = match self.blast_term(term) {
            Some(bits) => bits,
            None => return (SolveResult::Unknown, HashMap::new()),
        };
        if self.exceeded {
            return (SolveResult::Unknown, HashMap::new());
        }

        // Phase 2: Add target constraint
        self.add_target_constraint(&result_bits, width, target);
        if self.exceeded {
            return (SolveResult::Unknown, HashMap::new());
        }

        // Phase 3: Collect variable mapping for witness extraction
        let var_info: Vec<(u32, Vec<i32>)> = self.term_bits.iter()
            .filter_map(|(&tid, bits)| {
                if let TermKind::Var(var_id) = &self.tt.get(tid).kind {
                    Some((*var_id, bits.clone()))
                } else {
                    None
                }
            })
            .collect();

        // Phase 4: Invoke splr
        let clauses = std::mem::take(&mut self.clauses);

        match splr::Certificate::try_from(clauses) {
            Ok(splr::Certificate::SAT(model)) => {
                let mut witness = HashMap::new();
                for (var_id, bits) in &var_info {
                    let mut value: u64 = 0;
                    for (bit_idx, &sat_var) in bits.iter().enumerate() {
                        if is_true_in_model(&model, sat_var) {
                            value |= 1u64 << bit_idx;
                        }
                    }
                    witness.insert(*var_id, value);
                }
                (SolveResult::Sat, witness)
            }
            Ok(splr::Certificate::UNSAT) => {
                (SolveResult::Unsat, HashMap::new())
            }
            Err(_) => {
                (SolveResult::Unknown, HashMap::new())
            }
        }
    }
}

/// Check if a SAT variable is assigned true in the model.
/// Model format: model[var-1] is positive (true) or negative (false).
fn is_true_in_model(model: &[i32], lit: i32) -> bool {
    if lit > 0 {
        let idx = (lit - 1) as usize;
        idx < model.len() && model[idx] > 0
    } else if lit < 0 {
        let idx = (-lit - 1) as usize;
        idx < model.len() && model[idx] < 0
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermTable;

    #[test]
    fn test_bitblast_const_sat() {
        let mut tt = TermTable::new();
        // Constant 5 (width 8) in target set containing 5
        let c = tt.make_const(5, 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(5);

        let mut bb = BitBlaster::new(&tt);
        let (result, _) = bb.solve(c, 8, &target);
        assert_eq!(result, SolveResult::Sat);
    }

    #[test]
    fn test_bitblast_const_unsat() {
        let mut tt = TermTable::new();
        // Constant 5 (width 8) in target set NOT containing 5
        let c = tt.make_const(5, 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(3);
        target = target.insert(7);

        let mut bb = BitBlaster::new(&tt);
        let (result, _) = bb.solve(c, 8, &target);
        assert_eq!(result, SolveResult::Unsat);
    }

    #[test]
    fn test_bitblast_var_sat() {
        let mut tt = TermTable::new();
        // Variable x (width 4) in FULL target set — trivially SAT
        let x = tt.make_var(1, 4);
        let target = ValueSet::FULL;

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(x, 4, &target);
        assert_eq!(result, SolveResult::Sat);
        assert!(witness.contains_key(&1));
    }

    #[test]
    fn test_bitblast_add_sat() {
        let mut tt = TermTable::new();
        // x + 3 == 5, where x is 8-bit → x must be 2
        let x = tt.make_var(1, 8);
        let three = tt.make_const(3, 8);
        let sum = tt.make_app(OpKind::Add, vec![x, three], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(5);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(sum, 8, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!(witness[&1], 2);
    }

    #[test]
    fn test_bitblast_add_unsat() {
        let mut tt = TermTable::new();
        // x + x == 5 (8-bit) → no solution (5 is odd, x+x is always even)
        let x = tt.make_var(1, 8);
        let sum = tt.make_app(OpKind::Add, vec![x, x], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(5);

        let mut bb = BitBlaster::new(&tt);
        let (result, _) = bb.solve(sum, 8, &target);
        assert_eq!(result, SolveResult::Unsat);
    }

    #[test]
    fn test_bitblast_eq_sat() {
        let mut tt = TermTable::new();
        // EQ(x, 42) where x is 8-bit → SAT when target includes 1
        let x = tt.make_var(1, 8);
        let c42 = tt.make_const(42, 8);
        let eq = tt.make_app(OpKind::Eq, vec![x, c42], 1);
        let mut target = ValueSet::EMPTY;
        target = target.insert(1); // true

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(eq, 1, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!(witness[&1], 42);
    }

    #[test]
    fn test_bitblast_ult() {
        let mut tt = TermTable::new();
        // ULT(x, 3) where x is 4-bit → x can be 0, 1, 2
        let x = tt.make_var(1, 4);
        let three = tt.make_const(3, 4);
        let lt = tt.make_app(OpKind::Ult, vec![x, three], 1);
        let mut target = ValueSet::EMPTY;
        target = target.insert(1);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(lt, 1, &target);
        assert_eq!(result, SolveResult::Sat);
        assert!(witness[&1] < 3, "expected x < 3, got x = {}", witness[&1]);
    }

    #[test]
    fn test_bitblast_mul_sat() {
        let mut tt = TermTable::new();
        // x * 3 == 15 (8-bit) → x = 5
        let x = tt.make_var(1, 8);
        let three = tt.make_const(3, 8);
        let prod = tt.make_app(OpKind::Mul, vec![x, three], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(15);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(prod, 8, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!((witness[&1] * 3) & 0xFF, 15);
    }

    #[test]
    fn test_bitblast_shift_left() {
        let mut tt = TermTable::new();
        // SLL(1, x) == 4 (8-bit) → x = 2
        let one = tt.make_const(1, 8);
        let x = tt.make_var(1, 8);
        let sll = tt.make_app(OpKind::Sll, vec![one, x], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(4);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(sll, 8, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!((1u64 << witness[&1]) & 0xFF, 4);
    }

    #[test]
    fn test_bitblast_ite() {
        let mut tt = TermTable::new();
        // ITE(c, 10, 20) in target {10} → c must be true (1)
        let c = tt.make_var(1, 1);
        let ten = tt.make_const(10, 8);
        let twenty = tt.make_const(20, 8);
        let ite = tt.make_app(OpKind::Ite, vec![c, ten, twenty], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(10);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(ite, 8, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!(witness[&1], 1); // condition must be true
    }

    #[test]
    fn test_bitblast_concat_slice_roundtrip() {
        let mut tt = TermTable::new();
        // CONCAT(x[4bit], y[4bit]) then SLICE upper 4 bits == x
        let x = tt.make_var(1, 4);
        let y = tt.make_var(2, 4);
        let cat = tt.make_app(OpKind::Concat, vec![x, y], 8);
        // Slice [7:4] should be x
        let sliced = tt.make_slice(cat, 7, 4);
        // EQ(sliced, 5) → x = 5
        let five = tt.make_const(5, 4);
        let eq = tt.make_app(OpKind::Eq, vec![sliced, five], 1);
        let mut target = ValueSet::EMPTY;
        target = target.insert(1);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(eq, 1, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!(witness[&1], 5);
    }

    #[test]
    fn test_bitblast_udiv_sat() {
        let mut tt = TermTable::new();
        // 15 / x == 5 (8-bit) → x = 3
        let c15 = tt.make_const(15, 8);
        let x = tt.make_var(1, 8);
        let div = tt.make_app(OpKind::Udiv, vec![c15, x], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(5);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(div, 8, &target);
        assert_eq!(result, SolveResult::Sat);
        assert_eq!(witness[&1], 3);
    }

    #[test]
    fn test_bitblast_urem_sat() {
        let mut tt = TermTable::new();
        // 17 % x == 2 (8-bit) → x could be 3, 5, 15
        let c17 = tt.make_const(17, 8);
        let x = tt.make_var(1, 8);
        let rem = tt.make_app(OpKind::Urem, vec![c17, x], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(2);

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(rem, 8, &target);
        assert_eq!(result, SolveResult::Sat);
        let vx = witness[&1];
        assert!(vx > 0 && 17 % vx == 2, "17 % {} != 2", vx);
    }

    #[test]
    fn test_bitblast_udiv_by_zero() {
        let mut tt = TermTable::new();
        // 42 / 0 == 255 (8-bit, BTOR2: div by zero = all-ones)
        let c42 = tt.make_const(42, 8);
        let zero = tt.make_const(0, 8);
        let div = tt.make_app(OpKind::Udiv, vec![c42, zero], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(255);

        let mut bb = BitBlaster::new(&tt);
        let (result, _) = bb.solve(div, 8, &target);
        assert_eq!(result, SolveResult::Sat);
    }

    #[test]
    fn test_bitblast_sdiv_sat() {
        let mut tt = TermTable::new();
        // (-6) / 3 == -2 (8-bit signed)
        // -6 = 0xFA = 250, 3 = 3, -2 = 0xFE = 254
        let neg6 = tt.make_const(250, 8); // -6 in two's complement
        let three = tt.make_const(3, 8);
        let div = tt.make_app(OpKind::Sdiv, vec![neg6, three], 8);
        let mut target = ValueSet::EMPTY;
        target = target.insert(254); // -2 & 0xFF

        let mut bb = BitBlaster::new(&tt);
        let (result, _) = bb.solve(div, 8, &target);
        assert_eq!(result, SolveResult::Sat);
    }

    #[test]
    fn test_bitblast_two_vars_16bit() {
        let mut tt = TermTable::new();
        // x + y == 1000 (16-bit) — SAT with many solutions
        let x = tt.make_var(1, 16);
        let y = tt.make_var(2, 16);
        let sum = tt.make_app(OpKind::Add, vec![x, y], 16);
        // Target: lower byte of 1000 = 0xE8 = 232
        let mut target = ValueSet::EMPTY;
        target = target.insert(232); // 1000 & 0xFF

        let mut bb = BitBlaster::new(&tt);
        let (result, witness) = bb.solve(sum, 16, &target);
        assert_eq!(result, SolveResult::Sat);
        let vx = witness[&1];
        let vy = witness[&2];
        assert_eq!((vx + vy) & 0xFF, 232);
    }
}
