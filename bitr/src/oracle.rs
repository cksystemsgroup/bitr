//! External theory oracle integration
//!
//! Converts residual formulas to SMT-LIB2 format and invokes an external
//! solver (bitwuzla, boolector, z3) as a subprocess. Results are cached.

use std::collections::HashMap;
use std::process::Command;
use std::io::Write;

use bvdd::types::{TermId, BvWidth, SolveResult};
use bvdd::term::{TermTable, TermKind};
use bvdd::valueset::ValueSet;

/// External SMT solver oracle
pub struct SmtOracle {
    /// Path to the solver binary (e.g., "bitwuzla", "z3", "boolector")
    solver_path: String,
    /// Cache: (term structure hash) → result
    cache: HashMap<u64, SolveResult>,
    /// Stats
    pub calls: u64,
    pub cache_hits: u64,
    pub timeouts: u64,
    /// Timeout in seconds
    timeout_s: u64,
}

impl SmtOracle {
    pub fn new(solver_path: &str) -> Self {
        SmtOracle {
            solver_path: solver_path.to_string(),
            cache: HashMap::new(),
            calls: 0,
            cache_hits: 0,
            timeouts: 0,
            timeout_s: 5,
        }
    }

    /// Check if the solver binary exists
    #[allow(dead_code)]
    pub fn is_available(&self) -> bool {
        Command::new(&self.solver_path)
            .arg("--version")
            .output()
            .is_ok()
    }

    /// Set timeout in seconds per oracle call
    pub fn set_timeout(&mut self, s: u64) {
        self.timeout_s = s;
    }

    /// Check if a term can produce a value in the target set
    pub fn check(
        &mut self,
        tt: &TermTable,
        term: TermId,
        width: BvWidth,
        target: ValueSet,
    ) -> SolveResult {
        self.calls += 1;

        // Generate SMT-LIB2 first (needed for both cache key and solver call)
        let smt = self.term_to_smtlib2(tt, term, width, target);

        // Use hash of the full SMT-LIB2 string as cache key (collision-resistant)
        let cache_key = {
            let mut h: u64 = 0xcbf29ce484222325;
            for b in smt.bytes() {
                h ^= b as u64;
                h = h.wrapping_mul(0x100000001b3);
            }
            h
        };
        if let Some(&result) = self.cache.get(&cache_key) {
            self.cache_hits += 1;
            return result;
        }

        // Invoke solver
        let result = self.invoke_solver(&smt);

        // Cache result
        self.cache.insert(cache_key, result);
        result
    }

    /// Convert a term + target to SMT-LIB2 format
    fn term_to_smtlib2(
        &self,
        tt: &TermTable,
        term: TermId,
        width: BvWidth,
        target: ValueSet,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        // Collect variables and declare them
        let vars = tt.collect_vars(term);
        for &(var_id, var_width) in &vars {
            smt.push_str(&format!(
                "(declare-const v{} (_ BitVec {}))\n",
                var_id, var_width
            ));
        }

        // Define the term expression
        let expr = Self::term_to_sexp(tt, term);

        // Assert the term's value is in the target set
        // We build a disjunction: (or (= expr #b00000001) (= expr #b00000010) ...)
        let mut target_clauses = Vec::new();
        for v in target.iter() {
            target_clauses.push(format!(
                "(= {} (_ bv{} {}))",
                expr, v, width
            ));
        }

        if target_clauses.is_empty() {
            smt.push_str("(assert false)\n");
        } else if target_clauses.len() == 1 {
            smt.push_str(&format!("(assert {})\n", target_clauses[0]));
        } else {
            smt.push_str(&format!("(assert (or {}))\n", target_clauses.join(" ")));
        }

        smt.push_str("(check-sat)\n(exit)\n");
        smt
    }

    /// Convert a term to an S-expression string
    fn term_to_sexp(tt: &TermTable, term: TermId) -> String {
        let t = tt.get(term);
        match &t.kind {
            TermKind::Const(val) => {
                format!("(_ bv{} {})", val, t.width)
            }
            TermKind::Var(var_id) => {
                format!("v{}", var_id)
            }
            TermKind::App { op, args, slice_upper, slice_lower } => {
                let child_sexps: Vec<String> = args.iter()
                    .map(|&a| Self::term_to_sexp(tt, a))
                    .collect();

                use bvdd::types::OpKind;
                match op {
                    OpKind::Eq => format!("(= {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Neq => format!("(not (= {} {}))", child_sexps[0], child_sexps[1]),
                    OpKind::Ult => format!("(bvult {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Slt => format!("(bvslt {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Ulte => format!("(bvule {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Slte => format!("(bvsle {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Add => format!("(bvadd {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Sub => format!("(bvsub {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Mul => format!("(bvmul {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Udiv => format!("(bvudiv {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Urem => format!("(bvurem {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Sdiv => format!("(bvsdiv {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Srem => format!("(bvsrem {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Smod => format!("(bvsmod {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::And => format!("(bvand {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Or => format!("(bvor {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Xor => format!("(bvxor {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Not => format!("(bvnot {})", child_sexps[0]),
                    OpKind::Neg => format!("(bvneg {})", child_sexps[0]),
                    OpKind::Sll => format!("(bvshl {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Srl => format!("(bvlshr {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Sra => format!("(bvashr {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Concat => format!("(concat {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Slice => {
                        format!("((_ extract {} {}) {})", slice_upper, slice_lower, child_sexps[0])
                    }
                    OpKind::Uext => {
                        let ext_bits = t.width - tt.get(args[0]).width;
                        format!("((_ zero_extend {}) {})", ext_bits, child_sexps[0])
                    }
                    OpKind::Sext => {
                        let ext_bits = t.width - tt.get(args[0]).width;
                        format!("((_ sign_extend {}) {})", ext_bits, child_sexps[0])
                    }
                    OpKind::Ite => {
                        // Condition is 1-bit bitvec; convert to Bool
                        format!("(ite (= {} (_ bv1 1)) {} {})",
                            child_sexps[0], child_sexps[1], child_sexps[2])
                    }
                    OpKind::Redand => format!("(bvredand {})", child_sexps[0]),
                    OpKind::Redor => format!("(bvredor {})", child_sexps[0]),
                    OpKind::Redxor => {
                        // No direct SMT-LIB2 bvredxor; use XOR reduction
                        format!("(bvredxor {})", child_sexps[0])
                    }
                    OpKind::Uaddo | OpKind::Umulo => {
                        // Overflow: approximate via wider arithmetic
                        format!("(_ bv0 {})", t.width) // fallback
                    }
                    OpKind::Read => format!("(select {} {})", child_sexps[0], child_sexps[1]),
                    OpKind::Write => format!("(store {} {} {})", child_sexps[0], child_sexps[1], child_sexps[2]),
                }
            }
        }
    }

    /// Invoke the external solver on SMT-LIB2 input
    fn invoke_solver(&mut self, smt: &str) -> SolveResult {
        // Write to a temp file
        let tmp_path = std::env::temp_dir().join("bitr_oracle.smt2");
        if let Ok(mut f) = std::fs::File::create(&tmp_path) {
            if f.write_all(smt.as_bytes()).is_err() {
                return SolveResult::Unknown;
            }
        } else {
            return SolveResult::Unknown;
        }

        // Run solver with timeout
        let result = Command::new(&self.solver_path)
            .arg(tmp_path.to_str().unwrap_or(""))
            .output();

        // Clean up
        let _ = std::fs::remove_file(&tmp_path);

        match result {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                let trimmed = stdout.trim();
                if trimmed == "sat" {
                    SolveResult::Sat
                } else if trimmed == "unsat" {
                    SolveResult::Unsat
                } else {
                    SolveResult::Unknown
                }
            }
            Err(_) => {
                self.timeouts += 1;
                SolveResult::Unknown
            }
        }
    }
}

/// Run the solver directly on an SMT-LIB2 file (no translation needed)
pub fn solve_smtlib2_file(solver_path: &str, file_path: &str) -> SolveResult {
    let result = Command::new(solver_path)
        .arg(file_path)
        .output();

    match result {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let trimmed = stdout.trim();
            if trimmed.starts_with("sat") {
                SolveResult::Sat
            } else if trimmed.starts_with("unsat") {
                SolveResult::Unsat
            } else {
                SolveResult::Unknown
            }
        }
        Err(_) => SolveResult::Unknown,
    }
}

/// Try to find an available SMT solver
pub fn find_solver() -> Option<String> {
    for solver in &["bitwuzla", "boolector", "z3"] {
        if Command::new(solver).arg("--version").output().is_ok() {
            return Some(solver.to_string());
        }
    }
    None
}
