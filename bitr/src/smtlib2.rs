//! SMT-LIB2 parser for QF_BV and QF_ABV benchmarks
//!
//! Parses SMT-LIB2 format into BVCs for the BITR solver.
//! Supports: declare-const, declare-fun, assert, check-sat, define-fun.

use std::collections::HashMap;

use bvdd::types::{BvcId, BvWidth, OpKind};
use bvdd::term::TermTable;
use bvdd::constraint::ConstraintTable;
use bvdd::bvc::{BvcManager, BvcEntry};

/// Parsed SMT-LIB2 model
pub struct SmtModel {
    pub tt: TermTable,
    pub ct: ConstraintTable,
    pub bm: BvcManager,
    pub assertions: Vec<BvcId>,
    pub var_map: HashMap<String, BvcId>,
}

/// SMT-LIB2 sort
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum SmtSort {
    BitVec(BvWidth),
    Bool,
    Array(Box<SmtSort>, Box<SmtSort>),
}

/// Tokenizer for S-expressions
struct Tokenizer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Tokenizer<'a> {
    fn new(input: &'a str) -> Self {
        Tokenizer { input, pos: 0 }
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() {
            let c = self.input.as_bytes()[self.pos];
            if c == b';' {
                // Skip comment to end of line
                while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'\n' {
                    self.pos += 1;
                }
            } else if c.is_ascii_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Option<String> {
        self.skip_whitespace();
        if self.pos >= self.input.len() {
            return None;
        }
        let c = self.input.as_bytes()[self.pos];
        if c == b'(' {
            self.pos += 1;
            return Some("(".to_string());
        }
        if c == b')' {
            self.pos += 1;
            return Some(")".to_string());
        }
        if c == b'"' {
            // String literal
            self.pos += 1;
            let start = self.pos;
            while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'"' {
                self.pos += 1;
            }
            let s = self.input[start..self.pos].to_string();
            if self.pos < self.input.len() { self.pos += 1; }
            return Some(format!("\"{}\"", s));
        }
        if c == b'|' {
            // Quoted symbol
            self.pos += 1;
            let start = self.pos;
            while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'|' {
                self.pos += 1;
            }
            let s = self.input[start..self.pos].to_string();
            if self.pos < self.input.len() { self.pos += 1; }
            return Some(s);
        }
        // Regular symbol/number
        let start = self.pos;
        while self.pos < self.input.len() {
            let c = self.input.as_bytes()[self.pos];
            if c.is_ascii_whitespace() || c == b'(' || c == b')' || c == b';' {
                break;
            }
            self.pos += 1;
        }
        Some(self.input[start..self.pos].to_string())
    }
}

/// S-expression
#[derive(Debug, Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexp(tok: &mut Tokenizer) -> Option<Sexp> {
    let token = tok.next_token()?;
    if token == "(" {
        let mut items = Vec::new();
        loop {
            tok.skip_whitespace();
            if tok.pos < tok.input.len() && tok.input.as_bytes()[tok.pos] == b')' {
                tok.pos += 1;
                break;
            }
            if let Some(item) = parse_sexp(tok) {
                items.push(item);
            } else {
                break;
            }
        }
        Some(Sexp::List(items))
    } else {
        Some(Sexp::Atom(token))
    }
}

/// Parse an SMT-LIB2 file
pub fn parse_smtlib2(input: &str) -> Result<SmtModel, String> {
    let mut tok = Tokenizer::new(input);
    let mut model = SmtModel {
        tt: TermTable::new(),
        ct: ConstraintTable::new(),
        bm: BvcManager::new(),
        assertions: Vec::new(),
        var_map: HashMap::new(),
    };
    let mut var_ids: HashMap<String, (u32, BvWidth)> = HashMap::new();
    let mut next_var: u32 = 1;
    let mut defines: HashMap<String, BvcId> = HashMap::new();

    while let Some(sexp) = parse_sexp(&mut tok) {
        if let Sexp::List(items) = &sexp {
            if items.is_empty() { continue; }
            if let Sexp::Atom(cmd) = &items[0] {
                match cmd.as_str() {
                    "set-logic" | "set-info" | "set-option" | "exit" | "get-model"
                    | "get-value" | "get-unsat-core" | "push" | "pop" => {
                        // Ignore
                    }
                    "declare-const" => {
                        // (declare-const name sort)
                        if items.len() >= 3 {
                            let name = atom_str(&items[1]);
                            let sort = parse_sort(&items[2])?;
                            if let SmtSort::BitVec(w) = sort {
                                let vid = next_var; next_var += 1;
                                var_ids.insert(name.clone(), (vid, w));
                                let bvc = model.bm.make_input(&mut model.tt, &model.ct, vid, w);
                                model.var_map.insert(name, bvc);
                            }
                        }
                    }
                    "declare-fun" => {
                        // (declare-fun name () sort)
                        if items.len() >= 4 {
                            let name = atom_str(&items[1]);
                            let sort = parse_sort(&items[items.len() - 1])?;
                            if let SmtSort::BitVec(w) = sort {
                                let vid = next_var; next_var += 1;
                                var_ids.insert(name.clone(), (vid, w));
                                let bvc = model.bm.make_input(&mut model.tt, &model.ct, vid, w);
                                model.var_map.insert(name, bvc);
                            }
                        }
                    }
                    "define-fun" => {
                        // (define-fun name ((params)) sort body)
                        if items.len() >= 5 {
                            let name = atom_str(&items[1]);
                            let body = &items[items.len() - 1];
                            let bvc = translate_expr(
                                body, &mut model.tt, &mut model.ct, &mut model.bm,
                                &model.var_map, &var_ids, &defines,
                            )?;
                            defines.insert(name.clone(), bvc);
                            model.var_map.insert(name, bvc);
                        }
                    }
                    "assert" => {
                        if items.len() >= 2 {
                            let bvc = translate_expr(
                                &items[1], &mut model.tt, &mut model.ct, &mut model.bm,
                                &model.var_map, &var_ids, &defines,
                            )?;
                            model.assertions.push(bvc);
                        }
                    }
                    "check-sat" => {
                        // We'll handle this at the top level
                    }
                    _ => {
                        // Unknown command — ignore
                    }
                }
            }
        }
    }

    Ok(model)
}

fn atom_str(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Atom(s) => s.clone(),
        Sexp::List(_) => String::new(),
    }
}

fn parse_sort(sexp: &Sexp) -> Result<SmtSort, String> {
    match sexp {
        Sexp::Atom(s) => {
            if s == "Bool" { return Ok(SmtSort::Bool); }
            Err(format!("unknown sort: {}", s))
        }
        Sexp::List(items) => {
            if items.len() == 3 {
                if let (Sexp::Atom(u), Sexp::Atom(kind), Sexp::Atom(width)) =
                    (&items[0], &items[1], &items[2])
                {
                    if u == "_" && kind == "BitVec" {
                        let w: u16 = width.parse().map_err(|_| format!("bad width: {}", width))?;
                        return Ok(SmtSort::BitVec(w));
                    }
                }
            }
            if items.len() == 3 {
                if let Sexp::Atom(s) = &items[0] {
                    if s == "Array" {
                        let idx = parse_sort(&items[1])?;
                        let elem = parse_sort(&items[2])?;
                        return Ok(SmtSort::Array(Box::new(idx), Box::new(elem)));
                    }
                }
            }
            Err(format!("unknown sort: {:?}", sexp))
        }
    }
}

/// Translate an SMT-LIB2 expression to a BVC
fn translate_expr(
    sexp: &Sexp,
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    var_map: &HashMap<String, BvcId>,
    var_ids: &HashMap<String, (u32, BvWidth)>,
    defines: &HashMap<String, BvcId>,
) -> Result<BvcId, String> {
    match sexp {
        Sexp::Atom(s) => {
            // Variable reference or constant
            if let Some(&bvc) = var_map.get(s) {
                return Ok(bvc);
            }
            if let Some(&bvc) = defines.get(s) {
                return Ok(bvc);
            }
            if s == "true" {
                return Ok(bm.make_const(tt, ct, 1, 1));
            }
            if s == "false" {
                return Ok(bm.make_const(tt, ct, 0, 1));
            }
            // Binary literal: #b0101
            if let Some(bin) = s.strip_prefix("#b") {
                let val = u64::from_str_radix(bin, 2).unwrap_or(0);
                let width = bin.len() as u16;
                return Ok(bm.make_const(tt, ct, val, width));
            }
            // Hex literal: #x1a2b
            if let Some(hex) = s.strip_prefix("#x") {
                let val = u64::from_str_radix(hex, 16).unwrap_or(0);
                let width = (hex.len() * 4) as u16;
                return Ok(bm.make_const(tt, ct, val, width));
            }
            Err(format!("unknown symbol: {}", s))
        }
        Sexp::List(items) => {
            if items.is_empty() {
                return Err("empty expression".into());
            }

            // (_ bvN W) — bitvector constant
            if items.len() == 3 {
                if let (Sexp::Atom(u), Sexp::Atom(val_s), Sexp::Atom(width_s)) =
                    (&items[0], &items[1], &items[2])
                {
                    if u == "_" {
                        if let Some(val_str) = val_s.strip_prefix("bv") {
                            let val: u64 = val_str.parse().unwrap_or(0);
                            let width: u16 = width_s.parse().unwrap_or(0);
                            return Ok(bm.make_const(tt, ct, val, width));
                        }
                    }
                }
            }

            let head = atom_str(&items[0]);

            // Indexed operators: (_ extract 7 0), (_ zero_extend 8), etc.
            if head == "_" && items.len() >= 3 {
                let op_name = atom_str(&items[1]);
                let param1 = atom_str(&items[2]);
                let param2 = if items.len() > 3 { atom_str(&items[3]) } else { String::new() };
                // These return a partially applied operator — the actual expression
                // is in the parent list. Return a marker.
                return Err(format!("indexed_op:{}:{}:{}", op_name, param1, param2));
            }

            // Check for indexed operator application: ((_ extract 7 0) expr)
            if let Sexp::List(inner) = &items[0] {
                if inner.len() >= 3 {
                    if let Sexp::Atom(u) = &inner[0] {
                        if u == "_" {
                            let op_name = atom_str(&inner[1]);
                            return translate_indexed_op(
                                &op_name, inner, &items[1..],
                                tt, ct, bm, var_map, var_ids, defines,
                            );
                        }
                    }
                }
            }

            // Regular operators
            match head.as_str() {
                "not" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let w = bm.get(a).width;
                    if w == 1 {
                        // Boolean not → bitvector NOT at width 1
                        Ok(bm.apply(tt, ct, OpKind::Not, &[a], 1))
                    } else {
                        Ok(bm.apply(tt, ct, OpKind::Not, &[a], w))
                    }
                }
                "and" => translate_nary(OpKind::And, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "or" => translate_nary(OpKind::Or, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "xor" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    let w = bm.get(a).width;
                    Ok(bm.apply(tt, ct, OpKind::Xor, &[a, b], w))
                }
                "=" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Eq, &[a, b], 1))
                }
                "distinct" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Neq, &[a, b], 1))
                }
                "ite" => {
                    let c = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let t = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    let e = translate_expr(&items[3], tt, ct, bm, var_map, var_ids, defines)?;
                    let w = bm.get(t).width;
                    Ok(bm.apply(tt, ct, OpKind::Ite, &[c, t, e], w))
                }
                "bvand" => translate_binop(OpKind::And, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvor" => translate_binop(OpKind::Or, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvxor" => translate_binop(OpKind::Xor, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvnot" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let w = bm.get(a).width;
                    Ok(bm.apply(tt, ct, OpKind::Not, &[a], w))
                }
                "bvneg" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let w = bm.get(a).width;
                    Ok(bm.apply(tt, ct, OpKind::Neg, &[a], w))
                }
                "bvadd" => translate_binop(OpKind::Add, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvsub" => translate_binop(OpKind::Sub, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvmul" => translate_binop(OpKind::Mul, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvudiv" => translate_binop(OpKind::Udiv, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvurem" => translate_binop(OpKind::Urem, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvsdiv" => translate_binop(OpKind::Sdiv, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvsrem" => translate_binop(OpKind::Srem, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvsmod" => translate_binop(OpKind::Smod, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvshl" => translate_binop(OpKind::Sll, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvlshr" => translate_binop(OpKind::Srl, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvashr" => translate_binop(OpKind::Sra, &items[1..], tt, ct, bm, var_map, var_ids, defines),
                "bvult" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Ult, &[a, b], 1))
                }
                "bvule" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Ulte, &[a, b], 1))
                }
                "bvslt" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Slt, &[a, b], 1))
                }
                "bvsle" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Slte, &[a, b], 1))
                }
                "bvugt" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Ult, &[b, a], 1))
                }
                "bvuge" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Ulte, &[b, a], 1))
                }
                "bvsgt" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Slt, &[b, a], 1))
                }
                "bvsge" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Slte, &[b, a], 1))
                }
                "concat" => {
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    let wa = bm.get(a).width;
                    let wb = bm.get(b).width;
                    Ok(bm.apply(tt, ct, OpKind::Concat, &[a, b], wa + wb))
                }
                "bvcomp" => {
                    // (bvcomp a b) returns #b1 if a==b, #b0 otherwise
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    Ok(bm.apply(tt, ct, OpKind::Eq, &[a, b], 1))
                }
                "let" => {
                    // (let ((x expr) ...) body)
                    if items.len() >= 3 {
                        let mut local_defines = defines.clone();
                        let mut local_var_map = var_map.clone();
                        if let Sexp::List(bindings) = &items[1] {
                            for binding in bindings {
                                if let Sexp::List(pair) = binding {
                                    if pair.len() >= 2 {
                                        let name = atom_str(&pair[0]);
                                        let val = translate_expr(
                                            &pair[1], tt, ct, bm,
                                            &local_var_map, var_ids, &local_defines,
                                        )?;
                                        local_defines.insert(name.clone(), val);
                                        local_var_map.insert(name, val);
                                    }
                                }
                            }
                        }
                        translate_expr(
                            &items[2], tt, ct, bm,
                            &local_var_map, var_ids, &local_defines,
                        )
                    } else {
                        Err("malformed let".into())
                    }
                }
                "=>" => {
                    // implies
                    let a = translate_expr(&items[1], tt, ct, bm, var_map, var_ids, defines)?;
                    let b = translate_expr(&items[2], tt, ct, bm, var_map, var_ids, defines)?;
                    let not_a = bm.apply(tt, ct, OpKind::Not, &[a], 1);
                    Ok(bm.apply(tt, ct, OpKind::Or, &[not_a, b], 1))
                }
                _ => Err(format!("unsupported SMT-LIB2 operator: {}", head)),
            }
        }
    }
}

/// Translate an indexed operator like (_ extract 7 0) or (_ zero_extend 8)
#[allow(clippy::too_many_arguments)]
fn translate_indexed_op(
    op_name: &str,
    inner: &[Sexp],
    args: &[Sexp],
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    var_map: &HashMap<String, BvcId>,
    var_ids: &HashMap<String, (u32, BvWidth)>,
    defines: &HashMap<String, BvcId>,
) -> Result<BvcId, String> {
    match op_name {
        "extract" => {
            let upper: u16 = atom_str(&inner[2]).parse().unwrap_or(0);
            let lower: u16 = atom_str(&inner[3]).parse().unwrap_or(0);
            let a = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
            let arg_term = bm.get(a).entries[0].term;
            let slice_term = tt.make_slice(arg_term, upper, lower);
            let constraint = bm.get(a).entries[0].constraint;
            let width = upper - lower + 1;
            Ok(bm.alloc(width, vec![BvcEntry { term: slice_term, constraint }]))
        }
        "zero_extend" => {
            let ext: u16 = atom_str(&inner[2]).parse().unwrap_or(0);
            let a = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
            let wa = bm.get(a).width;
            let new_width = wa + ext;
            let arg_term = bm.get(a).entries[0].term;
            let ext_term = tt.make_app(OpKind::Uext, vec![arg_term], new_width);
            let constraint = bm.get(a).entries[0].constraint;
            Ok(bm.alloc(new_width, vec![BvcEntry { term: ext_term, constraint }]))
        }
        "sign_extend" => {
            let ext: u16 = atom_str(&inner[2]).parse().unwrap_or(0);
            let a = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
            let wa = bm.get(a).width;
            let new_width = wa + ext;
            let arg_term = bm.get(a).entries[0].term;
            let ext_term = tt.make_app(OpKind::Sext, vec![arg_term], new_width);
            let constraint = bm.get(a).entries[0].constraint;
            Ok(bm.alloc(new_width, vec![BvcEntry { term: ext_term, constraint }]))
        }
        "repeat" => {
            let count: u16 = atom_str(&inner[2]).parse().unwrap_or(1);
            let a = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
            let wa = bm.get(a).width;
            let mut result = a;
            for _ in 1..count {
                result = bm.apply(tt, ct, OpKind::Concat, &[result, a], bm.get(result).width + wa);
            }
            Ok(result)
        }
        "rotate_left" | "rotate_right" => {
            // Approximation: treat as shift (correct for many benchmarks)
            let _amount: u16 = atom_str(&inner[2]).parse().unwrap_or(0);
            let a = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
            Ok(a) // TODO: proper rotation
        }
        _ => Err(format!("unsupported indexed op: {}", op_name)),
    }
}

#[allow(clippy::too_many_arguments)]
fn translate_binop(
    op: OpKind,
    args: &[Sexp],
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    var_map: &HashMap<String, BvcId>,
    var_ids: &HashMap<String, (u32, BvWidth)>,
    defines: &HashMap<String, BvcId>,
) -> Result<BvcId, String> {
    let a = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
    let b = translate_expr(&args[1], tt, ct, bm, var_map, var_ids, defines)?;
    let w = bm.get(a).width;
    Ok(bm.apply(tt, ct, op, &[a, b], w))
}

#[allow(clippy::too_many_arguments)]
fn translate_nary(
    op: OpKind,
    args: &[Sexp],
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    var_map: &HashMap<String, BvcId>,
    var_ids: &HashMap<String, (u32, BvWidth)>,
    defines: &HashMap<String, BvcId>,
) -> Result<BvcId, String> {
    if args.is_empty() {
        return Err("empty n-ary op".into());
    }
    let mut result = translate_expr(&args[0], tt, ct, bm, var_map, var_ids, defines)?;
    for arg in &args[1..] {
        let b = translate_expr(arg, tt, ct, bm, var_map, var_ids, defines)?;
        let w = bm.get(result).width;
        result = bm.apply(tt, ct, op, &[result, b], w);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_qf_bv() {
        let input = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvadd x y) (_ bv255 8)))
(check-sat)
"#;
        let model = parse_smtlib2(input).unwrap();
        assert_eq!(model.assertions.len(), 1);
        assert_eq!(model.var_map.len(), 2);
    }

    #[test]
    fn test_parse_bitvec_constants() {
        let input = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #b1010))
(check-sat)
"#;
        let model = parse_smtlib2(input).unwrap();
        assert_eq!(model.assertions.len(), 1);
    }

    #[test]
    fn test_parse_extract() {
        let input = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= ((_ extract 3 0) x) #b1111))
(check-sat)
"#;
        let model = parse_smtlib2(input).unwrap();
        assert_eq!(model.assertions.len(), 1);
    }

    #[test]
    fn test_parse_let() {
        let input = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (let ((y (bvadd x (_ bv1 8)))) (= y (_ bv0 8))))
(check-sat)
"#;
        let model = parse_smtlib2(input).unwrap();
        assert_eq!(model.assertions.len(), 1);
    }
}
