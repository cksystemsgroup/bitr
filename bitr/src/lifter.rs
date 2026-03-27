//! BTOR2 → BVC lifter
//!
//! Maps parsed BTOR2 nodes to BVCs in the BVDD framework.
//! Structural operators create PRED constraints; non-structural
//! operators are lifted to fresh variables.

use std::collections::HashMap;

use bvdd::types::{BvcId, BvWidth, OpKind};
use bvdd::term::TermTable;
use bvdd::constraint::ConstraintTable;
use bvdd::bvc::{BvcManager, BvcEntry};

use crate::btor2::{Btor2Model, Btor2Sort};

/// Tracks array state for ROW expansion
#[derive(Clone, Debug)]
enum ArrayState {
    /// Base array (unconstrained input)
    Base { nid: u32, index_width: BvWidth, element_width: BvWidth },
    /// Write: store(base, addr, val)
    Write {
        base: Box<ArrayState>,
        addr_bvc: BvcId,
        val_bvc: BvcId,
        index_width: BvWidth,
        element_width: BvWidth,
    },
}

/// Result of lifting a BTOR2 model
pub struct LiftedModel {
    pub tt: TermTable,
    pub ct: ConstraintTable,
    pub bm: BvcManager,
    /// Map from BTOR2 nid to BvcId
    pub nid_to_bvc: HashMap<u32, BvcId>,
    /// Bad property BVC IDs
    pub bad_properties: Vec<BvcId>,
    /// State variables: (nid, init_bvc, next_bvc)
    pub states: Vec<(u32, Option<BvcId>, Option<BvcId>)>,
    /// Constraint BVC IDs (assumptions)
    pub constraints: Vec<BvcId>,
    /// Input variables: (nid, width) — for BMC fresh-renaming
    pub inputs: Vec<(u32, BvWidth)>,
}

/// Map a BTOR2 operator name to an OpKind
fn map_op(name: &str) -> Option<OpKind> {
    match name {
        "eq" => Some(OpKind::Eq),
        "neq" => Some(OpKind::Neq),
        "ult" => Some(OpKind::Ult),
        "slt" => Some(OpKind::Slt),
        "ulte" => Some(OpKind::Ulte),
        "slte" => Some(OpKind::Slte),
        "ugt" | "sgt" | "ugte" | "sgte" => None, // handled by swapping args
        "add" => Some(OpKind::Add),
        "sub" => Some(OpKind::Sub),
        "mul" => Some(OpKind::Mul),
        "udiv" => Some(OpKind::Udiv),
        "urem" => Some(OpKind::Urem),
        "sdiv" => Some(OpKind::Sdiv),
        "srem" => Some(OpKind::Srem),
        "smod" => Some(OpKind::Smod),
        "and" => Some(OpKind::And),
        "or" => Some(OpKind::Or),
        "xor" => Some(OpKind::Xor),
        "not" => Some(OpKind::Not),
        "neg" => Some(OpKind::Neg),
        "sll" => Some(OpKind::Sll),
        "srl" => Some(OpKind::Srl),
        "sra" => Some(OpKind::Sra),
        "slice" => Some(OpKind::Slice),
        "uext" => Some(OpKind::Uext),
        "sext" => Some(OpKind::Sext),
        "concat" => Some(OpKind::Concat),
        "ite" => Some(OpKind::Ite),
        "read" => Some(OpKind::Read),
        "write" => Some(OpKind::Write),
        "redand" => Some(OpKind::Redand),
        "redor" => Some(OpKind::Redor),
        "redxor" => Some(OpKind::Redxor),
        "uaddo" => Some(OpKind::Uaddo),
        "umulo" => Some(OpKind::Umulo),
        // Derived ops (not in OpKind — handled as combinations)
        "xnor" | "implies" | "nand" | "nor" => None,
        _ => None,
    }
}

/// Lift a BTOR2 model into BVCs
pub fn lift_btor2(model: &Btor2Model) -> Result<LiftedModel, String> {
    let mut tt = TermTable::new();
    let mut ct = ConstraintTable::new();
    let mut bm = BvcManager::new();
    let mut nid_to_bvc: HashMap<u32, BvcId> = HashMap::new();
    let mut nid_to_array: HashMap<u32, ArrayState> = HashMap::new();
    let mut sort_map: HashMap<u32, Btor2Sort> = HashMap::new();
    let mut bad_properties = Vec::new();
    let mut states: Vec<(u32, Option<BvcId>, Option<BvcId>)> = Vec::new();
    let mut constraints = Vec::new();
    let mut inputs = Vec::new();

    // Index sorts
    for (nid, sort) in &model.sorts {
        sort_map.insert(*nid, sort.clone());
    }

    // Helper: resolve sort to bitvec width
    let get_width = |sort_id: u32| -> Result<BvWidth, String> {
        match sort_map.get(&sort_id) {
            Some(Btor2Sort::Bitvec(w)) => Ok(*w),
            Some(Btor2Sort::Array { element_width, .. }) => Ok(*element_width),
            None => Err(format!("unknown sort id {}", sort_id)),
        }
    };

    // Helper: get array sort info
    let get_array_sort = |sort_id: u32| -> Option<(BvWidth, BvWidth)> {
        match sort_map.get(&sort_id) {
            Some(Btor2Sort::Array { index_width, element_width }) => {
                Some((*index_width, *element_width))
            }
            _ => None,
        }
    };

    // Process nodes in order (BTOR2 guarantees topological order)
    for node in &model.nodes {
        let op = node.op.as_str();

        match op {
            "input" => {
                if let Some((iw, ew)) = get_array_sort(node.sort_id) {
                    nid_to_array.insert(node.nid, ArrayState::Base {
                        nid: node.nid,
                        index_width: iw,
                        element_width: ew,
                    });
                } else {
                    let width = get_width(node.sort_id)?;
                    let bvc = bm.make_input(&mut tt, &ct, node.nid, width);
                    nid_to_bvc.insert(node.nid, bvc);
                    inputs.push((node.nid, width));
                }
            }
            "state" => {
                if let Some((iw, ew)) = get_array_sort(node.sort_id) {
                    // Array state
                    nid_to_array.insert(node.nid, ArrayState::Base {
                        nid: node.nid,
                        index_width: iw,
                        element_width: ew,
                    });
                    states.push((node.nid, None, None));
                } else {
                    let width = get_width(node.sort_id)?;
                    let bvc = bm.make_input(&mut tt, &ct, node.nid, width);
                    nid_to_bvc.insert(node.nid, bvc);
                    states.push((node.nid, None, None));
                }
            }
            "init" => {
                if node.args.len() >= 2 {
                    let state_nid = node.args[0].unsigned_abs() as u32;
                    let val_bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                    // Find the state and set its init
                    for s in &mut states {
                        if s.0 == state_nid {
                            s.1 = Some(val_bvc);
                        }
                    }
                }
            }
            "next" => {
                if node.args.len() >= 2 {
                    let state_nid = node.args[0].unsigned_abs() as u32;
                    let next_bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                    for s in &mut states {
                        if s.0 == state_nid {
                            s.2 = Some(next_bvc);
                        }
                    }
                }
            }
            "bad" => {
                if !node.args.is_empty() {
                    let bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                    bad_properties.push(bvc);
                }
            }
            "constraint" => {
                if !node.args.is_empty() {
                    let bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                    constraints.push(bvc);
                }
            }
            "output" => {
                // Output nodes are informational; just resolve the reference
                if !node.args.is_empty() {
                    let _bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0]);
                }
            }
            "const" | "constd" | "consth" => {
                let width = get_width(node.sort_id)?;
                let val = parse_const_value(op, &node.args, width)
                    .map_err(|e| format!("nid {}: {}", node.nid, e))?;
                let bvc = bm.make_const(&mut tt, &ct, val, width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            "one" => {
                let width = get_width(node.sort_id)?;
                let bvc = bm.make_const(&mut tt, &ct, 1, width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            "ones" => {
                let width = get_width(node.sort_id)?;
                let val = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
                let bvc = bm.make_const(&mut tt, &ct, val, width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            "zero" => {
                let width = get_width(node.sort_id)?;
                let bvc = bm.make_const(&mut tt, &ct, 0, width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            // Array WRITE: track the write chain
            "write" => {
                if node.args.len() >= 3 {
                    let array_nid = node.args[0].unsigned_abs() as u32;
                    let addr_bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                    let val_bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[2])?;

                    let base_state = nid_to_array.get(&array_nid)
                        .ok_or_else(|| format!("write to non-array nid {}", array_nid))?
                        .clone();

                    let (iw, ew) = match &base_state {
                        ArrayState::Base { index_width, element_width, .. } => (*index_width, *element_width),
                        ArrayState::Write { index_width, element_width, .. } => (*index_width, *element_width),
                    };

                    nid_to_array.insert(node.nid, ArrayState::Write {
                        base: Box::new(base_state),
                        addr_bvc,
                        val_bvc,
                        index_width: iw,
                        element_width: ew,
                    });
                }
            }
            // Array READ: expand to ITE chain (ROW expansion)
            "read" => {
                if node.args.len() >= 2 {
                    let array_nid = node.args[0].unsigned_abs() as u32;
                    let read_addr_bvc = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                    let width = get_width(node.sort_id)?;

                    if let Some(array_state) = nid_to_array.get(&array_nid).cloned() {
                        // Expand READ-over-WRITE chain to ITE chain
                        let result_bvc = expand_read(
                            &mut tt, &mut ct, &mut bm,
                            &array_state, read_addr_bvc, width,
                        );
                        nid_to_bvc.insert(node.nid, result_bvc);
                    } else {
                        // Read from non-array? Treat as unconstrained
                        let bvc = bm.make_input(&mut tt, &ct, node.nid, width);
                        nid_to_bvc.insert(node.nid, bvc);
                    }
                }
            }
            // Slice: special handling for bit indices
            "slice" => {
                let width = get_width(node.sort_id)?;
                let operand = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let upper = node.args[1] as u16;
                let lower = node.args[2] as u16;
                // Build slice term directly
                let arg_term = bm.get(operand).entries[0].term;
                let slice_term = tt.make_slice(arg_term, upper, lower);
                let constraint = bm.get(operand).entries[0].constraint;
                let bvc = bm.alloc(width, vec![BvcEntry {
                    term: slice_term,
                    constraint,
                }]);
                nid_to_bvc.insert(node.nid, bvc);
            }
            // Uext/Sext: special handling for extension width
            "uext" | "sext" => {
                let width = get_width(node.sort_id)?;
                let operand = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let op_kind = if op == "uext" { OpKind::Uext } else { OpKind::Sext };
                let arg_term = bm.get(operand).entries[0].term;
                let ext_term = tt.make_app(op_kind, vec![arg_term], width);
                let constraint = bm.get(operand).entries[0].constraint;
                let bvc = bm.alloc(width, vec![BvcEntry {
                    term: ext_term,
                    constraint,
                }]);
                nid_to_bvc.insert(node.nid, bvc);
            }
            // Derived operators: express as combinations of base ops
            "xnor" => {
                let width = get_width(node.sort_id)?;
                let a = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let b = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                let xor_bvc = bm.apply(&mut tt, &mut ct, OpKind::Xor, &[a, b], width);
                let bvc = bm.apply(&mut tt, &mut ct, OpKind::Not, &[xor_bvc], width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            "implies" => {
                // implies(a, b) = or(not(a), b)
                let width = get_width(node.sort_id)?;
                let a = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let b = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                let not_a = bm.apply(&mut tt, &mut ct, OpKind::Not, &[a], width);
                let bvc = bm.apply(&mut tt, &mut ct, OpKind::Or, &[not_a, b], width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            "nand" => {
                let width = get_width(node.sort_id)?;
                let a = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let b = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                let and_bvc = bm.apply(&mut tt, &mut ct, OpKind::And, &[a, b], width);
                let bvc = bm.apply(&mut tt, &mut ct, OpKind::Not, &[and_bvc], width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            "nor" => {
                let width = get_width(node.sort_id)?;
                let a = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let b = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                let or_bvc = bm.apply(&mut tt, &mut ct, OpKind::Or, &[a, b], width);
                let bvc = bm.apply(&mut tt, &mut ct, OpKind::Not, &[or_bvc], width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            // Reverse comparisons: swap arguments
            "ugt" | "sgt" | "ugte" | "sgte" => {
                let width = get_width(node.sort_id)?;
                let a = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[0])?;
                let b = resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, node.args[1])?;
                let mapped_op = match op {
                    "ugt" => OpKind::Ult,
                    "sgt" => OpKind::Slt,
                    "ugte" => OpKind::Ulte,
                    "sgte" => OpKind::Slte,
                    _ => unreachable!(),
                };
                // Swap: ugt(a,b) = ult(b,a)
                let bvc = bm.apply(&mut tt, &mut ct, mapped_op, &[b, a], width);
                nid_to_bvc.insert(node.nid, bvc);
            }
            _ => {
                // General operator
                if let Some(op_kind) = map_op(op) {
                    let width = get_width(node.sort_id)?;
                    let operands: Result<Vec<BvcId>, String> = node.args.iter()
                        .take(op_kind.arity())
                        .map(|&arg| resolve_ref(&nid_to_bvc, &mut bm, &mut tt, &mut ct, arg))
                        .collect();
                    let operands = operands?;
                    let bvc = bm.apply(&mut tt, &mut ct, op_kind, &operands, width);
                    nid_to_bvc.insert(node.nid, bvc);
                } else {
                    return Err(format!("unsupported BTOR2 operator: {}", op));
                }
            }
        }
    }

    Ok(LiftedModel {
        tt,
        ct,
        bm,
        nid_to_bvc,
        bad_properties,
        states,
        constraints,
        inputs,
    })
}

/// Expand a READ from an array state into an ITE chain.
///
/// READ(WRITE(a, w_addr, w_val), r_addr) →
///   ITE(EQ(r_addr, w_addr), w_val, READ(a, r_addr))
///
/// Nested writes produce nested ITE chains.
fn expand_read(
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    bm: &mut BvcManager,
    state: &ArrayState,
    read_addr_bvc: BvcId,
    element_width: BvWidth,
) -> BvcId {
    match state {
        ArrayState::Base { nid, index_width, .. } => {
            // Base array: READ is unconstrained — model as a fresh variable
            // (any array read from an unconstrained base is unconstrained)
            let read_addr_term = bm.get(read_addr_bvc).entries[0].term;
            let array_var = tt.make_var(*nid, *index_width);
            let read_term = tt.make_app(
                OpKind::Read,
                vec![array_var, read_addr_term],
                element_width,
            );
            bm.alloc(element_width, vec![BvcEntry {
                term: read_term,
                constraint: ct.true_id(),
            }])
        }
        ArrayState::Write { base, addr_bvc, val_bvc, index_width: _, element_width: ew } => {
            // ROW expansion:
            // ITE(EQ(r_addr, w_addr), w_val, READ(base, r_addr))
            let r_addr_term = bm.get(read_addr_bvc).entries[0].term;
            let w_addr_term = bm.get(*addr_bvc).entries[0].term;
            let w_val_term = bm.get(*val_bvc).entries[0].term;

            // Build EQ(r_addr, w_addr)
            let addr_width = tt.get(r_addr_term).width;
            let eq_term = tt.make_app(OpKind::Eq, vec![r_addr_term, w_addr_term], 1);

            // Recursively expand READ from the base array
            let base_read_bvc = expand_read(tt, ct, bm, base, read_addr_bvc, *ew);
            let base_read_term = bm.get(base_read_bvc).entries[0].term;

            // Build ITE(eq, w_val, base_read)
            let ite_term = tt.make_app(
                OpKind::Ite,
                vec![eq_term, w_val_term, base_read_term],
                element_width,
            );

            // Collect constraints from all involved BVCs
            let mut constraint = ct.true_id();
            let r_constraint = bm.get(read_addr_bvc).entries[0].constraint;
            let w_addr_constraint = bm.get(*addr_bvc).entries[0].constraint;
            let w_val_constraint = bm.get(*val_bvc).entries[0].constraint;
            let base_constraint = bm.get(base_read_bvc).entries[0].constraint;
            constraint = ct.make_and(constraint, r_constraint);
            constraint = ct.make_and(constraint, w_addr_constraint);
            constraint = ct.make_and(constraint, w_val_constraint);
            constraint = ct.make_and(constraint, base_constraint);
            let _ = addr_width;

            bm.alloc(element_width, vec![BvcEntry {
                term: ite_term,
                constraint,
            }])
        }
    }
}

/// Resolve a BTOR2 reference (possibly negated) to a BvcId
fn resolve_ref(
    nid_to_bvc: &HashMap<u32, BvcId>,
    bm: &mut BvcManager,
    tt: &mut TermTable,
    ct: &mut ConstraintTable,
    arg: i64,
) -> Result<BvcId, String> {
    let negated = arg < 0;
    let nid = arg.unsigned_abs() as u32;

    let bvc = *nid_to_bvc.get(&nid)
        .ok_or_else(|| format!("unresolved reference to nid {}", nid))?;

    if negated {
        // Negate: for width-1, this is Boolean NOT
        // For wider bitvectors, this is bitwise NOT
        let width = bm.get(bvc).width;
        Ok(bm.apply(tt, ct, OpKind::Not, &[bvc], width))
    } else {
        Ok(bvc)
    }
}

/// Parse a constant value from BTOR2
fn parse_const_value(kind: &str, args: &[i64], width: BvWidth) -> Result<u64, String> {
    match kind {
        "constd" => {
            // Decimal constant — first arg is the value
            if args.is_empty() {
                return Err("constd missing value".into());
            }
            let val = args[0] as u64;
            let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
            Ok(val & mask)
        }
        "const" => {
            // Binary constant — args contain the bits as a number
            // In BTOR2, "const" is followed by a binary string, which the parser
            // stores as a decimal value in args[0]
            if args.is_empty() {
                return Err("const missing value".into());
            }
            Ok(args[0] as u64)
        }
        "consth" => {
            // Hex constant
            if args.is_empty() {
                return Err("consth missing value".into());
            }
            Ok(args[0] as u64)
        }
        _ => Err(format!("unknown constant kind: {}", kind)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btor2::parse_btor2;

    #[test]
    fn test_lift_simple() {
        let input = "\
1 sort bitvec 2
2 sort bitvec 1
3 input 1 x
4 input 1 y
5 add 1 3 4
6 constd 1 3
7 eq 2 5 6
8 bad 7
";
        let model = parse_btor2(input).unwrap();
        let lifted = lift_btor2(&model).unwrap();

        // Should have BVCs for nodes 3, 4, 5, 6, 7
        assert!(lifted.nid_to_bvc.contains_key(&3));
        assert!(lifted.nid_to_bvc.contains_key(&4));
        assert!(lifted.nid_to_bvc.contains_key(&5));
        assert!(lifted.nid_to_bvc.contains_key(&6));
        assert!(lifted.nid_to_bvc.contains_key(&7));

        // One bad property
        assert_eq!(lifted.bad_properties.len(), 1);

        // Node 6 should be constant 3
        let c6 = lifted.nid_to_bvc[&6];
        assert_eq!(lifted.bm.get_const_value(&lifted.tt, c6), Some(3));
    }

    #[test]
    fn test_lift_with_state() {
        let input = "\
1 sort bitvec 8
2 state 1 cnt
3 constd 1 0
4 init 1 2 3
5 constd 1 1
6 add 1 2 5
7 next 1 2 6
8 constd 1 10
9 eq 1 2 8
10 sort bitvec 1
11 bad 9
";
        // Note: eq result should have sort bitvec 1, but let's see if it parses
        let model = parse_btor2(input).unwrap();
        let lifted = lift_btor2(&model).unwrap();

        assert_eq!(lifted.states.len(), 1);
        assert_eq!(lifted.states[0].0, 2); // state nid
        assert!(lifted.states[0].1.is_some()); // has init
        assert!(lifted.states[0].2.is_some()); // has next
        assert_eq!(lifted.bad_properties.len(), 1);
    }

    #[test]
    fn test_lift_negated_ref() {
        let input = "\
1 sort bitvec 1
2 input 1 a
3 not 1 2
4 bad 3
";
        let model = parse_btor2(input).unwrap();
        let lifted = lift_btor2(&model).unwrap();

        assert_eq!(lifted.bad_properties.len(), 1);
        // Node 3 is NOT at width 1 → structural → keeps actual NOT term
        let bvc3 = lifted.nid_to_bvc[&3];
        let term3 = lifted.bm.get(bvc3).entries[0].term;
        match &lifted.tt.get(term3).kind {
            bvdd::term::TermKind::App { op: bvdd::types::OpKind::Not, .. } => {} // correct
            other => panic!("expected Not app, got {:?}", other),
        }
    }

    #[test]
    fn test_lift_constants() {
        let input = "\
1 sort bitvec 8
2 zero 1
3 one 1
4 ones 1
";
        let model = parse_btor2(input).unwrap();
        let lifted = lift_btor2(&model).unwrap();

        assert_eq!(lifted.bm.get_const_value(&lifted.tt, lifted.nid_to_bvc[&2]), Some(0));
        assert_eq!(lifted.bm.get_const_value(&lifted.tt, lifted.nid_to_bvc[&3]), Some(1));
        assert_eq!(lifted.bm.get_const_value(&lifted.tt, lifted.nid_to_bvc[&4]), Some(255));
    }
}
