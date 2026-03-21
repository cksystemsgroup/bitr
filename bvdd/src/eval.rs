//! Compiled term evaluator
//!
//! Compiles a term DAG into a flat register-machine instruction sequence
//! for ~10x faster evaluation in generalized blast inner loops.
//! Each term maps to a register; instructions execute in topological order.

use crate::types::{TermId, OpKind, BvWidth};
use crate::term::{TermTable, TermKind};
use crate::valueset::ValueSet;

/// A single instruction in the compiled program
#[derive(Debug, Clone)]
pub struct Instruction {
    /// Destination register (same index as in the program)
    pub dst: u32,
    pub op: CompiledOp,
    pub width: BvWidth,
}

/// Compiled operation — all operands are register indices
#[derive(Debug, Clone)]
pub enum CompiledOp {
    /// Load a constant value
    Const(u64),
    /// Load from a variable slot
    LoadVar(u32),
    /// Unary op: op(src)
    Unary { op: OpKind, src: u32 },
    /// Binary op: op(lhs, rhs)
    Binary { op: OpKind, lhs: u32, rhs: u32, lhs_width: BvWidth },
    /// Ternary op: op(a, b, c)
    Ternary { op: OpKind, a: u32, b: u32, c: u32 },
    /// Slice: extract bits [upper:lower] from src
    Slice { src: u32, upper: u16, lower: u16 },
    /// Concat: hi << lo_width | lo
    Concat { hi: u32, lo: u32, lo_width: BvWidth },
    /// Sign extend from src_width to dst width
    Sext { src: u32, src_width: BvWidth },
}

/// Packed bytecode instruction — fixed 32 bytes for cache-friendly iteration.
/// Encodes opcode + up to 3 register operands + pre-computed mask.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct PackedInst {
    pub opcode: u8,     // OpCode discriminant
    pub dst: u8,        // destination register
    pub src1: u8,       // first source register (or var slot for LoadVar)
    pub src2: u8,       // second source register
    pub src3: u8,       // third source (ITE)
    pub _pad: [u8; 3],
    pub mask: u64,      // pre-computed width mask ((1<<width)-1 or u64::MAX)
    pub imm: u64,       // immediate value (constants, slice params, arg_width mask)
}

/// Opcode constants for packed instructions
#[allow(non_upper_case_globals)]
pub mod opcode {
    pub const Const: u8 = 0;
    pub const LoadVar: u8 = 1;
    pub const Add: u8 = 2;
    pub const Sub: u8 = 3;
    pub const Mul: u8 = 4;
    pub const And: u8 = 5;
    pub const Or: u8 = 6;
    pub const Xor: u8 = 7;
    pub const Not: u8 = 8;
    pub const Neg: u8 = 9;
    pub const Eq: u8 = 10;
    pub const Neq: u8 = 11;
    pub const Ult: u8 = 12;
    pub const Ulte: u8 = 13;
    pub const Sll: u8 = 14;
    pub const Srl: u8 = 15;
    pub const Sra: u8 = 16;
    pub const Slt: u8 = 17;
    pub const Slte: u8 = 18;
    pub const Ite: u8 = 19;
    pub const Slice: u8 = 20;
    pub const Concat: u8 = 21;
    pub const Sext: u8 = 22;
    pub const Uext: u8 = 23;
    pub const Udiv: u8 = 24;
    pub const Urem: u8 = 25;
    pub const Sdiv: u8 = 26;
    pub const Srem: u8 = 27;
    pub const Smod: u8 = 28;
    pub const Redand: u8 = 29;
    pub const Redor: u8 = 30;
    pub const Redxor: u8 = 31;
    pub const Uaddo: u8 = 32;
    pub const Umulo: u8 = 33;
    pub const Other: u8 = 255; // fallback
}

/// A compiled program ready for repeated evaluation
#[derive(Debug)]
pub struct CompiledProgram {
    pub instructions: Vec<Instruction>,
    /// Packed bytecode for fast evaluation
    packed: Vec<PackedInst>,
    /// Maps variable IDs to their slot index in the vars array
    pub var_slots: Vec<(u32, u32)>, // (var_id, slot_index)
    /// Number of variable slots
    pub num_vars: u32,
    /// Register index of the output (root term)
    pub output_reg: u32,
    /// Total number of registers
    pub num_regs: u32,
}

impl CompiledProgram {
    /// Compile a term into a flat instruction sequence
    pub fn compile(tt: &TermTable, root: TermId) -> Self {
        let mut compiler = Compiler {
            tt,
            term_to_reg: std::collections::HashMap::new(),
            var_to_slot: std::collections::HashMap::new(),
            instructions: Vec::new(),
            next_reg: 0,
            next_slot: 0,
        };
        let output_reg = compiler.compile_term(root);
        let mut var_slots: Vec<(u32, u32)> = compiler.var_to_slot.into_iter().collect();
        var_slots.sort_by_key(|&(vid, _)| vid);

        let packed = pack_instructions(&compiler.instructions);
        CompiledProgram {
            instructions: compiler.instructions,
            packed,
            var_slots,
            num_vars: compiler.next_slot,
            output_reg,
            num_regs: compiler.next_reg,
        }
    }

    /// Execute the compiled program with given variable values.
    /// `vars` must have length == num_vars, indexed by slot order.
    pub fn eval(&self, vars: &[u64]) -> u64 {
        // Use stack allocation for small register counts (common case)
        if self.num_regs <= 32 {
            let mut regs = [0u64; 32];
            self.eval_into(vars, &mut regs)
        } else {
            let mut regs = vec![0u64; self.num_regs as usize];
            self.eval_into(vars, &mut regs)
        }
    }

    /// Execute into a pre-allocated register buffer. Avoids allocation in hot loops.
    #[inline]
    pub fn eval_into(&self, vars: &[u64], regs: &mut [u64]) -> u64 {
        for inst in &self.instructions {
            let val = match &inst.op {
                CompiledOp::Const(v) => *v,
                CompiledOp::LoadVar(slot) => unsafe { *vars.get_unchecked(*slot as usize) },
                CompiledOp::Unary { op, src } => {
                    eval_unary(*op, unsafe { *regs.get_unchecked(*src as usize) }, inst.width)
                }
                CompiledOp::Binary { op, lhs, rhs, lhs_width } => {
                    eval_binary(
                        *op,
                        unsafe { *regs.get_unchecked(*lhs as usize) },
                        unsafe { *regs.get_unchecked(*rhs as usize) },
                        *lhs_width, inst.width,
                    )
                }
                CompiledOp::Ternary { op, a, b, c } => {
                    eval_ternary(
                        *op,
                        unsafe { *regs.get_unchecked(*a as usize) },
                        unsafe { *regs.get_unchecked(*b as usize) },
                        unsafe { *regs.get_unchecked(*c as usize) },
                        inst.width,
                    )
                }
                CompiledOp::Slice { src, upper, lower } => {
                    let v = unsafe { *regs.get_unchecked(*src as usize) };
                    mask((v >> lower) & mask(u64::MAX, upper - lower + 1), inst.width)
                }
                CompiledOp::Concat { hi, lo, lo_width } => {
                    let h = unsafe { *regs.get_unchecked(*hi as usize) };
                    let l = unsafe { *regs.get_unchecked(*lo as usize) };
                    mask((h << lo_width) | l, inst.width)
                }
                CompiledOp::Sext { src, src_width } => {
                    let v = unsafe { *regs.get_unchecked(*src as usize) };
                    mask(sign_extend(v, *src_width) as u64, inst.width)
                }
            };
            unsafe { *regs.get_unchecked_mut(inst.dst as usize) = val };
        }
        unsafe { *regs.get_unchecked(self.output_reg as usize) }
    }

    /// Fast evaluation using packed bytecode. Pre-computed masks eliminate
    /// per-instruction mask() calls. Fixed-size instructions improve cache locality.
    #[inline]
    pub fn eval_packed(&self, vars: &[u64], regs: &mut [u64]) -> u64 {
        for inst in &self.packed {
            let r1 = unsafe { *regs.get_unchecked(inst.src1 as usize) };
            let val = match inst.opcode {
                opcode::Const => inst.imm,
                opcode::LoadVar => unsafe { *vars.get_unchecked(inst.src1 as usize) },
                opcode::Add => r1.wrapping_add(unsafe { *regs.get_unchecked(inst.src2 as usize) }) & inst.mask,
                opcode::Sub => r1.wrapping_sub(unsafe { *regs.get_unchecked(inst.src2 as usize) }) & inst.mask,
                opcode::Mul => r1.wrapping_mul(unsafe { *regs.get_unchecked(inst.src2 as usize) }) & inst.mask,
                opcode::And => r1 & unsafe { *regs.get_unchecked(inst.src2 as usize) } & inst.mask,
                opcode::Or => (r1 | unsafe { *regs.get_unchecked(inst.src2 as usize) }) & inst.mask,
                opcode::Xor => (r1 ^ unsafe { *regs.get_unchecked(inst.src2 as usize) }) & inst.mask,
                opcode::Not => (!r1) & inst.mask,
                opcode::Neg => r1.wrapping_neg() & inst.mask,
                opcode::Eq => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; if r1 == r2 { 1 } else { 0 } }
                opcode::Neq => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; if r1 != r2 { 1 } else { 0 } }
                opcode::Ult => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; if r1 < r2 { 1 } else { 0 } }
                opcode::Ulte => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; if r1 <= r2 { 1 } else { 0 } }
                opcode::Sll => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; if r2 >= 64 { 0 } else { (r1 << r2) & inst.mask } }
                opcode::Srl => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; if r2 >= 64 { 0 } else { (r1 >> r2) & inst.mask } }
                opcode::Ite => {
                    let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) };
                    let r3 = unsafe { *regs.get_unchecked(inst.src3 as usize) };
                    (if r1 != 0 { r2 } else { r3 }) & inst.mask
                }
                opcode::Concat => {
                    let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) };
                    // imm stores lo_width
                    ((r1 << inst.imm) | r2) & inst.mask
                }
                opcode::Slice => {
                    // imm stores (upper << 16) | lower
                    let lower = inst.imm & 0xFFFF;
                    let slice_mask = inst.mask; // pre-computed (1<<(upper-lower+1))-1
                    (r1 >> lower) & slice_mask
                }
                opcode::Uext => r1 & inst.mask,
                opcode::Sext => {
                    // imm stores src_width
                    sign_extend(r1, inst.imm as BvWidth) as u64 & inst.mask
                }
                opcode::Slt => {
                    let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) };
                    if sign_extend(r1, inst.imm as BvWidth) < sign_extend(r2, inst.imm as BvWidth) { 1 } else { 0 }
                }
                opcode::Slte => {
                    let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) };
                    if sign_extend(r1, inst.imm as BvWidth) <= sign_extend(r2, inst.imm as BvWidth) { 1 } else { 0 }
                }
                opcode::Sra => {
                    let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) };
                    if r2 >= inst.imm { if sign_extend(r1, inst.imm as BvWidth) < 0 { inst.mask } else { 0 } }
                    else { (sign_extend(r1, inst.imm as BvWidth).wrapping_shr(r2 as u32) as u64) & inst.mask }
                }
                opcode::Redor => if r1 != 0 { 1 } else { 0 },
                opcode::Redand => if r1 == inst.imm { 1 } else { 0 }, // imm = full_mask
                opcode::Redxor => (r1.count_ones() % 2) as u64,
                opcode::Udiv => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; (if r2 == 0 { inst.mask } else { r1 / r2 }) & inst.mask }
                opcode::Urem => { let r2 = unsafe { *regs.get_unchecked(inst.src2 as usize) }; (if r2 == 0 { r1 } else { r1 % r2 }) & inst.mask }
                _ => {
                    // Fallback to the interpreted path for rare ops
                    self.eval_into(vars, regs);
                    return unsafe { *regs.get_unchecked(self.output_reg as usize) };
                }
            };
            unsafe { *regs.get_unchecked_mut(inst.dst as usize) = val };
        }
        unsafe { *regs.get_unchecked(self.output_reg as usize) }
    }

    /// Look up the slot index for a variable ID
    pub fn var_slot(&self, var_id: u32) -> Option<u32> {
        self.var_slots.iter().find(|&&(vid, _)| vid == var_id).map(|&(_, slot)| slot)
    }

    /// Parallel exhaustive search: find any variable assignment where the
    /// output value is in the target set. Splits the outermost variable
    /// into chunks across threads using rayon. Returns Some((slot_vals, output_val))
    /// on SAT, None on UNSAT.
    ///
    /// `slots`: (var_id, slot_idx, domain_size) for each variable to enumerate.
    pub fn parallel_search(
        &self,
        slots: &[(u32, u32, u64)],
        target: ValueSet,
        result_width: BvWidth,
    ) -> Option<(Vec<u64>, u64)> {
        use rayon::prelude::*;

        if slots.is_empty() {
            return None;
        }

        let (_, outer_slot, outer_domain) = slots[0];
        let inner_slots = &slots[1..];

        // Inner domain size per outer value
        let inner_domain: u64 = inner_slots.iter()
            .map(|&(_, _, d)| d)
            .product::<u64>()
            .max(1);

        // Chunk size: each chunk should do ~256K evaluations for good granularity
        let chunk_size = (256 * 1024u64 / inner_domain).max(1).min(outer_domain);
        let num_chunks = outer_domain.div_ceil(chunk_size);

        let found = (0..num_chunks).into_par_iter().find_map_any(|chunk_idx| {
            let start = chunk_idx * chunk_size;
            let end = (start + chunk_size).min(outer_domain);

            let mut slot_vals = vec![0u64; self.num_vars as usize];
            let mut regs = vec![0u64; self.num_regs as usize];

            for outer_val in start..end {
                slot_vals[outer_slot as usize] = outer_val;

                if inner_slots.is_empty() {
                    let val = self.eval_packed(&slot_vals, &mut regs);
                    let check = mask_for_check(val, result_width);
                    if target.contains(check) {
                        return Some((slot_vals, val));
                    }
                    continue;
                }

                // Initialize inner slots to 0
                for &(_, si, _) in inner_slots {
                    slot_vals[si as usize] = 0;
                }

                // Enumerate all inner combinations
                loop {
                    let val = self.eval_packed(&slot_vals, &mut regs);
                    let check = mask_for_check(val, result_width);
                    if target.contains(check) {
                        return Some((slot_vals, val));
                    }

                    let mut carry = true;
                    for &(_, si, domain) in inner_slots.iter().rev() {
                        if carry {
                            let next = slot_vals[si as usize] + 1;
                            if next < domain {
                                slot_vals[si as usize] = next;
                                carry = false;
                            } else {
                                slot_vals[si as usize] = 0;
                            }
                        }
                    }
                    if carry { break; }
                }
            }
            None
        });

        found
    }
}

struct Compiler<'a> {
    tt: &'a TermTable,
    term_to_reg: std::collections::HashMap<TermId, u32>,
    var_to_slot: std::collections::HashMap<u32, u32>,
    instructions: Vec<Instruction>,
    next_reg: u32,
    next_slot: u32,
}

impl<'a> Compiler<'a> {
    fn alloc_reg(&mut self) -> u32 {
        let r = self.next_reg;
        self.next_reg += 1;
        r
    }

    fn compile_term(&mut self, id: TermId) -> u32 {
        if let Some(&reg) = self.term_to_reg.get(&id) {
            return reg;
        }

        let term = self.tt.get(id).clone();
        let reg = self.alloc_reg();
        // Insert early to handle DAG sharing
        self.term_to_reg.insert(id, reg);

        let inst = match &term.kind {
            TermKind::Const(v) => Instruction {
                dst: reg,
                op: CompiledOp::Const(mask(*v, term.width)),
                width: term.width,
            },
            TermKind::Var(var_id) => {
                let slot = *self.var_to_slot.entry(*var_id).or_insert_with(|| {
                    let s = self.next_slot;
                    self.next_slot += 1;
                    s
                });
                Instruction {
                    dst: reg,
                    op: CompiledOp::LoadVar(slot),
                    width: term.width,
                }
            }
            TermKind::App { op, args, slice_upper, slice_lower } => {
                let op = *op;
                let su = *slice_upper;
                let sl = *slice_lower;
                // Compile children first (topological order)
                let child_regs: Vec<u32> = args.iter().map(|&a| self.compile_term(a)).collect();
                let arg_widths: Vec<BvWidth> = args.iter().map(|&a| self.tt.get(a).width).collect();

                match op {
                    OpKind::Slice => Instruction {
                        dst: reg,
                        op: CompiledOp::Slice { src: child_regs[0], upper: su, lower: sl },
                        width: term.width,
                    },
                    OpKind::Concat => Instruction {
                        dst: reg,
                        op: CompiledOp::Concat {
                            hi: child_regs[0],
                            lo: child_regs[1],
                            lo_width: arg_widths[1],
                        },
                        width: term.width,
                    },
                    OpKind::Sext => Instruction {
                        dst: reg,
                        op: CompiledOp::Sext { src: child_regs[0], src_width: arg_widths[0] },
                        width: term.width,
                    },
                    OpKind::Ite => Instruction {
                        dst: reg,
                        op: CompiledOp::Ternary {
                            op,
                            a: child_regs[0],
                            b: child_regs[1],
                            c: child_regs[2],
                        },
                        width: term.width,
                    },
                    _ if op.arity() == 1 => Instruction {
                        dst: reg,
                        op: CompiledOp::Unary { op, src: child_regs[0] },
                        width: term.width,
                    },
                    _ => Instruction {
                        dst: reg,
                        op: CompiledOp::Binary {
                            op,
                            lhs: child_regs[0],
                            rhs: child_regs[1],
                            lhs_width: arg_widths[0],
                        },
                        width: term.width,
                    },
                }
            }
        };
        self.instructions.push(inst);
        reg
    }
}

/// Mask a value to `width` bits
/// Mask a value for checking against ValueSet (8-bit domain)
/// Pack high-level instructions into flat bytecode
fn pack_instructions(instructions: &[Instruction]) -> Vec<PackedInst> {
    instructions.iter().map(|inst| {
        let width_mask = if inst.width >= 64 { u64::MAX } else { (1u64 << inst.width) - 1 };
        match &inst.op {
            CompiledOp::Const(v) => PackedInst {
                opcode: opcode::Const, dst: inst.dst as u8,
                src1: 0, src2: 0, src3: 0, _pad: [0; 3],
                mask: width_mask, imm: *v,
            },
            CompiledOp::LoadVar(slot) => PackedInst {
                opcode: opcode::LoadVar, dst: inst.dst as u8,
                src1: *slot as u8, src2: 0, src3: 0, _pad: [0; 3],
                mask: width_mask, imm: 0,
            },
            CompiledOp::Unary { op, src } => {
                let opc = match op {
                    OpKind::Not => opcode::Not, OpKind::Neg => opcode::Neg,
                    OpKind::Redand => opcode::Redand, OpKind::Redor => opcode::Redor,
                    OpKind::Redxor => opcode::Redxor, OpKind::Uext => opcode::Uext,
                    _ => opcode::Other,
                };
                PackedInst {
                    opcode: opc, dst: inst.dst as u8,
                    src1: *src as u8, src2: 0, src3: 0, _pad: [0; 3],
                    mask: width_mask, imm: width_mask, // imm=full mask for Redand
                }
            }
            CompiledOp::Binary { op, lhs, rhs, lhs_width } => {
                let opc = match op {
                    OpKind::Add => opcode::Add, OpKind::Sub => opcode::Sub,
                    OpKind::Mul => opcode::Mul, OpKind::And => opcode::And,
                    OpKind::Or => opcode::Or, OpKind::Xor => opcode::Xor,
                    OpKind::Eq => opcode::Eq, OpKind::Neq => opcode::Neq,
                    OpKind::Ult => opcode::Ult, OpKind::Ulte => opcode::Ulte,
                    OpKind::Slt => opcode::Slt, OpKind::Slte => opcode::Slte,
                    OpKind::Sll => opcode::Sll, OpKind::Srl => opcode::Srl,
                    OpKind::Sra => opcode::Sra,
                    OpKind::Udiv => opcode::Udiv, OpKind::Urem => opcode::Urem,
                    OpKind::Sdiv => opcode::Sdiv, OpKind::Srem => opcode::Srem,
                    OpKind::Smod => opcode::Smod,
                    OpKind::Uaddo => opcode::Uaddo, OpKind::Umulo => opcode::Umulo,
                    _ => opcode::Other,
                };
                PackedInst {
                    opcode: opc, dst: inst.dst as u8,
                    src1: *lhs as u8, src2: *rhs as u8, src3: 0, _pad: [0; 3],
                    mask: width_mask, imm: *lhs_width as u64,
                }
            }
            CompiledOp::Ternary { op: _, a, b, c } => PackedInst {
                opcode: opcode::Ite, dst: inst.dst as u8,
                src1: *a as u8, src2: *b as u8, src3: *c as u8, _pad: [0; 3],
                mask: width_mask, imm: 0,
            },
            CompiledOp::Slice { src, upper, lower } => {
                let slice_width = upper - lower + 1;
                let slice_mask = if slice_width >= 64 { u64::MAX } else { (1u64 << slice_width) - 1 };
                PackedInst {
                    opcode: opcode::Slice, dst: inst.dst as u8,
                    src1: *src as u8, src2: 0, src3: 0, _pad: [0; 3],
                    mask: slice_mask, imm: *lower as u64,
                }
            }
            CompiledOp::Concat { hi, lo, lo_width } => PackedInst {
                opcode: opcode::Concat, dst: inst.dst as u8,
                src1: *hi as u8, src2: *lo as u8, src3: 0, _pad: [0; 3],
                mask: width_mask, imm: *lo_width as u64,
            },
            CompiledOp::Sext { src, src_width } => PackedInst {
                opcode: opcode::Sext, dst: inst.dst as u8,
                src1: *src as u8, src2: 0, src3: 0, _pad: [0; 3],
                mask: width_mask, imm: *src_width as u64,
            },
        }
    }).collect()
}

#[inline(always)]
pub fn mask_for_check(val: u64, width: BvWidth) -> u8 {
    if width <= 8 {
        (val & ((1u64 << width) - 1)) as u8
    } else {
        (val & 0xFF) as u8
    }
}

#[inline(always)]
fn mask(val: u64, width: BvWidth) -> u64 {
    if width >= 64 { val } else { val & ((1u64 << width) - 1) }
}

/// Sign-extend a `width`-bit value to i64
#[inline(always)]
fn sign_extend(val: u64, width: BvWidth) -> i64 {
    if width == 0 { return 0; }
    if width >= 64 { return val as i64; }
    let sign_bit = 1u64 << (width - 1);
    if val & sign_bit != 0 {
        (val | !((1u64 << width) - 1)) as i64
    } else {
        val as i64
    }
}

#[inline]
fn eval_unary(op: OpKind, a: u64, width: BvWidth) -> u64 {
    let m = |v: u64| mask(v, width);
    match op {
        OpKind::Not => m(!a),
        OpKind::Neg => m(a.wrapping_neg()),
        OpKind::Redand => {
            let full = mask(u64::MAX, width);
            if a == full { 1 } else { 0 }
        }
        OpKind::Redor => if a != 0 { 1 } else { 0 },
        OpKind::Redxor => m((a.count_ones() % 2) as u64),
        OpKind::Uext => m(a),
        _ => 0,
    }
}

#[inline]
fn eval_binary(op: OpKind, a: u64, b: u64, arg_width: BvWidth, width: BvWidth) -> u64 {
    let m = |v: u64| mask(v, width);
    match op {
        OpKind::Eq => if a == b { 1 } else { 0 },
        OpKind::Neq => if a != b { 1 } else { 0 },
        OpKind::Ult => if a < b { 1 } else { 0 },
        OpKind::Ulte => if a <= b { 1 } else { 0 },
        OpKind::Slt => if sign_extend(a, arg_width) < sign_extend(b, arg_width) { 1 } else { 0 },
        OpKind::Slte => if sign_extend(a, arg_width) <= sign_extend(b, arg_width) { 1 } else { 0 },
        OpKind::Add => m(a.wrapping_add(b)),
        OpKind::Sub => m(a.wrapping_sub(b)),
        OpKind::Mul => m(a.wrapping_mul(b)),
        OpKind::Udiv => m(if b == 0 { mask(u64::MAX, width) } else { a / b }),
        OpKind::Urem => m(if b == 0 { a } else { a % b }),
        OpKind::Sdiv => {
            if b == 0 {
                let sa = sign_extend(a, arg_width);
                m(if sa >= 0 { mask(u64::MAX, width) } else { 1 })
            } else {
                m(sign_extend(a, arg_width).wrapping_div(sign_extend(b, arg_width)) as u64)
            }
        }
        OpKind::Srem => {
            if b == 0 { m(a) }
            else { m(sign_extend(a, arg_width).wrapping_rem(sign_extend(b, arg_width)) as u64) }
        }
        OpKind::Smod => {
            if b == 0 { m(a) }
            else {
                let sa = sign_extend(a, arg_width);
                let sb = sign_extend(b, arg_width);
                let rem = sa.wrapping_rem(sb);
                let result = if rem == 0 || (rem > 0) == (sb > 0) { rem } else { rem.wrapping_add(sb) };
                m(result as u64)
            }
        }
        OpKind::And => m(a & b),
        OpKind::Or => m(a | b),
        OpKind::Xor => m(a ^ b),
        OpKind::Sll => m(if b >= arg_width as u64 { 0 } else { a << b }),
        OpKind::Srl => m(if b >= arg_width as u64 { 0 } else { a >> b }),
        OpKind::Sra => {
            if b >= arg_width as u64 {
                if sign_extend(a, arg_width) < 0 { mask(u64::MAX, width) } else { 0 }
            } else {
                m(sign_extend(a, arg_width).wrapping_shr(b as u32) as u64)
            }
        }
        OpKind::Uaddo => {
            let sum = a.wrapping_add(b);
            if mask(sum, arg_width) != sum { 1 } else { 0 }
        }
        OpKind::Umulo => {
            let prod = (a as u128) * (b as u128);
            let max = if arg_width >= 64 { u64::MAX as u128 } else { (1u128 << arg_width) - 1 };
            if prod > max { 1 } else { 0 }
        }
        _ => 0,
    }
}

fn eval_ternary(op: OpKind, a: u64, b: u64, c: u64, width: BvWidth) -> u64 {
    match op {
        OpKind::Ite => mask(if a != 0 { b } else { c }, width),
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_const() {
        let mut tt = TermTable::new();
        let c = tt.make_const(42, 8);
        let prog = CompiledProgram::compile(&tt, c);
        assert_eq!(prog.eval(&[]), 42);
    }

    #[test]
    fn test_compile_var() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let prog = CompiledProgram::compile(&tt, x);
        assert_eq!(prog.num_vars, 1);
        assert_eq!(prog.eval(&[100]), 100);
    }

    #[test]
    fn test_compile_add() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let add = tt.make_app(OpKind::Add, vec![x, y], 8);
        let prog = CompiledProgram::compile(&tt, add);
        assert_eq!(prog.num_vars, 2);

        let sx = prog.var_slot(0).unwrap() as usize;
        let sy = prog.var_slot(1).unwrap() as usize;
        let mut vars = vec![0u64; 2];
        vars[sx] = 100;
        vars[sy] = 50;
        assert_eq!(prog.eval(&vars), 150);

        // Overflow
        vars[sx] = 200;
        vars[sy] = 100;
        assert_eq!(prog.eval(&vars), 44); // 300 & 0xFF
    }

    #[test]
    fn test_compile_nested() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let c5 = tt.make_const(5, 8);
        let add = tt.make_app(OpKind::Add, vec![x, c5], 8);
        let c100 = tt.make_const(100, 8);
        let mul = tt.make_app(OpKind::Mul, vec![add, c100], 8);

        let prog = CompiledProgram::compile(&tt, mul);
        let sx = prog.var_slot(0).unwrap() as usize;
        let mut vars = vec![0u64; 1];
        vars[sx] = 10;
        // (10+5)*100 = 1500 & 0xFF = 220
        assert_eq!(prog.eval(&vars), 220);
    }

    #[test]
    fn test_compile_dag_sharing() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let c1 = tt.make_const(1, 8);
        let add = tt.make_app(OpKind::Add, vec![x, c1], 8);
        // Use add twice: add * add
        let mul = tt.make_app(OpKind::Mul, vec![add, add], 8);

        let prog = CompiledProgram::compile(&tt, mul);
        let sx = prog.var_slot(0).unwrap() as usize;
        let mut vars = vec![0u64; 1];
        vars[sx] = 5;
        // (5+1)^2 = 36
        assert_eq!(prog.eval(&vars), 36);
        // DAG sharing means add is only compiled once
        // 3 instructions: x, const 1, add, mul — but x is LoadVar not a separate term
        assert!(prog.instructions.len() <= 4);
    }

    #[test]
    fn test_compile_comparisons() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let eq = tt.make_app(OpKind::Eq, vec![x, y], 1);
        let prog = CompiledProgram::compile(&tt, eq);

        let sx = prog.var_slot(0).unwrap() as usize;
        let sy = prog.var_slot(1).unwrap() as usize;
        let mut vars = vec![0u64; 2];
        vars[sx] = 42;
        vars[sy] = 42;
        assert_eq!(prog.eval(&vars), 1);
        vars[sy] = 43;
        assert_eq!(prog.eval(&vars), 0);
    }

    #[test]
    fn test_compile_ite() {
        let mut tt = TermTable::new();
        let c = tt.make_var(0, 1);
        let t = tt.make_const(10, 8);
        let e = tt.make_const(20, 8);
        let ite = tt.make_app(OpKind::Ite, vec![c, t, e], 8);

        let prog = CompiledProgram::compile(&tt, ite);
        let sc = prog.var_slot(0).unwrap() as usize;
        let mut vars = vec![0u64; 1];
        vars[sc] = 1;
        assert_eq!(prog.eval(&vars), 10);
        vars[sc] = 0;
        assert_eq!(prog.eval(&vars), 20);
    }

    #[test]
    fn test_compile_slice() {
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let sl = tt.make_slice(x, 5, 2);

        let prog = CompiledProgram::compile(&tt, sl);
        let sx = prog.var_slot(0).unwrap() as usize;
        let mut vars = vec![0u64; 1];
        vars[sx] = 0b11_1010_11; // bits[5:2] = 1010
        assert_eq!(prog.eval(&vars), 0b1010);
    }

    #[test]
    fn test_compile_concat() {
        let mut tt = TermTable::new();
        let hi = tt.make_var(0, 4);
        let lo = tt.make_var(1, 4);
        let cat = tt.make_app(OpKind::Concat, vec![hi, lo], 8);

        let prog = CompiledProgram::compile(&tt, cat);
        let shi = prog.var_slot(0).unwrap() as usize;
        let slo = prog.var_slot(1).unwrap() as usize;
        let mut vars = vec![0u64; 2];
        vars[shi] = 0xA;
        vars[slo] = 0x5;
        assert_eq!(prog.eval(&vars), 0xA5);
    }

    #[test]
    fn test_compiled_vs_recursive_eval() {
        // Verify compiled evaluator matches recursive evaluator
        use std::collections::HashMap;
        let mut tt = TermTable::new();
        let x = tt.make_var(0, 8);
        let y = tt.make_var(1, 8);
        let add = tt.make_app(OpKind::Add, vec![x, y], 8);
        let c3 = tt.make_const(3, 8);
        let mul = tt.make_app(OpKind::Mul, vec![add, c3], 8);
        let z = tt.make_var(2, 8);
        let sub = tt.make_app(OpKind::Sub, vec![mul, z], 8);

        let prog = CompiledProgram::compile(&tt, sub);
        let sx = prog.var_slot(0).unwrap() as usize;
        let sy = prog.var_slot(1).unwrap() as usize;
        let sz = prog.var_slot(2).unwrap() as usize;

        for xv in (0..=255).step_by(17) {
            for yv in (0..=255).step_by(23) {
                for zv in (0..=255).step_by(31) {
                    let mut vars = vec![0u64; 3];
                    vars[sx] = xv;
                    vars[sy] = yv;
                    vars[sz] = zv;
                    let compiled_result = prog.eval(&vars);

                    let mut assign = HashMap::new();
                    assign.insert(0u32, xv);
                    assign.insert(1u32, yv);
                    assign.insert(2u32, zv);
                    let recursive_result = tt.eval(sub, &assign).unwrap();

                    assert_eq!(compiled_result, recursive_result,
                        "mismatch at x={}, y={}, z={}", xv, yv, zv);
                }
            }
        }
    }
}
