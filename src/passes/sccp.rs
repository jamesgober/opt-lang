//! Sparse conditional constant propagation (Wegman–Zadeck).
//!
//! An optimistic analysis over a three-level lattice (unknown, constant,
//! varying) that propagates constants through instructions, block parameters,
//! and the edges that can actually be taken, so a branch on a constant prunes the
//! code behind it and a block parameter that only ever receives one constant
//! becomes that constant. `switch` and `check` edges are evaluated exactly:
//!
//! - a `check` whose operands are all constant is folded with the operation's
//!   policy (`specs/OPS.md`): a value goes to the normal edge, an `error`
//!   failure goes to the error edge with its OPS code, and a `trap` failure
//!   becomes a `trap` terminator. An operation that would raise is never folded
//!   into a value.
//! - a `check` whose operation provably cannot fail (adding or subtracting a
//!   constant zero, multiplying by a constant zero or one, a shift by a
//!   constant in range, a division by a constant other than `0` and `-1`, a
//!   widening `int_cast`) becomes the plain operation and a jump.
//! - a `check`'s error code is known on its error edge when the policy allows
//!   only one error kind.
//!
//! Values of type `ptr` and `ref`, and values derived from a `ref`, are never
//! made constant (addresses are not compile-time values, and a constant `ref`
//! would be live across safepoints).
//!
//! Cost: linear in instructions, values, and edges (each value is lowered at most
//! twice and each edge becomes executable once); terminators with many edges are
//! re-evaluated only when their own operands change. Unreachable code is left for
//! CFG simplification to delete.

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{
    BinaryOp, Block, BlockArg, BlockCall, BuildError, Builder, ConvOp, DivZero, Function, Inst,
    InstData, Overflow, Position, Shift, Terminator, Type, Value, ValueDef,
};

use crate::Budget;
use crate::analysis::{Cfg, edge, is_tracked, tracked_values};
use crate::edit::{block_start, constant, own_operands, replace_terminator, use_counts};
use crate::fold::{self, Fold};

const TOP: u8 = 0;
const CONST: u8 = 1;
const BOTTOM: u8 = 2;

/// A lattice cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Cell {
    state: u8,
    bits: u64,
}

const TOP_CELL: Cell = Cell {
    state: TOP,
    bits: 0,
};
const BOTTOM_CELL: Cell = Cell {
    state: BOTTOM,
    bits: 0,
};

fn konst(bits: u64) -> Cell {
    Cell { state: CONST, bits }
}

/// The meet of two cells.
fn meet(a: Cell, b: Cell) -> Cell {
    match (a.state, b.state) {
        (TOP, _) => b,
        (_, TOP) => a,
        (CONST, CONST) if a.bits == b.bits => a,
        _ => BOTTOM_CELL,
    }
}

/// A use of a value, for the sparse worklist.
#[derive(Clone, Copy)]
enum Use {
    Inst(u32),
    Term(u32),
    Arg { block: u32, edge: u32, arg: u32 },
}

struct Sccp<'f> {
    func: &'f Function,
    cfg: Cfg,
    tracked: Option<Vec<bool>>,
    cells: Vec<Cell>,
    /// Per block: the `check` result and error-code cells.
    check_res: Vec<Cell>,
    check_err: Vec<Cell>,
    exec_block: Vec<bool>,
    /// Executable flag per edge, indexed by `edge_base[block] + idx`.
    edge_base: Vec<u32>,
    exec_edge: Vec<bool>,
    use_start: Vec<u32>,
    uses: Vec<Use>,
    edge_work: Vec<(u32, u32)>,
    block_work: Vec<u32>,
    value_work: Vec<u32>,
}

impl<'f> Sccp<'f> {
    fn new(func: &'f Function) -> Sccp<'f> {
        let cfg = Cfg::new(func);
        let tracked = tracked_values(func, &cfg);
        let nb = func.block_count();
        let mut edge_base = vec![0u32; nb + 1];
        for b in 0..nb {
            edge_base[b + 1] = edge_base[b] + cfg.succs(b).len() as u32;
        }
        let total_edges = edge_base[nb] as usize;
        let mut s = Sccp {
            func,
            cfg,
            tracked,
            cells: vec![TOP_CELL; func.value_count()],
            check_res: vec![TOP_CELL; nb],
            check_err: vec![TOP_CELL; nb],
            exec_block: vec![false; nb],
            edge_base,
            exec_edge: vec![false; total_edges],
            use_start: Vec::new(),
            uses: Vec::new(),
            edge_work: Vec::new(),
            block_work: Vec::new(),
            value_work: Vec::new(),
        };
        s.build_uses();
        s
    }

    /// Builds the use lists of every value over the reachable blocks.
    fn build_uses(&mut self) {
        let func = self.func;
        let nv = func.value_count();
        let mut pairs: Vec<(u32, Use)> = Vec::new();
        for &b in &self.cfg.rpo {
            let block = Block::from_u32(b);
            for inst in func.insts(block) {
                if let Some(data) = func.inst(inst) {
                    data.for_each_operand(|v| {
                        pairs.push((func.resolve(v).as_u32(), Use::Inst(inst.as_u32())));
                    });
                }
            }
            if let Some(term) = func.terminator(block) {
                own_operands(term, |v| {
                    pairs.push((func.resolve(v).as_u32(), Use::Term(b)))
                });
                for (k, dest) in term.successors().enumerate() {
                    for (a, arg) in dest.args.iter().enumerate() {
                        if let BlockArg::Value(v) = arg {
                            pairs.push((
                                func.resolve(*v).as_u32(),
                                Use::Arg {
                                    block: b,
                                    edge: k as u32,
                                    arg: a as u32,
                                },
                            ));
                        }
                    }
                }
            }
        }
        // Counting sort by value.
        let mut start = vec![0u32; nv + 1];
        for &(v, _) in &pairs {
            if let Some(s) = start.get_mut(v as usize + 1) {
                *s += 1;
            }
        }
        for i in 0..nv {
            start[i + 1] += start[i];
        }
        let mut fill = start.clone();
        let mut uses = vec![Use::Term(0); pairs.len()];
        for &(v, u) in &pairs {
            if let Some(slot) = fill.get_mut(v as usize) {
                if let Some(dst) = uses.get_mut(*slot as usize) {
                    *dst = u;
                }
                *slot += 1;
            }
        }
        self.use_start = start;
        self.uses = uses;
    }

    fn cell(&self, v: Value) -> Cell {
        self.cells
            .get(self.func.resolve(v).index())
            .copied()
            .unwrap_or(BOTTOM_CELL)
    }

    /// Lowers `v` to (its meet with) `c`; queues its users if it changed.
    fn lower(&mut self, v: Value, c: Cell) {
        let i = v.index();
        let Some(old) = self.cells.get(i).copied() else {
            return;
        };
        let new = meet(old, c);
        if new != old {
            self.cells[i] = new;
            self.value_work.push(v.as_u32());
        }
    }

    /// Whether a value of this type may hold a constant in the lattice.
    fn constable(&self, v: Value) -> bool {
        !matches!(self.func.value_type(v), Some(Type::Ptr | Type::Ref) | None)
            && !is_tracked(&self.tracked, v)
    }

    fn edge_index(&self, block: u32, idx: u32) -> usize {
        self.edge_base.get(block as usize).copied().unwrap_or(0) as usize + idx as usize
    }

    fn analyze(&mut self, budget: &mut Budget) -> bool {
        let entry = self.func.entry();
        for &p in self.func.block_params(entry) {
            self.lower(p, BOTTOM_CELL);
        }
        if let Some(e) = self.exec_block.get_mut(entry.index()) {
            *e = true;
        }
        self.block_work.push(entry.as_u32());
        // Every step below is paid for up front by the caller's linear charge;
        // this counter only guards against a defect turning into a long loop.
        let mut steps: u64 = 0;
        let limit = 8 * (self.uses.len() + self.exec_edge.len() + self.cells.len() + 16) as u64;
        loop {
            steps += 1;
            if steps > limit && !budget.charge(1) {
                return false;
            }
            if let Some((from, idx)) = self.edge_work.pop() {
                self.take_edge(from, idx);
            } else if let Some(b) = self.block_work.pop() {
                let block = Block::from_u32(b);
                let insts: Vec<Inst> = self.func.insts(block).collect();
                for inst in insts {
                    self.eval_inst(inst);
                }
                self.eval_term(b);
            } else if let Some(v) = self.value_work.pop() {
                let lo = self.use_start.get(v as usize).copied().unwrap_or(0) as usize;
                let hi = self.use_start.get(v as usize + 1).copied().unwrap_or(0) as usize;
                for k in lo..hi {
                    match self.uses[k] {
                        Use::Inst(i) => {
                            let inst = Inst::from_u32(i);
                            if self
                                .func
                                .inst_block(inst)
                                .is_some_and(|b| self.exec_block[b.index()])
                            {
                                self.eval_inst(inst);
                            }
                        }
                        Use::Term(b) => {
                            if self.exec_block[b as usize] {
                                self.eval_term(b);
                            }
                        }
                        Use::Arg { block, edge, arg } => {
                            let ei = self.edge_index(block, edge);
                            if self.exec_edge.get(ei).copied().unwrap_or(false) {
                                self.meet_edge_arg(block, edge, arg);
                            }
                        }
                    }
                }
            } else {
                return true;
            }
        }
    }

    /// Marks an edge executable, passing its arguments to the target's
    /// parameters, and the target block executable.
    fn take_edge(&mut self, from: u32, idx: u32) {
        let ei = self.edge_index(from, idx);
        match self.exec_edge.get_mut(ei) {
            Some(e) if !*e => *e = true,
            _ => return,
        }
        self.meet_edge_args(from, idx, false);
        let Some(&to) = self.cfg.succs(from as usize).get(idx as usize) else {
            return;
        };
        if let Some(x) = self.exec_block.get_mut(to as usize) {
            if !*x {
                *x = true;
                self.block_work.push(to);
            }
        }
    }

    /// Meets one SSA-value argument of an executable edge into its parameter.
    fn meet_edge_arg(&mut self, from: u32, idx: u32, arg: u32) {
        let func = self.func;
        let Some(term) = func.terminator(Block::from_u32(from)) else {
            return;
        };
        let Some(dest) = edge(term, idx as usize) else {
            return;
        };
        let (Some(BlockArg::Value(v)), Some(&p)) = (
            dest.args.get(arg as usize),
            func.block_params(dest.block).get(arg as usize),
        ) else {
            return;
        };
        let c = if self.constable(p) {
            self.cell(*v)
        } else {
            BOTTOM_CELL
        };
        self.lower(p, c);
    }

    /// Meets the arguments of an executable edge into the target's parameters
    /// (only the `check`-produced ones when `produced_only`).
    fn meet_edge_args(&mut self, from: u32, idx: u32, produced_only: bool) {
        let func = self.func;
        let Some(term) = func.terminator(Block::from_u32(from)) else {
            return;
        };
        let Some(dest) = edge(term, idx as usize) else {
            return;
        };
        let params = func.block_params(dest.block);
        for (arg, &p) in dest.args.iter().zip(params) {
            let c = match arg {
                BlockArg::Value(v) => {
                    if produced_only {
                        continue;
                    }
                    self.cell(*v)
                }
                BlockArg::Result(_) => match term {
                    Terminator::Check { .. } => self.check_res[from as usize],
                    _ => BOTTOM_CELL,
                },
                BlockArg::ErrorCode => self.check_err[from as usize],
                _ => BOTTOM_CELL,
            };
            let c = if self.constable(p) { c } else { BOTTOM_CELL };
            self.lower(p, c);
        }
    }

    fn eval_inst(&mut self, inst: Inst) {
        let func = self.func;
        let results = func.results(inst);
        let Some(r) = results.first() else {
            return;
        };
        if results.len() != 1 || !self.constable(r) {
            for v in results {
                self.lower(v, BOTTOM_CELL);
            }
            return;
        }
        let Some(data) = func.inst(inst) else {
            return;
        };
        let c = self.eval_data(data);
        self.lower(r, c);
    }

    /// The cell an operation computes from its operands' cells.
    fn eval_data(&self, data: &InstData) -> Cell {
        let func = self.func;
        let ty = |v: Value| func.value_type(v).unwrap_or(Type::Ptr);
        let fold_cell = |f: Fold| match f {
            Fold::Value(bits) => konst(bits),
            _ => BOTTOM_CELL,
        };
        match data {
            InstData::Const { ty, bits } => {
                if matches!(ty, Type::Ptr | Type::Ref) {
                    BOTTOM_CELL
                } else {
                    konst(*bits)
                }
            }
            InstData::Unary { op, policy, arg } => match self.cell(*arg) {
                Cell { state: CONST, bits } => fold_cell(fold::unary(*op, *policy, ty(*arg), bits)),
                c => c,
            },
            InstData::Binary { op, policy, args } => {
                match (self.cell(args[0]), self.cell(args[1])) {
                    (
                        Cell {
                            state: CONST,
                            bits: a,
                        },
                        Cell {
                            state: CONST,
                            bits: b,
                        },
                    ) => fold_cell(fold::binary(*op, *policy, ty(args[0]), a, b)),
                    (x, y) if x.state == BOTTOM || y.state == BOTTOM => BOTTOM_CELL,
                    _ => TOP_CELL,
                }
            }
            InstData::Compare { op, args } => match (self.cell(args[0]), self.cell(args[1])) {
                (
                    Cell {
                        state: CONST,
                        bits: a,
                    },
                    Cell {
                        state: CONST,
                        bits: b,
                    },
                ) => match fold::compare(*op, ty(args[0]), a, b) {
                    Some(r) => konst(u64::from(r)),
                    None => BOTTOM_CELL,
                },
                (x, y) if x.state == BOTTOM || y.state == BOTTOM => BOTTOM_CELL,
                _ => TOP_CELL,
            },
            InstData::Convert {
                op,
                policy,
                to,
                arg,
            } => match self.cell(*arg) {
                Cell { state: CONST, bits } => {
                    fold_cell(fold::convert(*op, *policy, ty(*arg), *to, bits))
                }
                c => c,
            },
            InstData::Select { cond, args } => match self.cell(*cond) {
                Cell { state: CONST, bits } => {
                    self.cell(if bits & 1 == 1 { args[0] } else { args[1] })
                }
                Cell { state: TOP, .. } => TOP_CELL,
                _ => meet(self.cell(args[0]), self.cell(args[1])),
            },
            _ => BOTTOM_CELL,
        }
    }

    /// The `check` result, error-code cell, and feasible edges (normal, error).
    fn eval_check(&self, op: &InstData) -> (Cell, Cell, bool, bool) {
        let mut any_top = false;
        let mut all_const = true;
        let mut bits: [u64; 2] = [0; 2];
        let mut n = 0;
        op.for_each_operand(|v| {
            let c = self.cell(v);
            if c.state == TOP {
                any_top = true;
            }
            if c.state != CONST {
                all_const = false;
            }
            if let Some(slot) = bits.get_mut(n) {
                *slot = c.bits;
            }
            n += 1;
        });
        let kinds = fold::error_kinds(op);
        let single_err = if kinds.count_ones() == 1 {
            konst(u64::from(kinds.trailing_zeros()))
        } else {
            BOTTOM_CELL
        };
        if any_top {
            return (TOP_CELL, TOP_CELL, false, false);
        }
        if all_const {
            match fold_check(self.func, op, bits) {
                Fold::Value(v) => return (konst(v), TOP_CELL, true, false),
                Fold::Error(e) => return (TOP_CELL, konst(u64::from(e.code())), false, true),
                Fold::Trap(_) => return (TOP_CELL, TOP_CELL, false, false),
                Fold::Unknown => {}
            }
        }
        if !self.may_fail(op) {
            return (BOTTOM_CELL, TOP_CELL, true, false);
        }
        (BOTTOM_CELL, single_err, true, true)
    }

    /// Whether a `check`'s operation can take its error edge, given what is
    /// known about its operands (the partial analysis in the module docs).
    fn may_fail(&self, op: &InstData) -> bool {
        let func = self.func;
        match op {
            InstData::Binary { op, policy, args } => {
                let ty = func.value_type(args[0]).unwrap_or(Type::Ptr);
                if !ty.is_int() {
                    return true;
                }
                let lhs = self.cell(args[0]);
                let known = |c: Cell, v: i128| c.state == CONST && fold::sval(ty, c.bits) == v;
                // Adding zero, or multiplying by zero or one, cannot overflow.
                match op {
                    BinaryOp::Add if known(lhs, 0) => return false,
                    BinaryOp::Mul if known(lhs, 0) || known(lhs, 1) => return false,
                    _ => {}
                }
                let rhs = self.cell(args[1]);
                if rhs.state != CONST {
                    return true;
                }
                let y = fold::sval(ty, rhs.bits);
                let w = i128::from(ty.int_bits().unwrap_or(64));
                match op {
                    BinaryOp::Add | BinaryOp::Sub => y != 0,
                    BinaryOp::Mul => y != 0 && y != 1,
                    BinaryOp::Shl | BinaryOp::Shr => !(0..w).contains(&y),
                    BinaryOp::Div | BinaryOp::FloorDiv => {
                        let overflow_possible = policy.overflow == Some(Overflow::Error)
                            && ty.is_signed_int()
                            && y == -1;
                        let zero_possible = policy.div_zero == Some(DivZero::Error) && y == 0;
                        overflow_possible || zero_possible
                    }
                    BinaryOp::Rem | BinaryOp::FloorMod => {
                        policy.div_zero == Some(DivZero::Error) && y == 0
                    }
                    _ => true,
                }
            }
            InstData::Convert {
                op: ConvOp::IntCast,
                to,
                arg,
                ..
            } => {
                let from = func.value_type(*arg).unwrap_or(Type::Ptr);
                !widens(from, *to)
            }
            _ => true,
        }
    }

    fn eval_term(&mut self, b: u32) {
        let func = self.func;
        let Some(term) = func.terminator(Block::from_u32(b)) else {
            return;
        };
        let n_edges = self.cfg.succs(b as usize).len() as u32;
        match term {
            Terminator::Jump(_) => self.edge_work.push((b, 0)),
            Terminator::Branch { cond, .. } => match self.cell(*cond) {
                Cell { state: CONST, bits } => {
                    self.edge_work.push((b, if bits & 1 == 1 { 0 } else { 1 }));
                }
                Cell { state: TOP, .. } => {}
                _ => {
                    self.edge_work.push((b, 0));
                    self.edge_work.push((b, 1));
                }
            },
            Terminator::Switch { value, cases, .. } => match self.cell(*value) {
                Cell { state: CONST, bits } => {
                    let k = cases
                        .iter()
                        .position(|c| c.value == bits)
                        .unwrap_or(cases.len());
                    self.edge_work.push((b, k as u32));
                }
                Cell { state: TOP, .. } => {}
                _ => {
                    for k in 0..n_edges {
                        self.edge_work.push((b, k));
                    }
                }
            },
            Terminator::Invoke { .. } => {
                self.edge_work.push((b, 0));
                self.edge_work.push((b, 1));
            }
            Terminator::Check { op, .. } => {
                let (res, err, normal, error) = self.eval_check(op);
                let old = (self.check_res[b as usize], self.check_err[b as usize]);
                let new = (meet(old.0, res), meet(old.1, err));
                self.check_res[b as usize] = new.0;
                self.check_err[b as usize] = new.1;
                if new != old {
                    // Re-pass the produced arguments along the edges already taken.
                    for k in 0..n_edges {
                        let ei = self.edge_index(b, k);
                        if self.exec_edge.get(ei).copied().unwrap_or(false) {
                            self.meet_edge_args(b, k, true);
                        }
                    }
                }
                if normal {
                    self.edge_work.push((b, 0));
                }
                if error {
                    self.edge_work.push((b, 1));
                }
            }
            _ => {}
        }
    }
}

/// Whether every value of integer type `from` fits in integer type `to`.
fn widens(from: Type, to: Type) -> bool {
    let (Some(fw), Some(tw)) = (from.int_bits(), to.int_bits()) else {
        return false;
    };
    if from.is_signed_int() == to.is_signed_int() {
        tw >= fw
    } else {
        // unsigned -> signed needs a strictly wider target; signed -> unsigned
        // never fits (negative values).
        !from.is_signed_int() && tw > fw
    }
}

/// Folds a `check`'s operation on constant operand bits.
fn fold_check(func: &Function, op: &InstData, bits: [u64; 2]) -> Fold {
    let ty = |v: Value| func.value_type(v).unwrap_or(Type::Ptr);
    match op {
        InstData::Unary { op, policy, arg } => fold::unary(*op, *policy, ty(*arg), bits[0]),
        InstData::Binary { op, policy, args } => {
            fold::binary(*op, *policy, ty(args[0]), bits[0], bits[1])
        }
        InstData::Convert {
            op,
            policy,
            to,
            arg,
        } => fold::convert(*op, *policy, ty(*arg), *to, bits[0]),
        _ => Fold::Unknown,
    }
}

/// The result type of a `check`'s operation.
fn check_result_type(func: &Function, op: &InstData) -> Option<Type> {
    match op {
        InstData::Unary { arg, .. } => func.value_type(*arg),
        InstData::Binary { args, .. } => func.value_type(args[0]),
        InstData::Convert { to, .. } => Some(*to),
        _ => None,
    }
}

/// The plain (non-raising) form of a `check`'s operation whose error cannot
/// happen: the same result on every input the analysis allows.
fn relaxed(op: &InstData) -> InstData {
    let mut op = op.clone();
    if let InstData::Unary { policy, .. }
    | InstData::Binary { policy, .. }
    | InstData::Convert { policy, .. } = &mut op
    {
        if policy.overflow == Some(Overflow::Error) {
            policy.overflow = Some(Overflow::Wrap);
        }
        if policy.div_zero == Some(DivZero::Error) {
            policy.div_zero = Some(DivZero::Trap);
        }
        if policy.shift == Some(Shift::Error) {
            policy.shift = Some(Shift::Mask);
        }
    }
    op
}

/// `dest` with every `res0` / `err` argument replaced by `v`.
fn substitute(dest: &BlockCall, v: Value) -> BlockCall {
    let mut d = dest.clone();
    for a in &mut d.args {
        if matches!(a, BlockArg::Result(_) | BlockArg::ErrorCode) {
            *a = BlockArg::Value(v);
        }
    }
    d
}

/// Runs SCCP; returns whether anything changed.
pub(crate) fn run(b: &mut Builder<'_>, budget: &mut Budget) -> Result<bool, BuildError> {
    let func = b.func();
    let cost = 6 * (func.inst_count() + func.value_count() + func.block_count() + 1) as u64;
    if !budget.charge(cost) {
        return Ok(false);
    }
    let mut s = Sccp::new(func);
    if !s.analyze(budget) {
        return Ok(false);
    }
    // Safety net: no value defined in executable code may be left unknown.
    for (i, c) in s.cells.iter().enumerate() {
        if c.state != TOP {
            continue;
        }
        let v = Value::from_u32(i as u32);
        let block = match func.value_def(v) {
            Some(ValueDef::Param { block, .. }) => Some(block),
            Some(ValueDef::Result { inst, .. }) => func.inst_block(inst),
            _ => None,
        };
        if block.is_some_and(|bl| s.exec_block.get(bl.index()).copied().unwrap_or(false)) {
            return Ok(false);
        }
    }
    let uses = use_counts(func);
    let entry = func.entry();

    // Plan every rewrite while reading, then apply.
    enum Plan {
        /// Replace a parameter with a constant.
        Param(Value, Type, u64),
        /// Replace an instruction's result with a constant and remove it.
        Inst(Inst, Value, Type, u64),
        /// Replace a `select` with the chosen operand and remove it.
        Select(Inst, Value, Value),
        /// Replace a terminator.
        Term(Block, Term),
    }
    enum Term {
        Jump(BlockCall),
        /// Jump along `dest` with the produced argument a new constant.
        JumpWithConst(BlockCall, Type, u64),
        /// Jump along `dest` with the produced argument the relaxed operation.
        JumpWithOp(BlockCall, InstData),
        Trap(u32),
    }
    let mut plans: Vec<Plan> = Vec::new();
    for &bl in &s.cfg.rpo {
        let block = Block::from_u32(bl);
        if !s.exec_block[bl as usize] {
            continue;
        }
        if block != entry {
            for &p in func.block_params(block) {
                let c = s.cells[p.index()];
                if c.state == CONST && uses[p.index()] > 0 && s.constable(p) {
                    if let Some(ty) = func.value_type(p) {
                        plans.push(Plan::Param(p, ty, c.bits));
                    }
                }
            }
        }
        for inst in func.insts(block) {
            let Some(data) = func.inst(inst) else {
                continue;
            };
            if matches!(data, InstData::Const { .. }) {
                continue;
            }
            let results = func.results(inst);
            let Some(r) = results.first() else {
                continue;
            };
            if results.len() != 1 || uses[r.index()] == 0 || func.resolve(r) != r {
                continue;
            }
            let c = s.cells[r.index()];
            if c.state == CONST && s.constable(r) {
                if let Some(ty) = func.value_type(r) {
                    plans.push(Plan::Inst(inst, r, ty, c.bits));
                }
            } else if let InstData::Select { cond, args } = data {
                let cc = s.cell(*cond);
                if cc.state == CONST {
                    let chosen = func.resolve(if cc.bits & 1 == 1 { args[0] } else { args[1] });
                    if chosen != r {
                        plans.push(Plan::Select(inst, r, chosen));
                    }
                }
            }
        }
        let Some(term) = func.terminator(block) else {
            continue;
        };
        match term {
            Terminator::Branch {
                cond,
                then_dest,
                else_dest,
            } => {
                let c = s.cell(*cond);
                if c.state == CONST {
                    let dest = if c.bits & 1 == 1 {
                        then_dest
                    } else {
                        else_dest
                    };
                    plans.push(Plan::Term(block, Term::Jump(dest.clone())));
                }
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                let c = s.cell(*value);
                if c.state == CONST {
                    let dest = cases
                        .iter()
                        .find(|k| k.value == c.bits)
                        .map_or(default, |k| &k.dest);
                    plans.push(Plan::Term(block, Term::Jump(dest.clone())));
                }
            }
            Terminator::Check { op, normal, error } => {
                let (res, err, n_ok, e_ok) = s.eval_check(op);
                match (n_ok, e_ok) {
                    (true, false) if res.state == CONST => {
                        if let Some(ty) = check_result_type(func, op) {
                            plans.push(Plan::Term(
                                block,
                                Term::JumpWithConst(normal.clone(), ty, res.bits),
                            ));
                        }
                    }
                    (true, false) => {
                        plans.push(Plan::Term(
                            block,
                            Term::JumpWithOp(normal.clone(), relaxed(op)),
                        ));
                    }
                    (false, true) if err.state == CONST => {
                        plans.push(Plan::Term(
                            block,
                            Term::JumpWithConst(error.clone(), Type::U32, err.bits),
                        ));
                    }
                    (false, false) => {
                        // Every operand is known and the operation traps.
                        let mut bits = [0u64; 2];
                        let mut n = 0;
                        let mut known = true;
                        op.for_each_operand(|v| {
                            let c = s.cell(v);
                            known &= c.state == CONST;
                            if let Some(slot) = bits.get_mut(n) {
                                *slot = c.bits;
                            }
                            n += 1;
                        });
                        if let (true, Fold::Trap(e)) = (known, fold_check(func, op, bits)) {
                            plans.push(Plan::Term(block, Term::Trap(e.code())));
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    drop(s);
    if plans.is_empty() {
        return Ok(false);
    }
    for plan in plans {
        match plan {
            Plan::Param(p, ty, bits) => {
                let Some(ValueDef::Param { block, .. }) = b.func().value_def(p) else {
                    continue;
                };
                let pos = block_start(b.func(), block);
                let c = constant(b, pos, ty, bits)?;
                b.replace_all_uses(p, c)?;
            }
            Plan::Inst(inst, r, ty, bits) => {
                let c = constant(b, Position::Before(inst), ty, bits)?;
                b.replace_all_uses(r, c)?;
                b.remove_inst(inst)?;
            }
            Plan::Select(inst, r, chosen) => {
                b.replace_all_uses(r, chosen)?;
                b.remove_inst(inst)?;
            }
            Plan::Term(block, Term::Jump(dest)) => {
                replace_terminator(b, block, Terminator::Jump(dest))?;
            }
            Plan::Term(block, Term::JumpWithConst(dest, ty, bits)) => {
                let c = constant(b, Position::End(block), ty, bits)?;
                replace_terminator(b, block, Terminator::Jump(substitute(&dest, c)))?;
            }
            Plan::Term(block, Term::JumpWithOp(dest, op)) => {
                b.set_position(Position::End(block))?;
                let inst = b.insert(op)?;
                let v = b
                    .results(inst)
                    .first()
                    .ok_or_else(crate::edit::inconsistent)?;
                replace_terminator(b, block, Terminator::Jump(substitute(&dest, v)))?;
            }
            Plan::Term(block, Term::Trap(code)) => {
                replace_terminator(b, block, Terminator::Trap { code })?;
            }
        }
    }
    Ok(true)
}
