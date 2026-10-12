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
//! - a `check` with only some operands constant is folded as far as OPS allows
//!   (`fold::binary_partial`): `x ** 0` is `1`, `x ** 1` and `x + 0` are `x`,
//!   a negative constant exponent always raises `NegativeExponent`, a division
//!   by a constant zero always raises or traps. The normal edge then receives
//!   the constant or the operand, or control goes straight to the error edge.
//! - a `check` whose operation provably cannot raise (adding or subtracting a
//!   constant zero, multiplying by a constant zero or one, a shift by a
//!   constant in range or a non-negative constant under `saturate`, a division
//!   by a constant other than `0` and `-1`, a widening `int_cast`, a `pow` with
//!   a constant non-negative exponent under `wrap` or `trap`) becomes the plain
//!   operation and a jump, **but only when ir-lang's `can_error` accepts the
//!   plain form**. A signed `pow` is always fallible by that rule (its exponent
//!   could be negative), so it stays a `check`: `x ** 2` becomes `x * x` under
//!   the same overflow policy (a plain `mul` under `wrap`/`trap`, a
//!   `check mul` under `error`), and any other exponent keeps the `check` with
//!   its dead error edge redirected to an `unreachable` block, so the error
//!   handler can be deleted. An error edge that can fire is never touched.
//! - a `check`'s error code is known on its error edge when only one error
//!   kind remains possible.
//!
//! Plain integer operations get the same partial folding: `x ** 0`, `x * 0`,
//! and `shl<saturate>` by at least the width become constants, `x ** 1` and
//! `x + 0` become `x`, and `x ** 2` becomes `x * x`.
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
    InstData, Overflow, Policy, Position, Shift, Terminator, Type, Value, ValueDef,
};

use crate::Budget;
use crate::analysis::{Cfg, edge, is_tracked, is_unwind_edge, tracked_values};
use crate::edit::{
    block_start, constant, own_operands, replace_terminator, rewrite_terminator, use_counts,
};
use crate::fold::{self, Fold, Partial};

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
                let (x, y) = (self.cell(args[0]), self.cell(args[1]));
                if x.state == CONST && y.state == CONST {
                    fold_cell(fold::binary(*op, *policy, ty(args[0]), x.bits, y.bits))
                } else if x.state == BOTTOM && y.state == BOTTOM {
                    BOTTOM_CELL
                } else if x.state == BOTTOM || y.state == BOTTOM {
                    // One operand is known: the OPS identities.
                    match self.partial(*op, *policy, args) {
                        Partial::Always(Fold::Value(bits)) => konst(bits),
                        Partial::Operand(k) => self.cell(args[k]),
                        _ => BOTTOM_CELL,
                    }
                } else {
                    TOP_CELL
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

    /// The type of `v` (`ptr` for an unknown value, which is never folded).
    fn ty(&self, v: Value) -> Type {
        self.func.value_type(v).unwrap_or(Type::Ptr)
    }

    /// The constant bits of `v`, if the analysis found it constant.
    fn known(&self, v: Value) -> Option<u64> {
        let c = self.cell(v);
        (c.state == CONST).then_some(c.bits)
    }

    /// A binary operation folded as far as its constant operands allow.
    fn partial(&self, op: BinaryOp, policy: Policy, args: &[Value; 2]) -> Partial {
        fold::binary_partial(
            op,
            policy,
            self.ty(args[0]),
            self.known(args[0]),
            self.known(args[1]),
        )
    }

    /// What is known about a `check`'s operation; `None` while an operand is
    /// still unknown (the optimistic top of the lattice).
    fn check_partial(&self, data: &InstData) -> Option<Partial> {
        let mut any_top = false;
        data.for_each_operand(|v| any_top |= self.cell(v).state == TOP);
        if any_top {
            return None;
        }
        let open = |errors| Partial::Open {
            value: None,
            errors,
        };
        let whole = |f: Fold, errors| match f {
            Fold::Unknown => open(errors),
            f => Partial::Always(f),
        };
        Some(match data {
            InstData::Binary { op, policy, args } => self.partial(*op, *policy, args),
            InstData::Unary { op, policy, arg } => {
                let ty = self.ty(*arg);
                let errors = fold::error_kinds(data, ty);
                match self.known(*arg) {
                    Some(bits) => whole(fold::unary(*op, *policy, ty, bits), errors),
                    None => open(errors),
                }
            }
            InstData::Convert {
                op,
                policy,
                to,
                arg,
            } => {
                let from = self.ty(*arg);
                let errors = fold::error_kinds(data, from);
                match self.known(*arg) {
                    Some(bits) => whole(fold::convert(*op, *policy, from, *to, bits), errors),
                    // A widening `int_cast` always fits.
                    None if *op == ConvOp::IntCast && widens(from, *to) => open(0),
                    None => open(errors),
                }
            }
            _ => open(fold::error_kinds(data, Type::Ptr)),
        })
    }

    /// The `check` result, error-code cell, and feasible edges (normal, error)
    /// implied by what is known about its operation.
    fn outcome(&self, data: &InstData, p: Partial) -> (Cell, Cell, bool, bool) {
        match p {
            Partial::Always(Fold::Value(v)) => (konst(v), TOP_CELL, true, false),
            Partial::Always(Fold::Error(e)) => (TOP_CELL, konst(u64::from(e.code())), false, true),
            Partial::Always(Fold::Trap(_)) => (TOP_CELL, TOP_CELL, false, false),
            Partial::Always(Fold::Unknown) => (BOTTOM_CELL, BOTTOM_CELL, true, true),
            Partial::Operand(k) => {
                let res = match data {
                    InstData::Binary { args, .. } => {
                        args.get(k).map_or(BOTTOM_CELL, |&v| self.cell(v))
                    }
                    _ => BOTTOM_CELL,
                };
                (res, TOP_CELL, true, false)
            }
            Partial::Open { value, errors } => {
                let res = value.map_or(BOTTOM_CELL, konst);
                if errors == 0 {
                    (res, TOP_CELL, true, false)
                } else {
                    let err = if errors.count_ones() == 1 {
                        konst(u64::from(errors.trailing_zeros()))
                    } else {
                        BOTTOM_CELL
                    };
                    (res, err, true, true)
                }
            }
        }
    }

    /// The `check` result, error-code cell, and feasible edges (normal, error).
    fn eval_check(&self, data: &InstData) -> (Cell, Cell, bool, bool) {
        match self.check_partial(data) {
            Some(p) => self.outcome(data, p),
            None => (TOP_CELL, TOP_CELL, false, false),
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

/// The result type of a `check`'s operation.
fn check_result_type(func: &Function, op: &InstData) -> Option<Type> {
    match op {
        InstData::Unary { arg, .. } => func.value_type(*arg),
        InstData::Binary { args, .. } => func.value_type(args[0]),
        InstData::Convert { to, .. } => Some(*to),
        _ => None,
    }
}

/// The operand type that decides fallibility (the first operand's).
fn operand_type(func: &Function, data: &InstData) -> Type {
    let v = match data {
        InstData::Unary { arg, .. } | InstData::Convert { arg, .. } => *arg,
        InstData::Binary { args, .. } => args[0],
        _ => return Type::Ptr,
    };
    func.value_type(v).unwrap_or(Type::Ptr)
}

/// ir-lang's placement rule: whether `data` must be the operation of a
/// `check` (and can only be one).
fn can_error(data: &InstData, ty: Type) -> bool {
    match data {
        InstData::Unary { op, policy, .. } => op.can_error(*policy),
        InstData::Binary { op, policy, .. } => op.can_error(*policy, ty),
        InstData::Convert { op, policy, .. } => op.can_error(*policy),
        _ => true,
    }
}

/// `x ** 2` as `x * x` under the same overflow policy: exactly equal under
/// OPS (the same bits under `wrap`, the same overflow under `error` and
/// `trap`, and no negative exponent). `None` for any other operation, or for
/// `error` unless `allow_error` (the result must then stay in a `check`).
fn square(data: &InstData, exponent: Option<u64>, ty: Type, allow_error: bool) -> Option<InstData> {
    let InstData::Binary {
        op: BinaryOp::Pow,
        policy,
        args,
    } = data
    else {
        return None;
    };
    let o = policy.overflow?;
    if !ty.is_int() || exponent != Some(2) || (o == Overflow::Error && !allow_error) {
        return None;
    }
    Some(InstData::Binary {
        op: BinaryOp::Mul,
        policy: Policy::overflow(o),
        args: [args[0], args[0]],
    })
}

/// The plain (non-raising) form of a `check`'s operation that the analysis
/// proved cannot raise, if the IR accepts one: the `error` fields turned into
/// ones that act identically on every input the analysis allows, and a signed
/// `saturate` shift by a known non-negative amount turned into `mask` (with
/// the amount `width - 1` for an amount past the width, which gives the same
/// sign fill). The second element is that replacement amount, if any.
fn plain_form(
    func: &Function,
    data: &InstData,
    rhs: Option<u64>,
) -> Option<(InstData, Option<u64>)> {
    let ty = operand_type(func, data);
    let mut data = data.clone();
    let mut amount = None;
    if let InstData::Unary { policy, .. }
    | InstData::Binary { policy, .. }
    | InstData::Convert { policy, .. } = &mut data
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
    if let InstData::Binary {
        op: BinaryOp::Shl | BinaryOp::Shr,
        policy,
        ..
    } = &mut data
    {
        if policy.shift == Some(Shift::Saturate) && ty.is_signed_int() {
            let w = i128::from(ty.int_bits()?);
            let y = fold::sval(ty, rhs?);
            if y < 0 {
                return None;
            }
            policy.shift = Some(Shift::Mask);
            if y >= w {
                amount = Some((w - 1) as u64);
            }
        }
    }
    if !can_error(&data, ty) {
        return Some((data, amount));
    }
    square(&data, rhs, ty, false).map(|d| (d, None))
}

/// Whether `block` is an `unreachable` stub: no parameters, no instructions,
/// terminated by `unreachable`.
fn is_dead_stub(func: &Function, block: Block) -> bool {
    func.block_params(block).is_empty()
        && func.first_inst(block).is_none()
        && matches!(func.terminator(block), Some(Terminator::Unreachable))
}

/// An existing reachable stub (not the entry, not a landing pad) to reuse for
/// dead error edges.
fn find_stub(func: &Function, cfg: &Cfg) -> Option<Block> {
    cfg.rpo.iter().map(|&b| Block::from_u32(b)).find(|&b| {
        b != func.entry()
            && is_dead_stub(func, b)
            && !cfg.preds(b.index()).iter().any(|e| {
                func.terminator(Block::from_u32(e.from))
                    .is_some_and(|t| is_unwind_edge(t, e.idx as usize))
            })
    })
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
        /// Replace an instruction's result with an existing value (the chosen
        /// operand of a `select`, or `x` for `x ** 1`) and remove it.
        Forward(Inst, Value, Value),
        /// Replace an instruction's operation (`x ** 2` by `x * x`).
        Replace(Inst, InstData),
        /// Replace a terminator.
        Term(Block, Term),
        /// Point a `check`'s error edge, which cannot be taken, at the
        /// `unreachable` stub.
        DeadError(Block),
    }
    enum Term {
        Jump(BlockCall),
        /// Jump along `dest` with the produced argument a new constant.
        JumpWithConst(BlockCall, Type, u64),
        /// Jump along `dest` with the produced argument an existing value.
        JumpWithValue(BlockCall, Value),
        /// Jump along `dest` with the produced argument the plain operation
        /// (whose second operand becomes a new constant if one is given).
        JumpWithOp(BlockCall, InstData, Option<u64>),
        /// The same `check` with a cheaper operation.
        CheckOp(InstData, BlockCall, BlockCall),
        Trap(u32),
    }
    let stub = find_stub(func, &s.cfg);
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
                        plans.push(Plan::Forward(inst, r, chosen));
                    }
                }
            } else if let InstData::Binary { op, policy, args } = data {
                // The identities need a known operand.
                if !s.constable(r) || (s.known(args[0]).is_none() && s.known(args[1]).is_none()) {
                    continue;
                }
                if let Partial::Operand(k) = s.partial(*op, *policy, args) {
                    let v = func.resolve(args[k]);
                    if v != r {
                        plans.push(Plan::Forward(inst, r, v));
                    }
                } else if let Some(m) = square(data, s.known(args[1]), s.ty(args[0]), false) {
                    plans.push(Plan::Replace(inst, m));
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
                let Some(p) = s.check_partial(op) else {
                    continue;
                };
                let (res, err, n_ok, e_ok) = s.outcome(op, p);
                let rhs = match &**op {
                    InstData::Binary { args, .. } => s.known(args[1]),
                    _ => None,
                };
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
                        if let (Partial::Operand(k), InstData::Binary { args, .. }) = (p, &**op) {
                            let v = func.resolve(args[k]);
                            plans.push(Plan::Term(block, Term::JumpWithValue(normal.clone(), v)));
                        } else if let Some((data, amount)) = plain_form(func, op, rhs) {
                            plans.push(Plan::Term(
                                block,
                                Term::JumpWithOp(normal.clone(), data, amount),
                            ));
                        } else if !is_dead_stub(func, error.block) {
                            // The operation must stay a `check`, but its error
                            // edge cannot be taken.
                            plans.push(Plan::DeadError(block));
                        }
                    }
                    (true, true) => {
                        let ty = operand_type(func, op);
                        if let Some(m) = square(op, rhs, ty, true) {
                            plans.push(Plan::Term(
                                block,
                                Term::CheckOp(m, normal.clone(), error.clone()),
                            ));
                        }
                    }
                    (false, true) if err.state == CONST => {
                        plans.push(Plan::Term(
                            block,
                            Term::JumpWithConst(error.clone(), Type::U32, err.bits),
                        ));
                    }
                    (false, false) => {
                        if let Partial::Always(Fold::Trap(e)) = p {
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
    let mut stub = stub;
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
            Plan::Forward(inst, r, v) => {
                b.replace_all_uses(r, v)?;
                b.remove_inst(inst)?;
            }
            Plan::Replace(inst, data) => b.replace_inst(inst, data)?,
            Plan::DeadError(block) => {
                let target = match stub {
                    Some(t) => t,
                    None => {
                        let t = b.create_block(&[])?;
                        b.switch_to(t)?;
                        b.unreachable()?;
                        stub = Some(t);
                        t
                    }
                };
                rewrite_terminator(b, block, |term| {
                    if let Terminator::Check { error, .. } = term {
                        *error = BlockCall::new(target, &[]);
                    }
                })?;
            }
            Plan::Term(block, Term::Jump(dest)) => {
                replace_terminator(b, block, Terminator::Jump(dest))?;
            }
            Plan::Term(block, Term::JumpWithConst(dest, ty, bits)) => {
                let c = constant(b, Position::End(block), ty, bits)?;
                replace_terminator(b, block, Terminator::Jump(substitute(&dest, c)))?;
            }
            Plan::Term(block, Term::JumpWithValue(dest, v)) => {
                replace_terminator(b, block, Terminator::Jump(substitute(&dest, v)))?;
            }
            Plan::Term(block, Term::CheckOp(op, normal, error)) => {
                replace_terminator(
                    b,
                    block,
                    Terminator::Check {
                        op: alloc::boxed::Box::new(op),
                        normal,
                        error,
                    },
                )?;
            }
            Plan::Term(block, Term::JumpWithOp(dest, mut op, amount)) => {
                if let (Some(bits), InstData::Binary { args, .. }) = (amount, &mut op) {
                    let ty = b
                        .func()
                        .value_type(args[1])
                        .ok_or(BuildError::UnknownValue { value: args[1] })?;
                    args[1] = constant(b, Position::End(block), ty, bits)?;
                }
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
