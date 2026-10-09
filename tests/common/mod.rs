//! Random ir-lang programs in SSA form, and an observer that runs them in the
//! ir-lang reference interpreter.
//!
//! The programs are built directly with the `Builder`, the way a front end
//! lowers: variables are SSA values, joins pass them as block parameters, loops
//! carry them in header parameters. They mix everything the optimizer must
//! respect: constants (so there is something to fold), redundant and
//! loop-invariant expressions, dead code, branches on constants, `switch`,
//! loops, checked arithmetic with `error`, `wrap`, and `trap` policies, float
//! conversions (NaN included), stack and global memory, volatile accesses,
//! atomics, bulk memory, direct and indirect calls, `invoke` with landing pads,
//! `resume`, traps, and calls to imports whose effects are recorded in order.
//!
//! Every program is free of undefined behaviour by construction (every access
//! is in bounds and aligned, `memcpy` ranges never overlap, `unreachable` is
//! never reached), so the original and the optimized program must agree exactly:
//! same return values or trap code or exception payload, same import calls with
//! the same arguments in the same order, and the same final global memory.

#![allow(dead_code, clippy::unwrap_used, clippy::expect_used)]

use ir_lang::interp::{Host, HostReturn, InterpError, Interpreter, Limits, Memory, Outcome, Val};
use ir_lang::{
    Attrs, BinaryOp, BlockArg, BlockCall, Builder, Call, CmpOp, ConvOp, DivZero, FloatToInt,
    FuncId, Global, GlobalId, InstData, Linkage, MemFlags, MemOrder, Module, Overflow, Policy,
    RmwOp, Shift, SigId, Signature, SwitchCase, Type, UnaryOp, Value,
};

/// A small deterministic generator (xorshift64*).
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }

    pub fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }

    pub fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }

    pub fn lit(&mut self) -> i64 {
        match self.below(6) {
            0 => self.pick(&[0, 1, -1, 2, 3, 5, 7, 63, 64, -64]),
            1 => self.pick(&[i64::MIN, i64::MAX, i64::MIN + 1, i64::MAX - 1]),
            2 => self.pick(&[i32::MIN as i64, i32::MAX as i64, u32::MAX as i64, 255, 256]),
            _ => (self.next() as i64) >> self.below(60),
        }
    }
}

/// A generated program.
pub struct Program {
    pub module: Module,
    pub entry: FuncId,
    pub globals: Vec<GlobalId>,
}

/// Number of SSA variables threaded through each function.
pub const VARS: usize = 3;

const F8: MemFlags = MemFlags {
    align: 8,
    volatile: false,
};

struct Ctx<'a, 'm> {
    b: &'a mut Builder<'m>,
    rng: &'a mut Rng,
    func: usize,
    funcs: &'a [FuncId],
    sig: SigId,
    observe: FuncId,
    maythrow: FuncId,
    globals: &'a [GlobalId],
    array: Value,
    params: [Value; 2],
    vars: Vec<Value>,
    budget: u32,
}

impl Ctx<'_, '_> {
    fn i64c(&mut self, v: i64) -> Value {
        self.b.iconst(Type::I64, i128::from(v)).unwrap()
    }

    fn overflow(&mut self) -> Overflow {
        self.rng.pick(&[
            Overflow::Wrap,
            Overflow::Wrap,
            Overflow::Trap,
            Overflow::Error,
        ])
    }

    /// Returns `(0 + code + offset)` from the function: the error path.
    fn ret_code(&mut self, code: Value, offset: i64) {
        let wide = self
            .b
            .convert(ConvOp::Zext, Policy::NONE, code, Type::I64)
            .unwrap();
        let off = self.i64c(offset);
        let r = self.b.add(wide, off, Overflow::Wrap).unwrap();
        self.b.ret(&[r]).unwrap();
    }

    /// Emits `data` as a plain instruction, or as a `check` whose error edge
    /// returns the code + 1000.
    fn op(&mut self, data: InstData) -> Value {
        let can_error = match &data {
            InstData::Unary { policy, .. }
            | InstData::Binary { policy, .. }
            | InstData::Convert { policy, .. } => policy.can_error(),
            _ => false,
        } || matches!(
            data,
            InstData::Convert {
                op: ConvOp::CharFromU32,
                ..
            }
        );
        if !can_error {
            let inst = self.b.insert(data).unwrap();
            return self.b.results(inst).first().unwrap();
        }
        let ty = match &data {
            InstData::Convert { to, .. } => *to,
            InstData::Unary { arg, .. } => self.b.func().value_type(*arg).unwrap(),
            InstData::Binary { args, .. } => self.b.func().value_type(args[0]).unwrap(),
            _ => Type::I64,
        };
        let ok = self.b.create_block(&[ty]).unwrap();
        let err = self.b.create_block(&[Type::U32]).unwrap();
        self.b
            .check(
                data,
                BlockCall::with_args(ok, &[BlockArg::Result(0)]),
                BlockCall::with_args(err, &[BlockArg::ErrorCode]),
            )
            .unwrap();
        self.b.switch_to(err).unwrap();
        let code = self.b.block_param(err, 0).unwrap();
        self.ret_code(code, 1000);
        self.b.switch_to(ok).unwrap();
        self.b.block_param(ok, 0).unwrap()
    }

    fn leaf(&mut self) -> Value {
        match self.rng.below(7) {
            0 | 1 => {
                let v = self.rng.lit();
                self.i64c(v)
            }
            2 => self.params[self.rng.below(2) as usize],
            3 | 4 => self.vars[self.rng.below(VARS as u64) as usize],
            5 => {
                // A global (g0 or g1, written by the program) or the constant table.
                let g = self.globals[self.rng.below(3) as usize];
                let a = self.b.global_addr(g).unwrap();
                let addr = if g == self.globals[2] {
                    let i = self.rng.below(8) as i64;
                    let idx = self.i64c(i);
                    self.b.elem_addr(a, Type::I64.into(), idx).unwrap()
                } else {
                    a
                };
                let flags = if self.rng.chance(15) {
                    F8.volatile()
                } else {
                    F8
                };
                self.b.load(Type::I64, addr, flags).unwrap()
            }
            _ => {
                // array[k & 7]
                let k = self.vars[self.rng.below(VARS as u64) as usize];
                let addr = self.slot(k);
                self.b.load(Type::I64, addr, F8).unwrap()
            }
        }
    }

    /// The address of `array[v & 7]`.
    fn slot(&mut self, v: Value) -> Value {
        let seven = self.i64c(7);
        let i = self
            .b
            .binary(BinaryOp::And, Policy::NONE, v, seven)
            .unwrap();
        self.b.elem_addr(self.array, Type::I64.into(), i).unwrap()
    }

    /// One of a few fixed expressions over the parameters, so the same
    /// computation appears in many blocks (value numbering and LICM fodder).
    fn common(&mut self) -> Value {
        let [p, q] = self.params;
        match self.rng.below(4) {
            0 => self.b.add(p, q, Overflow::Wrap).unwrap(),
            1 => {
                let k = self.i64c(3);
                self.b.mul(p, k, Overflow::Wrap).unwrap()
            }
            2 => {
                let k = self.i64c(255);
                self.b.binary(BinaryOp::Xor, Policy::NONE, q, k).unwrap()
            }
            _ => {
                let c = self.b.compare(CmpOp::Lt, p, q).unwrap();
                self.b.select(c, p, q).unwrap()
            }
        }
    }

    fn int_binary(&mut self, a: Value, b: Value) -> Value {
        let op = self.rng.pick(&[
            BinaryOp::Add,
            BinaryOp::Sub,
            BinaryOp::Mul,
            BinaryOp::Div,
            BinaryOp::Rem,
            BinaryOp::FloorDiv,
            BinaryOp::FloorMod,
            BinaryOp::And,
            BinaryOp::Or,
            BinaryOp::Xor,
            BinaryOp::Shl,
            BinaryOp::Shr,
            BinaryOp::Min,
            BinaryOp::Max,
        ]);
        let ov = self.overflow();
        let dz = self.rng.pick(&[DivZero::Error, DivZero::Trap]);
        let policy = match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => Policy::overflow(ov),
            BinaryOp::Div | BinaryOp::FloorDiv => Policy::overflow(ov).with_div_zero(dz),
            BinaryOp::Rem | BinaryOp::FloorMod => Policy::div_zero(dz),
            BinaryOp::Shl | BinaryOp::Shr => {
                Policy::shift(self.rng.pick(&[Shift::Mask, Shift::Mask, Shift::Error]))
            }
            _ => Policy::NONE,
        };
        self.op(InstData::Binary {
            op,
            policy,
            args: [a, b],
        })
    }

    fn float(&mut self, a: Value, b: Value) -> Value {
        let ty = if self.rng.chance(70) {
            Type::F64
        } else {
            Type::F32
        };
        let fa = self
            .b
            .convert(ConvOp::IntToFloat, Policy::NONE, a, ty)
            .unwrap();
        let fb = self
            .b
            .convert(ConvOp::IntToFloat, Policy::NONE, b, ty)
            .unwrap();
        let x = match self.rng.below(4) {
            0 => {
                let op = self.rng.pick(&[
                    UnaryOp::Neg,
                    UnaryOp::Abs,
                    UnaryOp::Sqrt,
                    UnaryOp::Floor,
                    UnaryOp::Ceil,
                    UnaryOp::Trunc,
                    UnaryOp::Round,
                    UnaryOp::RoundEven,
                ]);
                // Scale first so rounding has fractions to work on.
                let half = if ty == Type::F64 {
                    self.b.f64const(0.37).unwrap()
                } else {
                    self.b.f32const(0.37).unwrap()
                };
                let s = self
                    .b
                    .binary(BinaryOp::Mul, Policy::NONE, fa, half)
                    .unwrap();
                self.b.unary(op, Policy::NONE, s).unwrap()
            }
            1 if self.rng.chance(30) => self.b.fma(fa, fb, fa).unwrap(),
            _ => {
                let op = self.rng.pick(&[
                    BinaryOp::Add,
                    BinaryOp::Sub,
                    BinaryOp::Mul,
                    BinaryOp::Div,
                    BinaryOp::Rem,
                    BinaryOp::IeeeRem,
                    BinaryOp::Min,
                    BinaryOp::Max,
                ]);
                self.b.binary(op, Policy::NONE, fa, fb).unwrap()
            }
        };
        if self.rng.chance(15) {
            // Observe the bits directly (NaN payloads included).
            let bits_ty = if ty == Type::F64 {
                Type::I64
            } else {
                Type::I32
            };
            let raw = self
                .b
                .convert(ConvOp::Bitcast, Policy::NONE, x, bits_ty)
                .unwrap();
            if bits_ty == Type::I64 {
                return raw;
            }
            return self
                .b
                .convert(ConvOp::Sext, Policy::NONE, raw, Type::I64)
                .unwrap();
        }
        let p = self.rng.pick(&[
            FloatToInt::Saturate,
            FloatToInt::Saturate,
            FloatToInt::Error,
        ]);
        self.op(InstData::Convert {
            op: ConvOp::FloatToInt,
            policy: Policy::float_to_int(p),
            to: Type::I64,
            arg: x,
        })
    }

    fn call_expr(&mut self, a: Value, b: Value) -> Value {
        if self.func + 1 < self.funcs.len() && self.rng.chance(70) {
            let callee = self.funcs[self.func
                + 1
                + self.rng.below((self.funcs.len() - self.func - 1) as u64) as usize];
            let call = if self.rng.chance(30) {
                let addr = self.b.func_addr(callee).unwrap();
                Call::indirect(self.sig, addr, &[a, b])
            } else {
                Call::direct(callee, &[a, b])
            };
            if self.rng.chance(40) {
                return self.invoke(call);
            }
            let inst = self.b.call(call).unwrap();
            return self.b.results(inst).first().unwrap();
        }
        let call = Call::direct(self.maythrow, &[a]);
        if self.rng.chance(60) {
            return self.invoke(call);
        }
        let inst = self.b.call(call).unwrap();
        self.b.results(inst).first().unwrap()
    }

    /// An `invoke` whose landing pad returns `2000 + payload` or rethrows.
    fn invoke(&mut self, call: Call) -> Value {
        let normal = self.b.create_block(&[Type::I64]).unwrap();
        let pad = self.b.create_block(&[Type::Ptr]).unwrap();
        self.b
            .invoke(
                call,
                BlockCall::with_args(normal, &[BlockArg::Result(0)]),
                BlockCall::with_args(pad, &[BlockArg::Exception]),
            )
            .unwrap();
        self.b.switch_to(pad).unwrap();
        let exn = self.b.block_param(pad, 0).unwrap();
        if self.rng.chance(25) {
            self.b.resume(exn).unwrap();
        } else {
            let k = self
                .b
                .convert(ConvOp::PtrToInt, Policy::NONE, exn, Type::U64)
                .unwrap();
            let k = self
                .b
                .convert(ConvOp::Narrow, Policy::NONE, k, Type::U32)
                .unwrap();
            self.ret_code(k, 2000);
        }
        self.b.switch_to(normal).unwrap();
        self.b.block_param(normal, 0).unwrap()
    }

    fn expr(&mut self, depth: u32) -> Value {
        self.budget = self.budget.saturating_sub(1);
        if depth == 0 || self.budget == 0 || self.rng.chance(25) {
            return self.leaf();
        }
        let d = depth - 1;
        match self.rng.below(16) {
            0..=3 => {
                let a = self.expr(d);
                let b = self.expr(d);
                self.int_binary(a, b)
            }
            4 => {
                let a = self.expr(d);
                let op = self.rng.pick(&[UnaryOp::Neg, UnaryOp::Abs, UnaryOp::Not]);
                let policy = if op == UnaryOp::Not {
                    Policy::NONE
                } else {
                    Policy::overflow(self.overflow())
                };
                self.op(InstData::Unary { op, policy, arg: a })
            }
            5 => {
                let a = self.expr(d);
                let ov = self.overflow();
                let n = self.op(InstData::Convert {
                    op: ConvOp::IntCast,
                    policy: Policy::overflow(ov),
                    to: Type::I32,
                    arg: a,
                });
                self.b
                    .convert(ConvOp::Sext, Policy::NONE, n, Type::I64)
                    .unwrap()
            }
            6 => {
                let a = self.expr(d);
                let n = self
                    .b
                    .convert(ConvOp::Narrow, Policy::NONE, a, Type::U8)
                    .unwrap();
                self.b
                    .convert(ConvOp::Zext, Policy::NONE, n, Type::I64)
                    .unwrap()
            }
            7 => {
                let a = self.expr(d);
                let b = self.expr(d);
                self.float(a, b)
            }
            8 => {
                let a = self.expr(d);
                let b = self.expr(d);
                let t = self.expr(d);
                let f = self.expr(d);
                let op = self.rng.pick(&[
                    CmpOp::Eq,
                    CmpOp::Ne,
                    CmpOp::Lt,
                    CmpOp::Le,
                    CmpOp::Gt,
                    CmpOp::Ge,
                ]);
                let c = self.b.compare(op, a, b).unwrap();
                self.b.select(c, t, f).unwrap()
            }
            9 => {
                let a = self.expr(d);
                let b = self.expr(d);
                let c = self.b.compare(CmpOp::Le, a, b).unwrap();
                let n = self
                    .b
                    .convert(ConvOp::BoolToInt, Policy::NONE, c, Type::U8)
                    .unwrap();
                self.b
                    .convert(ConvOp::Zext, Policy::NONE, n, Type::I64)
                    .unwrap()
            }
            10 | 11 => self.common(),
            12 => {
                // A u32 checked as a char, then widened back.
                let a = self.expr(d);
                let n = self
                    .b
                    .convert(ConvOp::Narrow, Policy::NONE, a, Type::U32)
                    .unwrap();
                let mask = self.b.iconst(Type::U32, 0x1F_FFFF).unwrap();
                let n = self.b.binary(BinaryOp::And, Policy::NONE, n, mask).unwrap();
                let c = self.op(InstData::Convert {
                    op: ConvOp::CharFromU32,
                    policy: Policy::NONE,
                    to: Type::U32,
                    arg: n,
                });
                self.b
                    .convert(ConvOp::Zext, Policy::NONE, c, Type::I64)
                    .unwrap()
            }
            13 if self.budget > 4 => {
                let a = self.expr(d);
                let b = self.expr(d);
                self.call_expr(a, b)
            }
            _ => self.leaf(),
        }
    }

    fn cmp(&mut self) -> CmpOp {
        self.rng.pick(&[
            CmpOp::Eq,
            CmpOp::Ne,
            CmpOp::Lt,
            CmpOp::Le,
            CmpOp::Gt,
            CmpOp::Ge,
        ])
    }

    /// A condition: a comparison, or a constant (so branches can be folded).
    fn cond(&mut self) -> Value {
        if self.rng.chance(20) {
            let v = self.rng.chance(50);
            return self.b.bconst(v).unwrap();
        }
        if self.rng.chance(15) {
            let (x, y) = (self.rng.lit(), self.rng.lit());
            let (x, y) = (self.i64c(x), self.i64c(y));
            let op = self.cmp();
            return self.b.compare(op, x, y).unwrap();
        }
        let a = self.expr(2);
        let b = self.expr(2);
        let op = self.cmp();
        self.b.compare(op, a, b).unwrap()
    }

    fn stmts(&mut self, depth: u32, n: u64) {
        let count = self.rng.below(n) + 1;
        for _ in 0..count {
            self.stmt(depth);
        }
    }

    fn stmt(&mut self, depth: u32) {
        let nested = depth > 0 && self.budget > 0;
        match self.rng.below(20) {
            0..=4 => {
                let i = self.rng.below(VARS as u64) as usize;
                self.vars[i] = self.expr(3);
            }
            5 | 6 if nested => self.if_stmt(depth - 1),
            7 if nested => self.loop_stmt(depth - 1),
            8 if nested => self.switch_stmt(depth - 1),
            9 => {
                // array[i & 7] = v
                let i = self.expr(1);
                let v = self.vars[self.rng.below(VARS as u64) as usize];
                let addr = self.slot(i);
                self.b.store(v, addr, F8).unwrap();
            }
            10 => {
                let g = self.globals[self.rng.below(2) as usize];
                let v = self.expr(2);
                let a = self.b.global_addr(g).unwrap();
                let flags = if self.rng.chance(30) {
                    F8.volatile()
                } else {
                    F8
                };
                self.b.store(v, a, flags).unwrap();
            }
            11 => {
                let a = self.b.global_addr(self.globals[3]).unwrap();
                let v = self.expr(1);
                let op = self
                    .rng
                    .pick(&[RmwOp::Add, RmwOp::Xor, RmwOp::Max, RmwOp::Xchg]);
                let old = self.b.atomic_rmw(op, a, v, MemOrder::SeqCst).unwrap();
                let i = self.rng.below(VARS as u64) as usize;
                if self.rng.chance(50) {
                    self.vars[i] = old;
                }
            }
            12 => {
                // Copy the upper half of the array onto the lower half, or clear it.
                let half = self.b.iconst(Type::U64, 32).unwrap();
                if self.rng.chance(50) {
                    let four = self.i64c(4);
                    let src = self
                        .b
                        .elem_addr(self.array, Type::I64.into(), four)
                        .unwrap();
                    self.b.memcpy(self.array, src, half, F8).unwrap();
                } else {
                    let byte = self.b.iconst(Type::U8, 0xA5).unwrap();
                    self.b.memset(self.array, byte, half, F8).unwrap();
                }
            }
            13 => {
                let v = self.expr(2);
                let _ = self
                    .b
                    .call(Call::direct(self.observe, &[v]).with_attrs(Attrs::NOUNWIND))
                    .unwrap();
            }
            14 => {
                // Dead computation.
                let _ = self.expr(2);
            }
            15 if self.rng.chance(30) => {
                // if c { trap k }
                let c = self.cond();
                let t = self.b.create_block(&[]).unwrap();
                let cont = self.b.create_block(&[]).unwrap();
                self.b.branch(c, t, &[], cont, &[]).unwrap();
                self.b.switch_to(t).unwrap();
                let code = 10 + self.rng.below(9) as u32;
                self.b.trap(code).unwrap();
                self.b.switch_to(cont).unwrap();
            }
            16 if self.rng.chance(30) => {
                // if c { raise k }
                let c = self.cond();
                let t = self.b.create_block(&[]).unwrap();
                let cont = self.b.create_block(&[]).unwrap();
                self.b.branch(c, t, &[], cont, &[]).unwrap();
                self.b.switch_to(t).unwrap();
                let k = self
                    .b
                    .iconst(Type::U64, i128::from(self.rng.below(9) + 1))
                    .unwrap();
                let p = self
                    .b
                    .convert(ConvOp::IntToPtr, Policy::NONE, k, Type::Ptr)
                    .unwrap();
                self.b.resume(p).unwrap();
                self.b.switch_to(cont).unwrap();
            }
            _ => {
                let i = self.rng.below(VARS as u64) as usize;
                self.vars[i] = self.expr(2);
            }
        }
    }

    fn join(&mut self) -> ir_lang::Block {
        self.b.create_block(&[Type::I64; VARS]).unwrap()
    }

    fn enter_join(&mut self, join: ir_lang::Block) {
        self.b.switch_to(join).unwrap();
        for i in 0..VARS {
            self.vars[i] = self.b.block_param(join, i).unwrap();
        }
    }

    fn if_stmt(&mut self, depth: u32) {
        let c = self.cond();
        let (t, e, join) = (
            self.b.create_block(&[]).unwrap(),
            self.b.create_block(&[]).unwrap(),
            self.join(),
        );
        self.b.branch(c, t, &[], e, &[]).unwrap();
        let saved = self.vars.clone();
        self.b.switch_to(t).unwrap();
        self.stmts(depth, 3);
        let vt = self.vars.clone();
        self.b.jump(join, &vt).unwrap();
        self.vars = saved;
        self.b.switch_to(e).unwrap();
        if self.rng.chance(60) {
            self.stmts(depth, 2);
        }
        let ve = self.vars.clone();
        self.b.jump(join, &ve).unwrap();
        self.enter_join(join);
    }

    fn loop_stmt(&mut self, depth: u32) {
        let n = self.rng.below(4);
        let mut tys = vec![Type::U32];
        tys.extend([Type::I64; VARS]);
        let head = self.b.create_block(&tys).unwrap();
        let body = self.b.create_block(&[]).unwrap();
        let exit = self.b.create_block(&[]).unwrap();
        let zero = self.b.iconst(Type::U32, 0).unwrap();
        let mut args = vec![zero];
        args.extend(self.vars.iter().copied());
        self.b.jump(head, &args).unwrap();
        self.b.switch_to(head).unwrap();
        let i = self.b.block_param(head, 0).unwrap();
        for k in 0..VARS {
            self.vars[k] = self.b.block_param(head, k + 1).unwrap();
        }
        let at_head = self.vars.clone();
        let limit = self.b.iconst(Type::U32, i128::from(n)).unwrap();
        let more = self.b.compare(CmpOp::Lt, i, limit).unwrap();
        self.b.branch(more, body, &[], exit, &[]).unwrap();
        self.b.switch_to(body).unwrap();
        if self.rng.chance(60) {
            // A loop-invariant computation feeding a variable.
            let inv = self.common();
            let k = self.rng.below(VARS as u64) as usize;
            self.vars[k] = self.b.add(self.vars[k], inv, Overflow::Wrap).unwrap();
        }
        self.stmts(depth, 3);
        let one = self.b.iconst(Type::U32, 1).unwrap();
        let next = self.b.add(i, one, Overflow::Wrap).unwrap();
        let mut back = vec![next];
        back.extend(self.vars.iter().copied());
        self.b.jump(head, &back).unwrap();
        self.b.switch_to(exit).unwrap();
        self.vars = at_head;
    }

    fn switch_stmt(&mut self, depth: u32) {
        let scrutinee = if self.rng.chance(25) {
            let k = self.rng.below(5) as i64;
            self.i64c(k)
        } else {
            let v = self.expr(2);
            let three = self.i64c(3);
            self.b
                .binary(BinaryOp::And, Policy::NONE, v, three)
                .unwrap()
        };
        let join = self.join();
        let saved = self.vars.clone();
        let mut cases = Vec::new();
        let blocks: Vec<_> = (0..3).map(|_| self.b.create_block(&[]).unwrap()).collect();
        let default = self.b.create_block(&[]).unwrap();
        for (k, &blk) in blocks.iter().enumerate() {
            cases.push(SwitchCase {
                value: k as u64,
                dest: BlockCall::new(blk, &[]),
            });
        }
        self.b
            .switch(scrutinee, cases, BlockCall::new(default, &[]))
            .unwrap();
        for blk in blocks.into_iter().chain([default]) {
            self.vars = saved.clone();
            self.b.switch_to(blk).unwrap();
            if self.rng.chance(70) {
                self.stmts(depth, 2);
            }
            let v = self.vars.clone();
            self.b.jump(join, &v).unwrap();
        }
        self.enter_join(join);
    }
}

/// Generates a program; `size` scales the statement budget per function.
pub fn generate_sized(seed: u64, size: u32) -> Program {
    let mut rng = Rng::new(seed);
    let mut module = Module::new("random");
    let sig = Signature::new(&[Type::I64, Type::I64], &[Type::I64]);
    let sig_id = module.intern_signature(&sig).unwrap();
    let observe = module
        .declare_function(
            "observe",
            &Signature::new(&[Type::I64], &[]),
            Linkage::Import,
        )
        .unwrap();
    let maythrow = module
        .declare_function(
            "maythrow",
            &Signature::new(&[Type::I64], &[Type::I64]),
            Linkage::Import,
        )
        .unwrap();
    let table: Vec<u8> = (0..64u8).map(|i| i.wrapping_mul(37) ^ 0x5a).collect();
    let globals = vec![
        module
            .declare_global("g0", Global::zeroed(8, 8).mutable())
            .unwrap(),
        module
            .declare_global("g1", Global::zeroed(8, 8).mutable())
            .unwrap(),
        module
            .declare_global("table", Global::bytes(&table, 8))
            .unwrap(),
        module
            .declare_global("counter", Global::zeroed(8, 8).mutable())
            .unwrap(),
    ];
    let nfuncs = rng.below(3) as usize + 1;
    let funcs: Vec<FuncId> = (0..nfuncs)
        .map(|i| {
            module
                .declare_function(&format!("f{i}"), &sig, Linkage::Export)
                .unwrap()
        })
        .collect();
    for (i, &f) in funcs.iter().enumerate() {
        let mut b = module.build(f).unwrap();
        let slot = b.stack_slot(64, 8).unwrap();
        let array = b.stack_addr(slot).unwrap();
        let zero = b.iconst(Type::U8, 0).unwrap();
        let len = b.iconst(Type::U64, 64).unwrap();
        b.memset(array, zero, len, F8).unwrap();
        let params = [b.param(0).unwrap(), b.param(1).unwrap()];
        let mut ctx = Ctx {
            b: &mut b,
            rng: &mut rng,
            func: i,
            funcs: &funcs,
            sig: sig_id,
            observe,
            maythrow,
            globals: &globals,
            array,
            params,
            vars: vec![params[0], params[1], params[0]],
            budget: size,
        };
        ctx.stmts(3, 6);
        // Return a mix of every variable so they all stay observable.
        let mut acc = ctx.vars[0];
        for k in 1..VARS {
            let v = ctx.vars[k];
            acc = ctx.b.binary(BinaryOp::Xor, Policy::NONE, acc, v).unwrap();
        }
        if i + 1 < nfuncs && ctx.rng.chance(20) {
            let callee = funcs[i + 1];
            ctx.b
                .tail_call(Call::direct(callee, &[acc, params[1]]))
                .unwrap();
        } else {
            ctx.b.ret(&[acc]).unwrap();
        }
    }
    Program {
        module,
        entry: funcs[0],
        globals,
    }
}

/// Generates a program of the default size.
pub fn generate(seed: u64) -> Program {
    generate_sized(seed, 70)
}

/// The host: records every import call and implements `observe` and
/// `maythrow` (which unwinds for multiples of 5).
#[derive(Default)]
pub struct Recorder {
    pub trace: Vec<(String, Vec<u64>)>,
}

impl Host for Recorder {
    fn call(
        &mut self,
        name: &str,
        args: &[Val],
        _: &mut Memory,
    ) -> Result<HostReturn, InterpError> {
        self.trace
            .push((name.to_string(), args.iter().map(|a| a.bits()).collect()));
        match name {
            "observe" => Ok(HostReturn::Values(vec![])),
            "maythrow" => {
                let x = args[0].bits() as i64;
                if x.rem_euclid(5) == 0 {
                    Ok(HostReturn::Unwind(Val::ptr((x as u64 & 0xff) + 1)))
                } else {
                    Ok(HostReturn::Values(vec![Val::i64(x.wrapping_mul(3) ^ 1)]))
                }
            }
            _ => Err(InterpError::UnresolvedImport { name: name.into() }),
        }
    }
}

/// Everything observable about one run.
#[derive(Debug)]
pub struct Observation {
    pub outcome: Result<Outcome, InterpError>,
    pub trace: Vec<(String, Vec<u64>)>,
    pub globals: Vec<Vec<u8>>,
}

impl Observation {
    /// Whether the run stopped on a resource limit (not a program behaviour).
    pub fn limited(&self) -> bool {
        matches!(
            self.outcome,
            Err(InterpError::FuelExhausted | InterpError::StackOverflow | InterpError::OutOfMemory)
        )
    }

    /// Whether two runs are indistinguishable.
    pub fn same(&self, other: &Observation) -> bool {
        let outcome = match (&self.outcome, &other.outcome) {
            (Ok(Outcome::Return(a)), Ok(Outcome::Return(b))) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.same_as(*y))
            }
            (Ok(a), Ok(b)) => a == b,
            (Err(a), Err(b)) => a == b,
            _ => false,
        };
        outcome && self.trace == other.trace && self.globals == other.globals
    }
}

/// Runs `entry(a, b)` in the reference interpreter.
pub fn observe(
    module: &Module,
    entry: FuncId,
    globals: &[GlobalId],
    a: i64,
    b: i64,
) -> Observation {
    let limits = Limits {
        fuel: 2_000_000,
        ..Limits::default()
    };
    let mut vm = match Interpreter::with_limits(module, Recorder::default(), limits) {
        Ok(vm) => vm,
        Err(e) => {
            return Observation {
                outcome: Err(e),
                trace: Vec::new(),
                globals: Vec::new(),
            };
        }
    };
    let outcome = vm.call(entry, &[Val::i64(a), Val::i64(b)]);
    let globals = globals
        .iter()
        .map(|&g| {
            vm.global_address(g)
                .and_then(|addr| vm.memory().read(addr, 8).ok().map(<[u8]>::to_vec))
                .unwrap_or_default()
        })
        .collect();
    let trace = core::mem::take(&mut vm.host_mut().trace);
    Observation {
        outcome,
        trace,
        globals,
    }
}
