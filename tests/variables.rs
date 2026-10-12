//! Differential tests on programs built the way irgen-lang lowers: mutable
//! locals through ir-lang's SSA construction (`declare_var`, `def_var`,
//! `use_var`, `seal_block`), OPS v2 `pow` and `saturate` shifts in `check`
//! terminators, and a GC reference kept in a variable across calls, with the
//! statepoints placed afterwards by `insert_statepoints`.
//!
//! Every program is run in the reference interpreter before and after
//! optimization (the whole pipeline and each pass alone); the outcome, the
//! import calls, and the validity of the IR must not change. The interpreter
//! detects a stale reference (one used after a safepoint without relocation)
//! at run time, and the validator checks the safepoint rules statically. As a
//! last oracle, statepoint insertion run again on the optimized function must
//! find nothing to add: no pass left a reference live across a safepoint
//! outside its GC list.

use ir_lang::interp::{Host, HostReturn, InterpError, Interpreter, Memory, Outcome, Val};
use ir_lang::{
    BinaryOp, Block, BlockArg, BlockCall, Builder, Call, CmpOp, ConvOp, FuncId, InstData, Linkage,
    MemFlags, Module, Overflow, Policy, Shift, Signature, Type, Value, Variable,
};
use opt_lang::{Budget, Optimizer, PassKind};
use proptest::prelude::*;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
}

const F8: MemFlags = MemFlags {
    align: 8,
    volatile: false,
};

struct Gen<'a, 'm> {
    b: &'a mut Builder<'m>,
    rng: Rng,
    vars: Vec<Variable>,
    obj: Variable,
    x: Value,
    poll: FuncId,
    observe: FuncId,
    budget: u32,
}

impl Gen<'_, '_> {
    fn konst(&mut self, v: i64) -> Value {
        self.b.iconst(Type::I64, i128::from(v)).unwrap()
    }

    fn var(&mut self) -> Variable {
        self.vars[self.rng.below(self.vars.len() as u64) as usize]
    }

    /// A block reached only from the current one: created, entered, sealed.
    fn fresh(&mut self, params: &[Type]) -> Block {
        self.b.create_block(params).unwrap()
    }

    /// Emits `data` as a `check` (it must be one): the error edge returns
    /// `code + 1000`, the normal edge continues with the result.
    fn checked(&mut self, data: InstData) -> Value {
        let ok = self.fresh(&[Type::I64]);
        let err = self.fresh(&[Type::U32]);
        self.b
            .check(
                data,
                BlockCall::with_args(ok, &[BlockArg::Result(0)]),
                BlockCall::with_args(err, &[BlockArg::ErrorCode]),
            )
            .unwrap();
        self.b.seal_block(ok).unwrap();
        self.b.seal_block(err).unwrap();
        self.b.switch_to(err).unwrap();
        let code = self.b.block_param(err, 0).unwrap();
        let wide = self
            .b
            .convert(ConvOp::Zext, Policy::NONE, code, Type::I64)
            .unwrap();
        let k = self.konst(1000);
        let r = self.b.add(wide, k, Overflow::Wrap).unwrap();
        self.b.ret(&[r]).unwrap();
        self.b.switch_to(ok).unwrap();
        self.b.block_param(ok, 0).unwrap()
    }

    fn leaf(&mut self) -> Value {
        match self.rng.below(4) {
            0 => {
                let v = self.rng.pick(&[0, 1, -1, 2, 3, 7, 64, i64::MAX, i64::MIN]);
                self.konst(v)
            }
            1 => self.x,
            _ => {
                let v = self.var();
                self.b.use_var(v).unwrap()
            }
        }
    }

    fn expr(&mut self, depth: u32) -> Value {
        self.budget = self.budget.saturating_sub(1);
        if depth == 0 || self.budget == 0 {
            return self.leaf();
        }
        let a = self.expr(depth - 1);
        match self.rng.below(7) {
            0 | 1 => {
                let b = self.expr(depth - 1);
                let op = self
                    .rng
                    .pick(&[BinaryOp::Add, BinaryOp::Sub, BinaryOp::Mul]);
                self.b
                    .binary(op, Policy::overflow(Overflow::Wrap), a, b)
                    .unwrap()
            }
            2 | 3 => {
                // `a ** e`: mostly a constant exponent, sometimes a variable.
                let e = if self.rng.below(4) == 0 {
                    self.leaf()
                } else {
                    let k = self.rng.pick(&[-1, 0, 1, 2, 2, 3, 4, 7]);
                    self.konst(k)
                };
                let o = self
                    .rng
                    .pick(&[Overflow::Wrap, Overflow::Trap, Overflow::Error]);
                self.checked(InstData::Binary {
                    op: BinaryOp::Pow,
                    policy: Policy::overflow(o),
                    args: [a, e],
                })
            }
            4 => {
                let k = self.rng.pick(&[-2, 0, 5, 63, 64, 100]);
                let n = self.konst(k);
                let op = self.rng.pick(&[BinaryOp::Shl, BinaryOp::Shr]);
                self.checked(InstData::Binary {
                    op,
                    policy: Policy::shift(Shift::Saturate),
                    args: [a, n],
                })
            }
            5 => {
                // A field of the object: a derived pointer used at once.
                let r = self.b.use_var(self.obj).unwrap();
                let p = self
                    .b
                    .convert(ConvOp::RefToPtr, Policy::NONE, r, Type::Ptr)
                    .unwrap();
                let k = (self.rng.below(8) * 8) as i64;
                let off = self.konst(k);
                let q = self.b.ptr_offset(p, off).unwrap();
                let v = self.b.load(Type::I64, q, F8).unwrap();
                self.b.add(a, v, Overflow::Wrap).unwrap()
            }
            _ => {
                let b = self.expr(depth - 1);
                self.b.binary(BinaryOp::Xor, Policy::NONE, a, b).unwrap()
            }
        }
    }

    fn stmts(&mut self, depth: u32) {
        let n = self.rng.below(4) + 1;
        for _ in 0..n {
            self.stmt(depth);
        }
    }

    fn stmt(&mut self, depth: u32) {
        let nested = depth > 0 && self.budget > 0;
        match self.rng.below(9) {
            0..=2 => {
                let v = self.var();
                let e = self.expr(3);
                self.b.def_var(v, e).unwrap();
            }
            3 if nested => {
                let a = self.expr(2);
                let zero = self.konst(0);
                let c = self.b.compare(CmpOp::Lt, a, zero).unwrap();
                let (t, e, join) = (self.fresh(&[]), self.fresh(&[]), self.fresh(&[]));
                self.b.branch(c, t, &[], e, &[]).unwrap();
                self.b.seal_block(t).unwrap();
                self.b.seal_block(e).unwrap();
                self.b.switch_to(t).unwrap();
                self.stmts(depth - 1);
                self.b.jump(join, &[]).unwrap();
                self.b.switch_to(e).unwrap();
                if self.rng.below(2) == 0 {
                    self.stmts(depth - 1);
                }
                self.b.jump(join, &[]).unwrap();
                self.b.seal_block(join).unwrap();
                self.b.switch_to(join).unwrap();
            }
            4 if nested => {
                // for i in 0..n { ... } with `i` a variable too; the head stays
                // unsealed until the back edge exists.
                let i = self.b.declare_var(Type::I64).unwrap();
                let zero = self.konst(0);
                self.b.def_var(i, zero).unwrap();
                let (head, body, exit) = (self.fresh(&[]), self.fresh(&[]), self.fresh(&[]));
                self.b.jump(head, &[]).unwrap();
                self.b.switch_to(head).unwrap();
                let iv = self.b.use_var(i).unwrap();
                let k = self.rng.below(4) as i64;
                let n = self.konst(k);
                let more = self.b.compare(CmpOp::Lt, iv, n).unwrap();
                self.b.branch(more, body, &[], exit, &[]).unwrap();
                self.b.seal_block(body).unwrap();
                self.b.switch_to(body).unwrap();
                self.stmts(depth - 1);
                let iv = self.b.use_var(i).unwrap();
                let one = self.konst(1);
                let next = self.b.add(iv, one, Overflow::Wrap).unwrap();
                self.b.def_var(i, next).unwrap();
                self.b.jump(head, &[]).unwrap();
                self.b.seal_block(head).unwrap();
                self.b.seal_block(exit).unwrap();
                self.b.switch_to(exit).unwrap();
            }
            5 | 6 => {
                // A safepoint with the object live: statepoint insertion lists
                // and relocates it later.
                let _ = self.b.call(Call::direct(self.poll, &[])).unwrap();
            }
            7 => {
                let v = self.var();
                let a = self.b.use_var(v).unwrap();
                let _ = self.b.call(Call::direct(self.observe, &[a])).unwrap();
            }
            _ => {
                // Store into the object through a derived pointer.
                let a = self.expr(1);
                let r = self.b.use_var(self.obj).unwrap();
                let p = self
                    .b
                    .convert(ConvOp::RefToPtr, Policy::NONE, r, Type::Ptr)
                    .unwrap();
                let k = (self.rng.below(8) * 8) as i64;
                let off = self.konst(k);
                let q = self.b.ptr_offset(p, off).unwrap();
                self.b.store(a, q, F8).unwrap();
            }
        }
    }
}

/// A program `f(x: i64) -> i64` built with variables, then given statepoints.
fn generate(seed: u64) -> (Module, FuncId) {
    let (m, f, _) = generate_counting(seed);
    (m, f)
}

/// [`generate`], also returning how many GC-list entries statepoint insertion
/// added.
fn generate_counting(seed: u64) -> (Module, FuncId, usize) {
    let mut m = Module::new("vars");
    let alloc = m
        .declare_function(
            "gc_alloc",
            &Signature::new(&[Type::I64], &[Type::Ref]),
            Linkage::Import,
        )
        .unwrap();
    let poll = m
        .declare_function("poll", &Signature::new(&[], &[]), Linkage::Import)
        .unwrap();
    let observe = m
        .declare_function(
            "observe",
            &Signature::new(&[Type::I64], &[]),
            Linkage::Import,
        )
        .unwrap();
    let f = m
        .declare_function(
            "f",
            &Signature::new(&[Type::I64], &[Type::I64]),
            Linkage::Export,
        )
        .unwrap();
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let vars: Vec<Variable> = (0..3).map(|_| b.declare_var(Type::I64).unwrap()).collect();
    b.def_var(vars[0], x).unwrap();
    let obj = b.declare_var(Type::Ref).unwrap();
    let size = b.iconst(Type::I64, 64).unwrap();
    let inst = b.call(Call::direct(alloc, &[size])).unwrap();
    let r = b.results(inst).first().unwrap();
    b.def_var(obj, r).unwrap();
    let mut g = Gen {
        b: &mut b,
        rng: Rng(seed | 1),
        vars,
        obj,
        x,
        poll,
        observe,
        budget: 60,
    };
    g.stmts(3);
    g.stmts(2);
    // Return a mix of every variable and one field of the object.
    let mut acc = g.b.use_var(g.vars[0]).unwrap();
    for k in 1..g.vars.len() {
        let v = g.b.use_var(g.vars[k]).unwrap();
        acc = g.b.binary(BinaryOp::Xor, Policy::NONE, acc, v).unwrap();
    }
    let r = g.b.use_var(g.obj).unwrap();
    let p =
        g.b.convert(ConvOp::RefToPtr, Policy::NONE, r, Type::Ptr)
            .unwrap();
    let field = g.b.load(Type::I64, p, F8).unwrap();
    let acc = g.b.add(acc, field, Overflow::Wrap).unwrap();
    g.b.ret(&[acc]).unwrap();
    b.seal_all_blocks().unwrap();
    let relocations = b.insert_statepoints().unwrap().relocations;
    (m, f, relocations)
}

#[derive(Default)]
struct Heap {
    trace: Vec<u64>,
}

impl Host for Heap {
    fn call(
        &mut self,
        name: &str,
        args: &[Val],
        mem: &mut Memory,
    ) -> Result<HostReturn, InterpError> {
        match name {
            "gc_alloc" => Ok(HostReturn::Values(vec![mem.alloc_object(args[0].bits())?])),
            "poll" => Ok(HostReturn::Values(vec![])),
            "observe" => {
                self.trace.push(args[0].bits());
                Ok(HostReturn::Values(vec![]))
            }
            _ => Err(InterpError::UnresolvedImport { name: name.into() }),
        }
    }
}

fn run(m: &Module, f: FuncId, x: i64) -> (Result<Outcome, InterpError>, Vec<u64>) {
    let mut vm = Interpreter::new(m, Heap::default()).unwrap();
    let out = vm.call(f, &[Val::i64(x)]);
    (out, core::mem::take(&mut vm.host_mut().trace))
}

/// Statepoint insertion on an already valid function adds nothing.
fn assert_statepoints_complete(m: &mut Module, f: FuncId) {
    let mut b = m.edit(f).unwrap();
    let stats = b.insert_statepoints().unwrap();
    assert_eq!(
        (stats.safepoints, stats.relocations, stats.params),
        (0, 0, 0),
        "{m}"
    );
}

fn check(seed: u64, xs: &[i64]) {
    let (m, f) = generate(seed);
    m.validate()
        .unwrap_or_else(|e| panic!("generator: {e}\n{m}"));
    let expect: Vec<_> = xs.iter().map(|&x| run(&m, f, x)).collect();
    for (e, x) in expect.iter().zip(xs) {
        assert!(e.0.is_ok(), "x = {x}: {:?}\n{m}", e.0);
    }
    let mut opt = m.clone();
    Optimizer::new()
        .validate(true)
        .run(&mut opt)
        .unwrap_or_else(|e| panic!("{e}\n{m}"));
    opt.validate().unwrap();
    for (e, &x) in expect.iter().zip(xs) {
        assert_eq!(&run(&opt, f, x), e, "x = {x}\n{m}\n{opt}");
    }
    assert_statepoints_complete(&mut opt, f);
    for kind in PassKind::ALL {
        let mut one = m.clone();
        let mut budget = Budget::unlimited();
        let _ = opt_lang::run_pass(&mut one.edit(f).unwrap(), kind, &mut budget)
            .unwrap_or_else(|e| panic!("{kind}: {e}\n{m}"));
        one.validate()
            .unwrap_or_else(|e| panic!("{kind}: {e}\n{one}"));
        for (e, &x) in expect.iter().zip(xs) {
            assert_eq!(&run(&one, f, x), e, "{kind} x = {x}\n{m}\n{one}");
        }
        assert_statepoints_complete(&mut one, f);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn prop_variable_programs_stay_valid_and_equal(seed in any::<u64>(), x in any::<i64>()) {
        check(seed, &[x, x % 7]);
    }
}

#[test]
fn test_variable_programs_on_many_seeds() {
    for seed in 0..300u64 {
        check(
            seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) + 11,
            &[0, 1, -3, 2, 40, i64::MAX, i64::MIN],
        );
    }
}

#[test]
fn test_variable_programs_are_optimized() {
    // The pipeline does real work on this shape: block parameters placed by
    // the SSA construction and constant `pow` checks are removed.
    let (mut before, mut after, mut relocations) = (0, 0, 0);
    for seed in 0..100u64 {
        let (mut m, _, r) = generate_counting(seed * 7 + 1);
        relocations += r;
        let stats = Optimizer::new().run(&mut m).unwrap();
        before += stats.insts_before() + stats.blocks_before();
        after += stats.insts_after() + stats.blocks_after();
    }
    assert!(after * 100 < before * 80, "{after} of {before}");
    assert!(relocations > 100, "the shape barely exercises statepoints");
}
