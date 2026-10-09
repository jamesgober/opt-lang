//! GC references and safepoints: random programs that carry a `ref` through
//! safepoints (relocating it each time), in branches and loops, and read and
//! write the object through derived pointers. The optimized program must still
//! satisfy the safepoint rules (the validator checks them) and behave the same
//! (the interpreter catches a stale reference at run time).

use ir_lang::interp::{Host, HostReturn, InterpError, Interpreter, Memory, Val};
use ir_lang::{
    Builder, Call, CmpOp, ConvOp, FuncId, Linkage, MemFlags, Module, Overflow, Policy, Signature,
    Type, Value,
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
        self.next() % n
    }
}

struct Gen<'a, 'm> {
    b: &'a mut Builder<'m>,
    rng: Rng,
    poll: FuncId,
    acc: Value,
    r: Value,
    budget: u32,
}

const F8: MemFlags = MemFlags {
    align: 8,
    volatile: false,
};

impl Gen<'_, '_> {
    fn field(&mut self) -> Value {
        // A derived pointer into the object, used at once.
        let p = self
            .b
            .convert(ConvOp::RefToPtr, Policy::NONE, self.r, Type::Ptr)
            .unwrap();
        let k = self
            .b
            .iconst(Type::I64, (self.rng.below(8) * 8) as i128)
            .unwrap();
        self.b.ptr_offset(p, k).unwrap()
    }

    fn stmt(&mut self, depth: u32) {
        self.budget = self.budget.saturating_sub(1);
        match self.rng.below(9) {
            0 => {
                // A safepoint: relocate the reference.
                let inst = if self.rng.below(2) == 0 {
                    self.b.safepoint(&[self.r]).unwrap()
                } else {
                    self.b
                        .call(Call::direct(self.poll, &[]).with_gc(&[self.r]))
                        .unwrap()
                };
                self.r = self.b.results(inst).first().unwrap();
            }
            1 | 2 => {
                let q = self.field();
                let v = self.b.load(Type::I64, q, F8).unwrap();
                self.acc = self.b.add(self.acc, v, Overflow::Wrap).unwrap();
                // The same derived pointer, recomputed (must not be merged
                // across a safepoint, may be within one).
                let q2 = self.field();
                let w = self.b.load(Type::I64, q2, F8).unwrap();
                self.acc = self
                    .b
                    .binary(ir_lang::BinaryOp::Xor, Policy::NONE, self.acc, w)
                    .unwrap();
            }
            3 => {
                let q = self.field();
                self.b.store(self.acc, q, F8).unwrap();
            }
            6 => {
                // A null check (a `ref` constant, which must not be shared
                // across safepoints or hoisted out of a loop that has one).
                let null = self.b.null(Type::Ref).unwrap();
                let c = self.b.compare(CmpOp::Eq, self.r, null).unwrap();
                let one = self.b.iconst(Type::I64, 1).unwrap();
                let zero = self.b.iconst(Type::I64, 0).unwrap();
                let bit = self.b.select(c, one, zero).unwrap();
                self.acc = self.b.add(self.acc, bit, Overflow::Wrap).unwrap();
            }
            4 if depth > 0 && self.budget > 0 => {
                let zero = self.b.iconst(Type::I64, 0).unwrap();
                let c = self.b.compare(CmpOp::Lt, self.acc, zero).unwrap();
                let (t, e) = (
                    self.b.create_block(&[]).unwrap(),
                    self.b.create_block(&[]).unwrap(),
                );
                let join = self.b.create_block(&[Type::I64, Type::Ref]).unwrap();
                self.b.branch(c, t, &[], e, &[]).unwrap();
                let (acc, r) = (self.acc, self.r);
                self.b.switch_to(t).unwrap();
                self.stmt(depth - 1);
                self.stmt(depth - 1);
                self.b.jump(join, &[self.acc, self.r]).unwrap();
                self.acc = acc;
                self.r = r;
                self.b.switch_to(e).unwrap();
                self.stmt(depth - 1);
                self.b.jump(join, &[self.acc, self.r]).unwrap();
                self.b.switch_to(join).unwrap();
                self.acc = self.b.block_param(join, 0).unwrap();
                self.r = self.b.block_param(join, 1).unwrap();
            }
            5 if depth > 0 && self.budget > 0 => {
                let head = self
                    .b
                    .create_block(&[Type::U32, Type::I64, Type::Ref])
                    .unwrap();
                let body = self.b.create_block(&[]).unwrap();
                let exit = self.b.create_block(&[]).unwrap();
                let zero = self.b.iconst(Type::U32, 0).unwrap();
                self.b.jump(head, &[zero, self.acc, self.r]).unwrap();
                self.b.switch_to(head).unwrap();
                let i = self.b.block_param(head, 0).unwrap();
                self.acc = self.b.block_param(head, 1).unwrap();
                self.r = self.b.block_param(head, 2).unwrap();
                let (acc, r) = (self.acc, self.r);
                let n = self
                    .b
                    .iconst(Type::U32, i128::from(self.rng.below(4)))
                    .unwrap();
                let more = self.b.compare(CmpOp::Lt, i, n).unwrap();
                self.b.branch(more, body, &[], exit, &[]).unwrap();
                self.b.switch_to(body).unwrap();
                // A loop-invariant computation next to the reference traffic.
                let seven = self.b.iconst(Type::I64, 7).unwrap();
                let inv = self.b.mul(seven, seven, Overflow::Wrap).unwrap();
                self.acc = self.b.add(self.acc, inv, Overflow::Wrap).unwrap();
                self.stmt(depth - 1);
                self.stmt(depth - 1);
                let one = self.b.iconst(Type::U32, 1).unwrap();
                let next = self.b.add(i, one, Overflow::Wrap).unwrap();
                self.b.jump(head, &[next, self.acc, self.r]).unwrap();
                self.b.switch_to(exit).unwrap();
                self.acc = acc;
                self.r = r;
            }
            _ => {
                let k = self
                    .b
                    .iconst(Type::I64, (self.rng.below(100) as i128) - 50)
                    .unwrap();
                let two = self.b.iconst(Type::I64, 2).unwrap();
                let c = self.b.mul(k, two, Overflow::Wrap).unwrap();
                self.acc = self.b.add(self.acc, c, Overflow::Wrap).unwrap();
            }
        }
    }
}

fn generate(seed: u64) -> (Module, FuncId) {
    let mut m = Module::new("gc");
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
    let f = m
        .declare_function(
            "f",
            &Signature::new(&[Type::I64], &[Type::I64]),
            Linkage::Export,
        )
        .unwrap();
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let size = b.iconst(Type::I64, 64).unwrap();
    let inst = b.call(Call::direct(alloc, &[size])).unwrap();
    let r = b.results(inst).first().unwrap();
    let mut g = Gen {
        b: &mut b,
        rng: Rng(seed | 1),
        poll,
        acc: x,
        r,
        budget: 40,
    };
    for _ in 0..8 {
        g.stmt(3);
    }
    let acc = g.acc;
    b.ret(&[acc]).unwrap();
    (m, f)
}

struct Heap;

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
            _ => Err(InterpError::UnresolvedImport { name: name.into() }),
        }
    }
}

fn run(m: &Module, f: FuncId, x: i64) -> Result<ir_lang::interp::Outcome, InterpError> {
    Interpreter::new(m, Heap)?.call(f, &[Val::i64(x)])
}

fn check(seed: u64, x: i64) {
    let (m, f) = generate(seed);
    m.validate()
        .unwrap_or_else(|e| panic!("generator: {e}\n{m}"));
    let expect = run(&m, f, x);
    assert!(expect.is_ok(), "{expect:?}\n{m}");
    let mut opt = m.clone();
    Optimizer::new()
        .validate(true)
        .run(&mut opt)
        .unwrap_or_else(|e| panic!("{e}\n{m}"));
    opt.validate().unwrap();
    assert_eq!(run(&opt, f, x), expect, "\n{m}\n{opt}");
    for kind in PassKind::ALL {
        let mut one = m.clone();
        let mut budget = Budget::unlimited();
        let _ = opt_lang::run_pass(&mut one.edit(f).unwrap(), kind, &mut budget)
            .unwrap_or_else(|e| panic!("{kind}: {e}\n{m}"));
        one.validate()
            .unwrap_or_else(|e| panic!("{kind}: {e}\n{one}"));
        assert_eq!(run(&one, f, x), expect, "{kind}\n{m}\n{one}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn prop_gc_programs_stay_valid_and_equal(seed in any::<u64>(), x in any::<i64>()) {
        check(seed, x);
    }
}

#[test]
fn test_gc_programs_on_many_seeds() {
    for seed in 0..400u64 {
        check(
            seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) + 1,
            (seed as i64) - 200,
        );
    }
}
