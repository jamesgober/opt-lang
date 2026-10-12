//! Optimizing code lowered the way irgen-lang lowers it: mutable locals
//! through ir-lang's SSA construction, an OPS v2 `pow` in a `check`, and a GC
//! reference kept across a call, with statepoints placed by ir-lang. Then one
//! call to `opt_lang::optimize`.
//!
//! The source, in a toy language:
//!
//! ```text
//! fn area(shape: ref, side: i64) -> i64 {
//!     let mut total = 0;
//!     let mut i = 0;
//!     while i < 3 {
//!         total = total + side ** 2;   // signed `pow`: always a `check`
//!         poll();                      // a safepoint: `shape` must survive it
//!         i = i + 1;
//!     }
//!     total + shape.field0
//! }
//! ```
//!
//! Run with `cargo run --example variables`.

use ir_lang::{
    BinaryOp, BlockArg, BlockCall, Call, CmpOp, ConvOp, InstData, Linkage, MemFlags, Module,
    Overflow, Policy, Signature, Type,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut m = Module::new("variables");
    let poll = m.declare_function("poll", &Signature::new(&[], &[]), Linkage::Import)?;
    let f = m.declare_function(
        "area",
        &Signature::new(&[Type::Ref, Type::I64], &[Type::I64]),
        Linkage::Export,
    )?;
    let mut b = m.build(f)?;
    let shape = b.declare_var(Type::Ref)?;
    let total = b.declare_var(Type::I64)?;
    let i = b.declare_var(Type::I64)?;
    let (s, side) = (b.param(0)?, b.param(1)?);
    b.def_var(shape, s)?;
    let zero = b.iconst(Type::I64, 0)?;
    b.def_var(total, zero)?;
    b.def_var(i, zero)?;

    let (head, body, exit) = (
        b.create_block(&[])?,
        b.create_block(&[])?,
        b.create_block(&[])?,
    );
    b.jump(head, &[])?;
    b.switch_to(head)?;
    let iv = b.use_var(i)?;
    let three = b.iconst(Type::I64, 3)?;
    let more = b.compare(CmpOp::Lt, iv, three)?;
    b.branch(more, body, &[], exit, &[])?;

    b.switch_to(body)?;
    b.seal_block(body)?;
    // side ** 2, checked: a negative exponent would raise E0006.
    let two = b.iconst(Type::I64, 2)?;
    let (ok, err) = (b.create_block(&[Type::I64])?, b.create_block(&[Type::U32])?);
    b.check(
        InstData::Binary {
            op: BinaryOp::Pow,
            policy: Policy::overflow(Overflow::Wrap),
            args: [side, two],
        },
        BlockCall::with_args(ok, &[BlockArg::Result(0)]),
        BlockCall::with_args(err, &[BlockArg::ErrorCode]),
    )?;
    b.seal_block(ok)?;
    b.seal_block(err)?;
    b.switch_to(err)?;
    b.trap(6)?;
    b.switch_to(ok)?;
    let sq = b.block_param(ok, 0)?;
    let t = b.use_var(total)?;
    let t2 = b.add(t, sq, Overflow::Wrap)?;
    b.def_var(total, t2)?;
    b.call(Call::direct(poll, &[]))?;
    let iv = b.use_var(i)?;
    let one = b.iconst(Type::I64, 1)?;
    let i2 = b.add(iv, one, Overflow::Wrap)?;
    b.def_var(i, i2)?;
    b.jump(head, &[])?;
    b.seal_block(head)?;

    b.switch_to(exit)?;
    b.seal_block(exit)?;
    let r = b.use_var(shape)?;
    let p = b.convert(ConvOp::RefToPtr, Policy::NONE, r, Type::Ptr)?;
    let field = b.load(
        Type::I64,
        p,
        MemFlags {
            align: 8,
            volatile: false,
        },
    )?;
    let t = b.use_var(total)?;
    let sum = b.add(t, field, Overflow::Wrap)?;
    b.ret(&[sum])?;
    b.seal_all_blocks()?;
    let sp = b.insert_statepoints()?;
    println!("statepoints: {} relocation(s)", sp.relocations);

    println!("before:\n{}", m.display_function(f));
    let stats = opt_lang::optimize(&mut m)?;
    println!("after:\n{}", m.display_function(f));
    println!(
        "instructions {} -> {}, blocks {} -> {}",
        stats.insts_before(),
        stats.insts_after(),
        stats.blocks_before(),
        stats.blocks_after()
    );
    // The result is valid, safepoint rules included.
    m.validate()?;
    Ok(())
}
