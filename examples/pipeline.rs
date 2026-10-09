//! Tiers 2 and 3: a configured `Optimizer`, and single passes run by hand with
//! a budget.
//!
//! Run with `cargo run --example pipeline`.

use ir_lang::{
    BinaryOp, BlockArg, BlockCall, InstData, Linkage, Module, Overflow, Policy, Signature, Type,
};
use opt_lang::{Budget, Optimizer, PassKind};

fn build() -> Result<(Module, ir_lang::FuncId), Box<dyn std::error::Error>> {
    // fn f(x: i64) -> i64 { checked(x + 0) * 1 }, where `+` raises on overflow.
    let mut m = Module::new("example");
    let f = m.declare_function(
        "f",
        &Signature::new(&[Type::I64], &[Type::I64]),
        Linkage::Export,
    )?;
    let mut b = m.build(f)?;
    let x = b.param(0)?;
    let zero = b.iconst(Type::I64, 0)?;
    let ok = b.create_block(&[Type::I64])?;
    let err = b.create_block(&[Type::U32])?;
    b.check(
        InstData::Binary {
            op: BinaryOp::Add,
            policy: Policy::overflow(Overflow::Error),
            args: [x, zero],
        },
        BlockCall::with_args(ok, &[BlockArg::Result(0)]),
        BlockCall::with_args(err, &[BlockArg::ErrorCode]),
    )?;
    b.switch_to(err)?;
    b.trap(1)?;
    b.switch_to(ok)?;
    let y = b.block_param(ok, 0)?;
    let one = b.iconst(Type::I64, 1)?;
    let z = b.mul(y, one, Overflow::Trap)?;
    b.ret(&[z])?;
    Ok((m, f))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Tier 2: chosen passes, sweeps, budget, and validation between passes.
    let (mut m, f) = build()?;
    let stats = Optimizer::new()
        .passes(&[
            PassKind::Sccp,
            PassKind::Gvn,
            PassKind::Dce,
            PassKind::SimplifyCfg,
        ])
        .max_iterations(3)
        .budget(1 << 20)
        .validate(true)
        .run(&mut m)?;
    println!("{}", m.display_function(f));
    for p in stats.passes() {
        println!(
            "{:>12}: {} runs, {} changed",
            p.kind().name(),
            p.runs(),
            p.changes()
        );
    }

    // Tier 3: one pass at a time on a builder, drawing from one budget.
    let (mut m, f) = build()?;
    let mut budget = Budget::new(100_000);
    for pass in [PassKind::Gvn, PassKind::Dce] {
        let changed = opt_lang::run_pass(&mut m.edit(f)?, pass, &mut budget)?;
        println!(
            "{pass}: changed = {changed}, budget left = {}",
            budget.remaining()
        );
    }
    m.validate()?;
    Ok(())
}
