//! The Tier-1 path: build a function, call `opt_lang::optimize`, print it
//! before and after.
//!
//! Run with `cargo run --example optimize`.

use ir_lang::{CmpOp, Linkage, Module, Overflow, Signature, Type};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // fn scale(x: i64) -> i64 {
    //     let k = 4 * 8;              // a constant expression
    //     let a = x * k;
    //     let b = x * k;              // the same value again
    //     let r = if k > 10 { a + b } else { a - b };   // a constant condition
    //     let mut s = r;
    //     for _ in 0..3 { s = s + x * 7 }               // x * 7 is loop-invariant
    //     s
    // }
    let mut m = Module::new("example");
    let f = m.declare_function(
        "scale",
        &Signature::new(&[Type::I64], &[Type::I64]),
        Linkage::Export,
    )?;
    let mut b = m.build(f)?;
    let x = b.param(0)?;
    let (four, eight) = (b.iconst(Type::I64, 4)?, b.iconst(Type::I64, 8)?);
    let k = b.mul(four, eight, Overflow::Wrap)?;
    let a = b.mul(x, k, Overflow::Wrap)?;
    let bb = b.mul(x, k, Overflow::Wrap)?;
    let ten = b.iconst(Type::I64, 10)?;
    let big = b.compare(CmpOp::Gt, k, ten)?;
    let (then_b, else_b) = (b.create_block(&[])?, b.create_block(&[])?);
    let join = b.create_block(&[Type::I64])?;
    b.branch(big, then_b, &[], else_b, &[])?;
    b.switch_to(then_b)?;
    let sum = b.add(a, bb, Overflow::Wrap)?;
    b.jump(join, &[sum])?;
    b.switch_to(else_b)?;
    let diff = b.sub(a, bb, Overflow::Wrap)?;
    b.jump(join, &[diff])?;
    b.switch_to(join)?;
    let r = b.block_param(join, 0)?;
    let head = b.create_block(&[Type::U32, Type::I64])?;
    let body = b.create_block(&[])?;
    let exit = b.create_block(&[])?;
    let zero = b.iconst(Type::U32, 0)?;
    b.jump(head, &[zero, r])?;
    b.switch_to(head)?;
    let (i, s) = (b.block_param(head, 0)?, b.block_param(head, 1)?);
    let three = b.iconst(Type::U32, 3)?;
    let more = b.compare(CmpOp::Lt, i, three)?;
    b.branch(more, body, &[], exit, &[])?;
    b.switch_to(body)?;
    let seven = b.iconst(Type::I64, 7)?;
    let inv = b.mul(x, seven, Overflow::Wrap)?;
    let s2 = b.add(s, inv, Overflow::Wrap)?;
    let one = b.iconst(Type::U32, 1)?;
    let i2 = b.add(i, one, Overflow::Wrap)?;
    b.jump(head, &[i2, s2])?;
    b.switch_to(exit)?;
    b.ret(&[s])?;

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
    m.validate()?;
    Ok(())
}
