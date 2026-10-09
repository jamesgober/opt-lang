//! Large functions of typical shapes, for the benchmarks and the scale tests.
//!
//! A "unit" is a small piece of code as a front end lowers it, repeated with
//! different constants: arithmetic on the parameters with a foldable constant
//! subexpression, a redundant recomputation, a dead value, a diamond whose arms
//! join through a block parameter, and every few units a counted loop with a
//! loop-invariant computation in its body. About 30 instructions per unit.

#![allow(dead_code, clippy::unwrap_used)]

use ir_lang::{CmpOp, FuncId, Linkage, Module, Overflow, Signature, Type};

/// One function `f(i64, i64) -> i64` of about `insts` instructions.
pub fn mixed(insts: usize) -> (Module, FuncId) {
    let mut m = Module::new("bench");
    let f = m
        .declare_function(
            "f",
            &Signature::new(&[Type::I64, Type::I64], &[Type::I64]),
            Linkage::Export,
        )
        .unwrap();
    let mut b = m.build(f).unwrap();
    let p0 = b.param(0).unwrap();
    let p1 = b.param(1).unwrap();
    let mut acc = p0;
    let mut k: i128 = 0;
    let mut emitted = 0usize;
    while emitted < insts {
        k += 1;
        // Constant subexpression and arithmetic.
        let c1 = b.iconst(Type::I64, k).unwrap();
        let c2 = b.iconst(Type::I64, 3).unwrap();
        let c = b.add(c1, c2, Overflow::Wrap).unwrap();
        let x = b.add(acc, c, Overflow::Wrap).unwrap();
        // The same computation again (value numbering).
        let c1b = b.iconst(Type::I64, k).unwrap();
        let c2b = b.iconst(Type::I64, 3).unwrap();
        let cb = b.add(c1b, c2b, Overflow::Wrap).unwrap();
        let xb = b.add(acc, cb, Overflow::Wrap).unwrap();
        let y = b.mul(x, xb, Overflow::Wrap).unwrap();
        // A dead value.
        let _dead = b
            .binary(ir_lang::BinaryOp::Xor, ir_lang::Policy::NONE, y, p1)
            .unwrap();
        // A diamond with a join parameter.
        let cond = b.compare(CmpOp::Lt, y, p1).unwrap();
        let t = b.create_block(&[]).unwrap();
        let e = b.create_block(&[]).unwrap();
        let j = b.create_block(&[Type::I64]).unwrap();
        b.branch(cond, t, &[], e, &[]).unwrap();
        b.switch_to(t).unwrap();
        let one = b.iconst(Type::I64, 1).unwrap();
        let v = b.sub(y, one, Overflow::Wrap).unwrap();
        b.jump(j, &[v]).unwrap();
        b.switch_to(e).unwrap();
        b.jump(j, &[y]).unwrap();
        b.switch_to(j).unwrap();
        let r = b.block_param(j, 0).unwrap();
        // A constant branch (folded away).
        let yes = b.bconst(k % 2 == 0).unwrap();
        let t2 = b.create_block(&[]).unwrap();
        let e2 = b.create_block(&[]).unwrap();
        let j2 = b.create_block(&[Type::I64]).unwrap();
        b.branch(yes, t2, &[], e2, &[]).unwrap();
        b.switch_to(t2).unwrap();
        b.jump(j2, &[r]).unwrap();
        b.switch_to(e2).unwrap();
        let neg = b.sub(p1, r, Overflow::Wrap).unwrap();
        b.jump(j2, &[neg]).unwrap();
        b.switch_to(j2).unwrap();
        acc = b.block_param(j2, 0).unwrap();
        emitted += 20;
        if k % 4 == 0 {
            // for i in 0..4 { acc += p0 * 7 + p1 }  (the product is invariant)
            let head = b.create_block(&[Type::U32, Type::I64]).unwrap();
            let body = b.create_block(&[]).unwrap();
            let exit = b.create_block(&[]).unwrap();
            let zero = b.iconst(Type::U32, 0).unwrap();
            b.jump(head, &[zero, acc]).unwrap();
            b.switch_to(head).unwrap();
            let i = b.block_param(head, 0).unwrap();
            let a = b.block_param(head, 1).unwrap();
            let four = b.iconst(Type::U32, 4).unwrap();
            let more = b.compare(CmpOp::Lt, i, four).unwrap();
            b.branch(more, body, &[], exit, &[]).unwrap();
            b.switch_to(body).unwrap();
            let seven = b.iconst(Type::I64, 7).unwrap();
            let inv = b.mul(p0, seven, Overflow::Wrap).unwrap();
            let inv2 = b.add(inv, p1, Overflow::Wrap).unwrap();
            let a2 = b.add(a, inv2, Overflow::Wrap).unwrap();
            let step = b.iconst(Type::U32, 1).unwrap();
            let i2 = b.add(i, step, Overflow::Wrap).unwrap();
            b.jump(head, &[i2, a2]).unwrap();
            b.switch_to(exit).unwrap();
            acc = a;
            emitted += 10;
        }
    }
    b.ret(&[acc]).unwrap();
    (m, f)
}
