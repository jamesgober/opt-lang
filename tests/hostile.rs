//! Hostile shapes: very deep, very long, very wide functions, and tiny budgets.
//! Every pass must finish (iteratively, no stack overflow), leave valid IR, and
//! keep the program's behaviour.

mod common;

use ir_lang::interp::{self, Outcome, Val};
use ir_lang::{
    Block, BlockCall, CmpOp, FuncId, Linkage, Module, Overflow, Signature, SwitchCase, Type,
};
use opt_lang::{Optimizer, PassKind};
use proptest::prelude::*;

const DEPTH: usize = 40_000;

fn func(params: &[Type], returns: &[Type]) -> (Module, FuncId) {
    let mut m = Module::new("hostile");
    let f = m
        .declare_function("f", &Signature::new(params, returns), Linkage::Export)
        .unwrap();
    (m, f)
}

fn optimize_and_check(m: &mut Module, f: FuncId, args: &[Val]) -> opt_lang::Stats {
    let expect = interp::run(m, f, args).unwrap();
    // Validation after every pass would dominate the run time at this size;
    // validate the result once.
    let stats = Optimizer::new().validate(false).run(m).unwrap();
    m.validate().unwrap();
    assert_eq!(interp::run(m, f, args).unwrap(), expect);
    stats
}

#[test]
fn test_a_long_chain_of_blocks_is_merged() {
    let (mut m, f) = func(&[Type::I64], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let mut x = b.param(0).unwrap();
    for _ in 0..DEPTH {
        let next = b.create_block(&[Type::I64]).unwrap();
        let one = b.iconst(Type::I64, 1).unwrap();
        let y = b.add(x, one, Overflow::Wrap).unwrap();
        b.jump(next, &[y]).unwrap();
        b.switch_to(next).unwrap();
        x = b.block_param(next, 0).unwrap();
    }
    b.ret(&[x]).unwrap();
    let stats = optimize_and_check(&mut m, f, &[Val::i64(5)]);
    assert_eq!(stats.blocks_after(), 1);
}

#[test]
fn test_a_long_chain_of_empty_forwarders_is_threaded() {
    let (mut m, f) = func(&[Type::I64, Type::Bool], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let c = b.param(1).unwrap();
    let blocks: Vec<Block> = (0..DEPTH)
        .map(|_| b.create_block(&[Type::I64]).unwrap())
        .collect();
    let exit = b.create_block(&[Type::I64]).unwrap();
    b.branch(c, blocks[0], &[x], exit, &[x]).unwrap();
    for (i, &blk) in blocks.iter().enumerate() {
        b.switch_to(blk).unwrap();
        let p = b.block_param(blk, 0).unwrap();
        let next = blocks.get(i + 1).copied().unwrap_or(exit);
        b.jump(next, &[p]).unwrap();
    }
    b.switch_to(exit).unwrap();
    let r = b.block_param(exit, 0).unwrap();
    b.ret(&[r]).unwrap();
    let stats = optimize_and_check(&mut m, f, &[Val::i64(3), Val::bool(true)]);
    assert!(stats.blocks_after() <= 2, "{}", stats.blocks_after());
}

#[test]
fn test_a_cycle_of_empty_blocks_terminates() {
    let (mut m, f) = func(&[Type::Bool], &[]);
    let mut b = m.build(f).unwrap();
    let c = b.param(0).unwrap();
    let blocks: Vec<Block> = (0..1000).map(|_| b.create_block(&[]).unwrap()).collect();
    let exit = b.create_block(&[]).unwrap();
    b.branch(c, blocks[0], &[], exit, &[]).unwrap();
    for (i, &blk) in blocks.iter().enumerate() {
        b.switch_to(blk).unwrap();
        b.jump(blocks[(i + 1) % blocks.len()], &[]).unwrap();
    }
    b.switch_to(exit).unwrap();
    b.ret(&[]).unwrap();
    let _ = optimize_and_check(&mut m, f, &[Val::bool(false)]);
}

#[test]
fn test_deeply_nested_diamonds() {
    // if c0 { if c1 { ... } } with every join passing a value: a dominator tree
    // of depth ~DEPTH.
    let (mut m, f) = func(&[Type::I64], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let mut joins = Vec::new();
    let mut v = x;
    for k in 0..DEPTH / 4 {
        let lim = b.iconst(Type::I64, k as i128).unwrap();
        let c = b.compare(CmpOp::Gt, v, lim).unwrap();
        let t = b.create_block(&[]).unwrap();
        let join = b.create_block(&[Type::I64]).unwrap();
        b.branch(c, t, &[], join, &[v]).unwrap();
        joins.push((join, v));
        b.switch_to(t).unwrap();
        let one = b.iconst(Type::I64, 1).unwrap();
        v = b.add(v, one, Overflow::Wrap).unwrap();
    }
    for (join, _) in joins.into_iter().rev() {
        b.jump(join, &[v]).unwrap();
        b.switch_to(join).unwrap();
        v = b.block_param(join, 0).unwrap();
    }
    b.ret(&[v]).unwrap();
    let _ = optimize_and_check(&mut m, f, &[Val::i64(1_000_000)]);
}

#[test]
fn test_deeply_nested_loops_respect_the_budget() {
    // 300 nested loops, each with an invariant multiply in the innermost body:
    // LICM's work grows with depth x size, so a tight budget must cut it off
    // cleanly.
    let depth = 300;
    let build = || {
        let (mut m, f) = func(&[Type::I64], &[Type::I64]);
        let mut b = m.build(f).unwrap();
        let x = b.param(0).unwrap();
        let mut exits = Vec::new();
        let mut acc = x;
        for _ in 0..depth {
            let head = b.create_block(&[Type::U32, Type::I64]).unwrap();
            let body = b.create_block(&[]).unwrap();
            let exit = b.create_block(&[Type::I64]).unwrap();
            let zero = b.iconst(Type::U32, 0).unwrap();
            b.jump(head, &[zero, acc]).unwrap();
            b.switch_to(head).unwrap();
            let i = b.block_param(head, 0).unwrap();
            let a = b.block_param(head, 1).unwrap();
            let one = b.iconst(Type::U32, 1).unwrap();
            let more = b.compare(CmpOp::Lt, i, one).unwrap();
            b.branch(more, body, &[], exit, &[a]).unwrap();
            b.switch_to(body).unwrap();
            let next = b.add(i, one, Overflow::Wrap).unwrap();
            exits.push((head, next, exit));
            acc = a;
        }
        let k = b.iconst(Type::I64, 3).unwrap();
        let inv = b.mul(x, k, Overflow::Wrap).unwrap();
        let mut a = b.add(acc, inv, Overflow::Wrap).unwrap();
        for (head, next, exit) in exits.into_iter().rev() {
            b.jump(head, &[next, a]).unwrap();
            b.switch_to(exit).unwrap();
            a = b.block_param(exit, 0).unwrap();
        }
        b.ret(&[a]).unwrap();
        (m, f)
    };
    let (mut m, f) = build();
    let expect = interp::run(&m, f, &[Val::i64(2)]).unwrap();
    let stats = Optimizer::new()
        .passes(&[PassKind::Licm])
        .budget(20_000)
        .validate(true)
        .run(&mut m)
        .unwrap();
    assert_eq!(stats.budget_exhausted(), 1);
    m.validate().unwrap();
    assert_eq!(interp::run(&m, f, &[Val::i64(2)]).unwrap(), expect);
    // With the default budget it completes and hoists the multiply out of all.
    let (mut m, f) = build();
    let stats = Optimizer::new().validate(false).run(&mut m).unwrap();
    m.validate().unwrap();
    assert_eq!(stats.budget_exhausted(), 0);
    assert_eq!(interp::run(&m, f, &[Val::i64(2)]).unwrap(), expect);
}

#[test]
fn test_a_huge_switch() {
    let (mut m, f) = func(&[Type::U32], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let join = b.create_block(&[Type::I64]).unwrap();
    let other = b.create_block(&[]).unwrap();
    let n = 20_000u64;
    let mut cases = Vec::new();
    let mut targets = Vec::new();
    for k in 0..n {
        let blk = b.create_block(&[]).unwrap();
        cases.push(SwitchCase {
            value: k,
            dest: BlockCall::new(if k % 2 == 0 { blk } else { other }, &[]),
        });
        targets.push(blk);
    }
    b.switch(x, cases, BlockCall::new(other, &[])).unwrap();
    for (k, &blk) in targets.iter().enumerate() {
        b.switch_to(blk).unwrap();
        let v = b.iconst(Type::I64, (k % 7) as i128).unwrap();
        b.jump(join, &[v]).unwrap();
    }
    b.switch_to(other).unwrap();
    let v = b.iconst(Type::I64, -1).unwrap();
    b.jump(join, &[v]).unwrap();
    b.switch_to(join).unwrap();
    let r = b.block_param(join, 0).unwrap();
    b.ret(&[r]).unwrap();
    let _ = optimize_and_check(&mut m, f, &[Val::u32(4)]);
    let _ = interp::run(&m, f, &[Val::u32(5)]).unwrap();
}

#[test]
fn test_thousands_of_dead_parameters() {
    let (mut m, f) = func(&[Type::I64], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let width = 3000;
    let mid = b.create_block(&vec![Type::I64; width]).unwrap();
    b.jump(mid, &vec![x; width]).unwrap();
    b.switch_to(mid).unwrap();
    let p = b.block_param(mid, width - 1).unwrap();
    b.ret(&[p]).unwrap();
    let stats = optimize_and_check(&mut m, f, &[Val::i64(9)]);
    assert_eq!(stats.blocks_after(), 1);
}

#[test]
fn test_a_wide_join() {
    // Many predecessors into one join with parameters: copy propagation and
    // DCE must stay linear in the edges.
    let (mut m, f) = func(&[Type::U32, Type::I64], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    let y = b.param(1).unwrap();
    let join = b.create_block(&[Type::I64, Type::I64, Type::I64]).unwrap();
    let n = 20_000u64;
    let mut cases = Vec::new();
    let mut blocks = Vec::new();
    for k in 0..n {
        let blk = b.create_block(&[]).unwrap();
        cases.push(SwitchCase {
            value: k,
            dest: BlockCall::new(blk, &[]),
        });
        blocks.push(blk);
    }
    b.switch(x, cases, BlockCall::new(join, &[y, y, y]))
        .unwrap();
    for (k, &blk) in blocks.iter().enumerate() {
        b.switch_to(blk).unwrap();
        let v = b.iconst(Type::I64, k as i128).unwrap();
        b.jump(join, &[y, v, y]).unwrap();
    }
    b.switch_to(join).unwrap();
    let a = b.block_param(join, 0).unwrap();
    let c = b.block_param(join, 1).unwrap();
    let s = b.add(a, c, Overflow::Wrap).unwrap();
    b.ret(&[s]).unwrap();
    let _ = optimize_and_check(&mut m, f, &[Val::u32(77), Val::i64(1)]);
}

#[test]
fn test_zero_budget_changes_nothing() {
    let p = common::generate(42);
    let mut m = p.module.clone();
    let before = m.to_string();
    let stats = Optimizer::new().budget(0).run(&mut m).unwrap();
    assert_eq!(m.to_string(), before);
    assert_eq!(stats.budget_exhausted(), stats.functions());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Any budget leaves valid IR with the same behaviour.
    #[test]
    fn prop_any_budget_is_safe(seed in any::<u64>(), budget in 0u64..20_000, a in any::<i64>(), b in any::<i64>()) {
        let p = common::generate(seed);
        let mut m = p.module.clone();
        let _ = Optimizer::new().budget(budget).validate(true).run(&mut m).unwrap();
        m.validate().unwrap();
        let before = common::observe(&p.module, p.entry, &p.globals, a, b);
        let after = common::observe(&m, p.entry, &p.globals, a, b);
        prop_assume!(!before.limited());
        prop_assert!(before.same(&after), "{before:?}\n{after:?}");
    }
}

#[test]
fn test_outcome_is_plain_return_for_reference() {
    // Sanity check of the harness itself.
    let (mut m, f) = func(&[Type::I64], &[Type::I64]);
    let mut b = m.build(f).unwrap();
    let x = b.param(0).unwrap();
    b.ret(&[x]).unwrap();
    assert_eq!(
        interp::run(&m, f, &[Val::i64(1)]).unwrap(),
        Outcome::Return(vec![Val::i64(1)])
    );
}
