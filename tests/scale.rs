//! Scale tests at 100k+ instructions: the documented reduction on the typical
//! shape holds, the behaviour is unchanged, and the work charged to the budget
//! stays within a fixed number of steps per unit of function size.

#[path = "../benches/shapes/mod.rs"]
mod shapes;

use ir_lang::interp::{self, Val};
use opt_lang::Optimizer;

fn units(m: &ir_lang::Module, f: ir_lang::FuncId) -> u64 {
    let func = m.function(f).unwrap();
    (func.inst_count() + func.block_count() + func.value_count()) as u64
}

#[test]
fn test_mixed_shape_reduction_at_100k() {
    let (m, f) = shapes::mixed(100_000);
    let mut opt = m.clone();
    let stats = Optimizer::new().validate(false).run(&mut opt).unwrap();
    opt.validate().unwrap();
    // The figures quoted in the README (instructions 76,674 -> 27,787, blocks
    // 30,004 -> 11,114).
    assert_eq!(stats.insts_before(), 76_674);
    assert_eq!(stats.insts_after(), 27_787);
    assert_eq!(stats.blocks_before(), 30_004);
    assert_eq!(stats.blocks_after(), 11_114);
    assert_eq!(stats.converged(), 1);
    for (a, b) in [(3, 4), (-100, 7), (i64::MAX, i64::MIN)] {
        let args = [Val::i64(a), Val::i64(b)];
        assert_eq!(
            interp::run(&m, f, &args).unwrap(),
            interp::run(&opt, f, &args).unwrap()
        );
    }
}

#[test]
fn test_charged_work_is_linear() {
    // The whole default pipeline (every sweep, every pass) fits in 160 steps
    // per unit of size at 100k and at 200k instructions alike.
    for n in [100_000, 200_000] {
        let (mut m, f) = shapes::mixed(n);
        let budget = 160 * units(&m, f);
        let stats = Optimizer::new()
            .budget(budget)
            .validate(false)
            .run(&mut m)
            .unwrap();
        assert_eq!(stats.budget_exhausted(), 0, "n = {n}");
        assert_eq!(stats.converged(), 1, "n = {n}");
    }
}
