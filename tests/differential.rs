//! Differential tests: random programs are run in the ir-lang reference
//! interpreter before and after optimization (the whole pipeline, each pass
//! alone, and random pass sequences). Results, trap codes, `check` error codes,
//! exceptions, import calls (with their arguments, in order), and final global
//! memory must be identical, and the optimized IR must validate.

mod common;

use common::{Observation, Program, generate, generate_sized, observe};
use ir_lang::Module;
use opt_lang::{Budget, Optimizer, PassKind};
use proptest::prelude::*;

const ARGS: [(i64, i64); 6] = [
    (0, 0),
    (1, -1),
    (7, 3),
    (-8, 5),
    (i64::MAX, i64::MIN),
    (255, 10),
];

fn run_all(m: &Module, p: &Program, args: &[(i64, i64)]) -> Vec<Observation> {
    args.iter()
        .map(|&(a, b)| observe(m, p.entry, &p.globals, a, b))
        .collect()
}

/// Checks that `optimized` behaves exactly as `p.module` on `args`. Returns
/// `false` (skips) when the original run hit a resource limit.
fn assert_same(p: &Program, optimized: &Module, args: &[(i64, i64)], what: &str) {
    let before = run_all(&p.module, p, args);
    let after = run_all(optimized, p, args);
    for ((b, a), &(x, y)) in before.iter().zip(&after).zip(args) {
        if b.limited() {
            continue;
        }
        assert!(
            b.outcome.is_ok(),
            "the generator made a program with undefined behaviour: {:?}\n{}",
            b.outcome,
            p.module
        );
        assert!(
            b.same(a),
            "{what}: args ({x}, {y})\nbefore: {b:?}\nafter: {a:?}\n--- original ---\n{}\n--- optimized ---\n{}",
            p.module,
            optimized
        );
    }
}

fn check_pipeline(seed: u64, size: u32, args: &[(i64, i64)]) {
    let p = generate_sized(seed, size);
    p.module.validate().unwrap();
    let mut m = p.module.clone();
    let stats = Optimizer::new().validate(true).run(&mut m).unwrap();
    m.validate().unwrap();
    assert!(stats.insts_after() <= stats.insts_before() + stats.blocks_before());
    assert_same(&p, &m, args, "pipeline");
    // The pipeline is idempotent: a second run finds nothing to do.
    let text = m.to_string();
    let again = Optimizer::new().validate(true).run(&mut m).unwrap();
    assert_eq!(again.insts_before(), again.insts_after());
    assert_eq!(m.to_string(), text, "second run changed the module");
}

fn check_each_pass(seed: u64, args: &[(i64, i64)]) {
    let p = generate(seed);
    for kind in PassKind::ALL {
        let mut m = p.module.clone();
        for f in p.module.functions() {
            if p.module.function(f).is_none() {
                continue;
            }
            let mut budget = Budget::unlimited();
            let _ = opt_lang::run_pass(&mut m.edit(f).unwrap(), kind, &mut budget).unwrap();
            m.validate_function(f)
                .unwrap_or_else(|e| panic!("{kind} left invalid IR: {e}\n{m}"));
            // Idempotent: running it again changes nothing.
            let again = opt_lang::run_pass(&mut m.edit(f).unwrap(), kind, &mut budget).unwrap();
            assert!(!again, "{kind} is not idempotent on seed {seed}\n{m}");
        }
        assert_same(&p, &m, args, kind.name());
    }
}

fn check_sequence(seed: u64, seq: &[u8], args: &[(i64, i64)]) {
    let p = generate(seed);
    let passes: Vec<PassKind> = seq
        .iter()
        .map(|&k| PassKind::ALL[k as usize % PassKind::ALL.len()])
        .collect();
    let mut m = p.module.clone();
    Optimizer::new()
        .passes(&passes)
        .max_iterations(2)
        .validate(true)
        .compact(seq.first().is_some_and(|k| k % 2 == 0))
        .run(&mut m)
        .unwrap();
    m.validate().unwrap();
    assert_same(&p, &m, args, "sequence");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(768))]

    #[test]
    fn prop_pipeline_preserves_semantics(seed in any::<u64>(), a in any::<i64>(), b in any::<i64>()) {
        check_pipeline(seed, 70, &[(a, b), (a, 0), (b % 17, a % 5)]);
    }

    #[test]
    fn prop_each_pass_preserves_semantics(seed in any::<u64>(), a in any::<i64>(), b in any::<i64>()) {
        check_each_pass(seed, &[(a, b), (b, a % 9)]);
    }

    #[test]
    fn prop_pass_sequences_preserve_semantics(
        seed in any::<u64>(),
        seq in proptest::collection::vec(any::<u8>(), 1..8),
        a in any::<i64>(),
        b in any::<i64>(),
    ) {
        check_sequence(seed, &seq, &[(a, b), (a % 11, b % 7)]);
    }
}

#[test]
fn test_pipeline_on_many_seeds_with_edge_arguments() {
    for seed in 0..300u64 {
        check_pipeline(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15), 70, &ARGS);
    }
}

#[test]
fn test_each_pass_on_many_seeds() {
    for seed in 0..120u64 {
        check_each_pass(seed.wrapping_mul(0xD1B5_4A32_D192_ED03) ^ 7, &ARGS[..3]);
    }
}

#[test]
fn test_large_programs() {
    for seed in 0..12u64 {
        check_pipeline(seed ^ 0xABCD, 400, &ARGS[..3]);
    }
}

#[test]
fn test_optimization_actually_happens() {
    // Across many programs, the pipeline removes a real share of the code, and
    // every pass contributes somewhere.
    let mut before = 0;
    let mut after = 0;
    let mut changed = [0u64; 6];
    for seed in 0..200u64 {
        let p = generate(seed.wrapping_mul(31) + 5);
        let mut m = p.module.clone();
        let stats = Optimizer::new().validate(true).run(&mut m).unwrap();
        before += stats.insts_before();
        after += stats.insts_after();
        for (k, kind) in PassKind::ALL.into_iter().enumerate() {
            changed[k] += stats.pass(kind).changes();
        }
    }
    assert!(
        after * 100 < before * 85,
        "only {after} of {before} removed"
    );
    for (k, kind) in PassKind::ALL.into_iter().enumerate() {
        assert!(changed[k] > 0, "{kind} never changed anything");
    }
}
