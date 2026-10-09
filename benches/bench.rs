//! Criterion benchmarks: throughput of each pass and of the whole pipeline on
//! functions of 100k and 1M instructions, plus the instruction-count reduction
//! on the typical shape (printed once per size, to stderr).
//!
//! The shape (`shapes::mixed`) is what a front end lowers ordinary code into:
//! arithmetic with constant subexpressions, recomputed values, dead values,
//! diamonds joined by block parameters, constant branches, and counted loops
//! with invariant bodies. Each measured iteration optimizes a fresh clone of the
//! module (the clone is not timed).

#![allow(clippy::unwrap_used)]

mod shapes;

use std::hint::black_box;
use std::time::Duration;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use opt_lang::{Budget, Optimizer, PassKind};

const SIZES: [usize; 2] = [100_000, 1_000_000];

/// Live instructions of the module's functions (an empty pipeline measures
/// without changing anything).
fn insts(m: &ir_lang::Module) -> u64 {
    Optimizer::new()
        .passes(&[])
        .run(&mut m.clone())
        .unwrap()
        .insts_before() as u64
}

fn report_reduction() {
    for &n in &SIZES {
        let (mut m, _) = shapes::mixed(n);
        let stats = Optimizer::new().validate(false).run(&mut m).unwrap();
        eprintln!(
            "mixed {n}: instructions {} -> {} ({:.1}% removed), blocks {} -> {} ({:.1}% removed), {} sweeps",
            stats.insts_before(),
            stats.insts_after(),
            100.0 * (1.0 - stats.insts_after() as f64 / stats.insts_before() as f64),
            stats.blocks_before(),
            stats.blocks_after(),
            100.0 * (1.0 - stats.blocks_after() as f64 / stats.blocks_before() as f64),
            stats.iterations(),
        );
    }
}

fn bench_pipeline(c: &mut Criterion) {
    report_reduction();
    let mut group = c.benchmark_group("pipeline");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));
    for &n in &SIZES {
        let (m, _) = shapes::mixed(n);
        group.throughput(Throughput::Elements(insts(&m)));
        group.bench_function(format!("optimize/{n}"), |b| {
            b.iter_batched(
                || m.clone(),
                |mut m| {
                    black_box(Optimizer::new().validate(false).run(&mut m).unwrap());
                    m
                },
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

fn bench_passes(c: &mut Criterion) {
    let mut group = c.benchmark_group("pass");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(10));
    for &n in &SIZES {
        let (m, f) = shapes::mixed(n);
        group.throughput(Throughput::Elements(insts(&m)));
        for kind in PassKind::ALL {
            group.bench_function(format!("{}/{n}", kind.name()), |b| {
                b.iter_batched(
                    || m.clone(),
                    |mut m| {
                        // One run of one pass on the unoptimized function. The
                        // optimizer validates its input once, as every caller pays.
                        let stats = Optimizer::new()
                            .passes(&[kind])
                            .max_iterations(1)
                            .validate(false)
                            .compact(false)
                            .run_function(&mut m, f)
                            .unwrap();
                        black_box(stats);
                        m
                    },
                    BatchSize::LargeInput,
                );
            });
        }
    }
    group.finish();
}

fn bench_validation_overhead(c: &mut Criterion) {
    // The cost of `run_pass`, which validates before and (in debug builds)
    // after the pass.
    let mut group = c.benchmark_group("run_pass");
    group.sample_size(10);
    let (m, f) = shapes::mixed(100_000);
    group.bench_function("sccp/100000", |b| {
        b.iter_batched(
            || m.clone(),
            |mut m| {
                let mut budget = Budget::unlimited();
                black_box(
                    opt_lang::run_pass(&mut m.edit(f).unwrap(), PassKind::Sccp, &mut budget)
                        .unwrap(),
                );
                m
            },
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_pipeline,
    bench_passes,
    bench_validation_overhead
);
criterion_main!(benches);
