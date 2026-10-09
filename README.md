<h1 align="center">
    <img width="99" alt="Rust logo" src="https://raw.githubusercontent.com/jamesgober/rust-collection/72baabd71f00e14aa9184efcb16fa3deddda3a0a/assets/rust-logo.svg">
    <br>
    <b>opt-lang</b>
    <br>
    <sub><sup>SSA OPTIMIZER</sup></sub>
</h1>

<div align="center">
    <a href="https://crates.io/crates/opt-lang"><img alt="Crates.io" src="https://img.shields.io/crates/v/opt-lang"></a>
    <a href="https://crates.io/crates/opt-lang"><img alt="Downloads" src="https://img.shields.io/crates/d/opt-lang?color=%230099ff"></a>
    <a href="https://docs.rs/opt-lang"><img alt="docs.rs" src="https://img.shields.io/docsrs/opt-lang"></a>
    <a href="https://github.com/jamesgober/opt-lang/actions"><img alt="CI" src="https://github.com/jamesgober/opt-lang/actions/workflows/ci.yml/badge.svg"></a>
    <a href="https://github.com/rust-lang/rfcs/blob/master/text/2495-min-rust-version.md"><img alt="MSRV" src="https://img.shields.io/badge/MSRV-1.85%2B-blue"></a>
</div>

<br>

<div align="left">
    <p>
        <strong>opt-lang</strong> makes <a href="https://crates.io/crates/ir-lang"><code>ir-lang</code></a> 2.0 programs smaller and faster without changing what they compute: sparse conditional constant propagation, global value numbering, dead-code elimination, CFG simplification, copy propagation, and loop-invariant code motion, run as a pipeline to a fixpoint with the IR validator between passes.
    </p>
    <p>
        It is the IR-to-IR stage of the <code>-lang</code> family's native compiler path, between a front end's lowering and instruction selection. Constant folding follows the shared operation semantics (<code>specs/OPS.md</code>) exactly, policy by policy: an operation whose <code>error</code> or <code>trap</code> policy would fire at run time is never folded into a value. Every pass is iterative and draws from a work budget, so no input can make it recurse deeply or run away.
    </p>
    <br>
    <hr>
    <p>
        <strong>MSRV is 1.85+</strong> (Rust 2024 edition). <code>no_std</code>-compatible (needs only <code>alloc</code>), <code>#![forbid(unsafe_code)]</code>, two dependencies, both from the family: <a href="https://crates.io/crates/ir-lang"><code>ir-lang</code></a> (pinned to <code>=2.0.0-alpha.1</code>) and <a href="https://crates.io/crates/pass-lang"><code>pass-lang</code></a>.
    </p>
    <blockquote>
        <strong>Status: pre-1.0 (0.2.0, the foundation).</strong> The public API is designed across the 0.x series and frozen at <code>1.0.0</code>, after a real backend consumes optimized IR. See <a href="./dev/ROADMAP.md"><code>dev/ROADMAP.md</code></a> and <a href="./CHANGELOG.md"><code>CHANGELOG.md</code></a>.
    </blockquote>
</div>

<hr>
<br>

## The model

One call optimizes a module; everything else is for callers who want control:

- **[`optimize`](./docs/API.md#optimize)** runs the default pipeline on every function with a body (Tier 1).
- **[`Optimizer`](./docs/API.md#optimizer)** chooses the passes and their order, the number of sweeps, the work budget, validation between passes, and compaction (Tier 2).
- **[`run_pass`](./docs/API.md#run_pass)** runs one [`PassKind`](./docs/API.md#passkind) on an `ir_lang::Builder` with a [`Budget`](./docs/API.md#budget), for callers with their own pipeline (Tier 3).
- **[`Stats`](./docs/API.md#stats)** reports sizes before and after, sweeps, budget exhaustion, and per-pass counts; **[`OptError`](./docs/API.md#opterror)** says why optimization stopped.

The passes:

| Pass | What it does |
|---|---|
| `SimplifyCfg` | Folds branches on constants and branches with identical edges, prunes switch cases, removes unreachable blocks, threads jumps through empty blocks, merges straight-line blocks. |
| `Sccp` | Sparse conditional constant propagation over block parameters and the edges that can be taken, including `switch` and `check` edges; folds a `check` to its normal edge, its error edge (with the OPS code), or a `trap`; turns a `check` that cannot fail into the plain operation. |
| `CopyProp` | Replaces a block parameter that receives the same value on every edge (loops included) and removes it. |
| `Gvn` | Dominator-based value numbering of pure operations, with commutative operands canonicalized and a few exact integer identities (`x + 0`, `x * 1`, `not(not(x))`, ...). |
| `Licm` | Hoists pure loop-invariant operations into the loop's preheader, creating one when needed, inner loops first. |
| `Dce` | Removes dead instructions and dead block parameters (dead loop variables included), keeping every side effect. |

<br>

What it guarantees, and how each guarantee is checked:

| Guarantee | How it is held |
|---|---|
| Optimized code behaves exactly like the original: same return values, same trap codes, same `check` error codes, same exceptions, the same import calls with the same arguments in the same order, and the same final memory. | Differential tests generate random SSA programs (loops, `switch`, calls, `invoke` and landing pads, `resume`, checked arithmetic under every policy, floats including NaN, stack and global memory, volatile accesses, atomics, `memcpy`/`memset`) and run them before and after optimization in the ir-lang reference interpreter: the whole pipeline, each pass alone, and random pass sequences. |
| Constant folding is exact, and never folds an operation that would raise into a value. | Every operation, type, and policy is folded and compared with the interpreter's `eval_*` functions over the OPS edge values and random bits; float rounding and square root are implemented in `core` and checked bit for bit against `std`. |
| The IR stays valid, including the GC safepoint rules. | The ir-lang validator runs after every pass in debug builds and in every test. Random programs that carry GC references through safepoints, branches, and loops are optimized, validated, and run. |
| Every pass is idempotent, and the pipeline reaches its fixpoint. | A second run of each pass, and of the pipeline, changes nothing, on every generated program. |
| No input makes a pass recurse or run away. | Every algorithm is iterative; 40,000-deep block chains, 10,000-deep dominator trees, 300-deep loop nests, 20,000-case switches, and 3,000-parameter blocks are optimized in the tests, and any budget (zero included) leaves valid IR with unchanged behaviour. |
| Work is linear in the function. | Each pass is linear by construction (the dominator tree is `O(E log V)`); the whole pipeline on a function of 100k or of 200k instructions fits in 160 budget steps per unit of size (a scale test). |

<hr>
<br>

## Installation

```toml
[dependencies]
opt-lang = "0.2"
ir-lang  = "=2.0.0-alpha.1"
```

Without the standard library (optimization results are identical):

```toml
[dependencies]
opt-lang = { version = "0.2", default-features = false }
```

<hr>
<br>

## Quick start

```rust
use ir_lang::{Linkage, Module, Overflow, Signature, Type};

// fn f(x: i64) -> i64 { let a = 2 + 3; (x * a) + (x * a) }
let mut m = Module::new("demo");
let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let x = b.param(0)?;
let (two, three) = (b.iconst(Type::I64, 2)?, b.iconst(Type::I64, 3)?);
let a = b.add(two, three, Overflow::Wrap)?;
let p = b.mul(x, a, Overflow::Wrap)?;
let q = b.mul(x, a, Overflow::Wrap)?;
let r = b.add(p, q, Overflow::Wrap)?;
b.ret(&[r])?;

let stats = opt_lang::optimize(&mut m)?;
assert_eq!((stats.insts_before(), stats.insts_after()), (6, 3));
let text = m.display_function(f).to_string();
assert!(text.contains("const 5"));
assert!(text.contains("mul<overflow=wrap> v0, v1"));
assert!(text.contains("add<overflow=wrap> v2, v2"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

### Policies decide what may be folded

A `check` holds an operation whose policy can raise. With constant operands it
folds to exactly what would happen at run time:

```rust
use ir_lang::{BinaryOp, BlockArg, BlockCall, InstData, Linkage, Module, Overflow, Policy, Signature, Type};

// i64::MAX + 1 with overflow=error: the error edge, with code 1 (E0001).
let mut m = Module::new("demo");
let f = m.declare_function("f", &Signature::new(&[], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let max = b.iconst(Type::I64, i128::from(i64::MAX))?;
let one = b.iconst(Type::I64, 1)?;
let ok = b.create_block(&[Type::I64])?;
let err = b.create_block(&[Type::U32])?;
b.check(
    InstData::Binary { op: BinaryOp::Add, policy: Policy::overflow(Overflow::Error), args: [max, one] },
    BlockCall::with_args(ok, &[BlockArg::Result(0)]),
    BlockCall::with_args(err, &[BlockArg::ErrorCode]),
)?;
b.switch_to(ok)?;
let sum = b.block_param(ok, 0)?;
b.ret(&[sum])?;
b.switch_to(err)?;
let code = b.block_param(err, 0)?;
let wide = b.convert(ir_lang::ConvOp::Zext, Policy::NONE, code, Type::I64)?;
b.ret(&[wide])?;

opt_lang::optimize(&mut m)?;
let text = m.display_function(f).to_string();
assert!(!text.contains("check"));
assert!(text.contains("const 1\n    ret"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

The same addition with `overflow=trap` stays an addition (it traps at run
time); with `overflow=wrap` it folds to `i64::MIN`.

### Choosing the passes

```rust
use ir_lang::{Linkage, Module, Overflow, Signature, Type};
use opt_lang::{Budget, Optimizer, PassKind};

let mut m = Module::new("demo");
let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let x = b.param(0)?;
let y = b.add(x, x, Overflow::Wrap)?;
let z = b.add(x, x, Overflow::Wrap)?;
let w = b.mul(y, z, Overflow::Wrap)?;
b.ret(&[w])?;

// Tier 2: value numbering and dead code only, at most two sweeps, a fixed
// budget, and the validator after every pass.
let stats = Optimizer::new()
    .passes(&[PassKind::Gvn, PassKind::Dce])
    .max_iterations(2)
    .budget(1 << 20)
    .validate(true)
    .run(&mut m)?;
assert_eq!(stats.insts_after(), 2);
assert_eq!(stats.pass(PassKind::Gvn).changes(), 1);

// Tier 3: one pass on a builder.
let mut budget = Budget::unlimited();
assert!(!opt_lang::run_pass(&mut m.edit(f)?, PassKind::Gvn, &mut budget)?);
# Ok::<(), Box<dyn std::error::Error>>(())
```

<hr>
<br>

## Examples

Runnable programs in [`examples/`](./examples):

| Example | What it shows |
|---|---|
| [`optimize`](./examples/optimize.rs) | The one-call path on a function with a constant expression, a recomputed value, a constant branch, and a loop-invariant product; prints the IR before and after. `cargo run --example optimize` |
| [`pipeline`](./examples/pipeline.rs) | A configured `Optimizer` with per-pass counts, and single passes run by hand from one budget. `cargo run --example pipeline` |

<hr>
<br>

## Performance

Every pass is a constant number of linear walks over the function (plus the
`O(E log V)` dominator tree), so time grows linearly with size; the cost per
instruction rises once the function no longer fits in cache (about 1.6x for
the pipeline between 100k and 1M instructions). Measured with the benchmarks
in [`benches/`](./benches) on functions of the typical shape (see below),
x86_64, Rust 1.95 stable, release profile, Windows 11, on a machine also
running other builds; each figure is one run of one pass, or the whole
pipeline to its fixpoint, on the unoptimized function. Library-only figures:
building the IR is not included.

| Benchmark | 100k instructions (76,674 live) | 1M instructions (766,674 live) |
|---|---:|---:|
| `pipeline/optimize` (all passes, to the fixpoint: 3 sweeps) | ~69 ms (1.1 M inst/s) | ~1.12 s (0.69 M inst/s) |
| `pass/simplify-cfg` | ~16 ms | ~254 ms |
| `pass/sccp` | ~16 ms | ~215 ms |
| `pass/copy-prop` | ~6.4 ms | ~102 ms |
| `pass/gvn` | ~11 ms | ~169 ms |
| `pass/licm` | ~7.7 ms | ~128 ms |
| `pass/dce` | ~5.6 ms | ~119 ms |

Every figure includes the input validation each optimizer run performs (about
4 ms at 100k and 60 ms at 1M instructions). The pipeline compacts a function
between passes once most of its arena is tombstones, which keeps later sweeps
on dense tables.

The typical shape is what a front end lowers ordinary code into: arithmetic
with a constant subexpression, the same value computed twice, a dead value, a
diamond joined by a block parameter, a branch on a constant, and every fourth
unit a counted loop with an invariant product. On it the pipeline removes
**63.8% of the instructions** (76,674 to 27,787 at 100k; 766,674 to 277,787 at
1M) and **63.0% of the blocks** (30,004 to 11,114), in three sweeps. Those are
the numbers for that shape only; real code has less redundancy.

```bash
cargo bench --bench bench
```

Criterion writes per-benchmark reports to `target/criterion/`; the reduction
figures are printed to stderr. Numbers vary by CPU; use the trend across runs,
not a single absolute.

<hr>
<br>

## Design notes

- **Analysis first, then rewrite.** Each pass computes everything it will do
  before it changes the function, and the IR is rewritten only through the
  ir-lang `Builder`, which type-checks every insertion. A pass that cannot be
  paid for from the budget changes nothing.
- **Bulk edits in linear time.** The builder has no "move instruction" and its
  `remove_block_param` scans every block, so the passes move an instruction by
  re-inserting a copy and forwarding its results, and remove many block
  parameters at once by rebuilding the affected blocks and retargeting their
  edges in one pass.
- **GC references are never moved.** A `ref`, or a value derived from one, is
  never made a constant, value-numbered, or hoisted: moving it across a
  safepoint would break the IR's statepoint rules. Everything else is fair game.
- **Folding without `std`.** `core` lacks `floor`, `round`, `sqrt`, and their
  kin on the MSRV; the folder implements them from the bit representation
  (rounding by clearing fraction bits, the square root by an exact integer
  root), so `no_std` builds fold exactly what `std` builds fold. A float
  operation whose result is a NaN is not folded: OPS lets a machine produce any
  quiet NaN, and folding would fix one payload at compile time.
- **The pipeline is pass-lang.** The sweep loop is a `pass_lang::PassManager`
  run to a fixpoint. pass-lang's errors carry only a message, so the typed
  `OptError` travels beside it and is what callers see.

What is not done yet, plainly: no memory optimizations (loads are not
value-numbered or forwarded across stores, dead stores are not removed), no
inlining, no SROA, no loop canonicalization or strength reduction, and `fma` is
not constant-folded. Calls are never removed, even to functions marked
`readnone` (the attribute is an unchecked hint). See
[`dev/ROADMAP.md`](./dev/ROADMAP.md).

<hr>
<br>

## Testing

```bash
cargo test                       # unit + integration + property + doctests
cargo test --no-default-features # no_std + alloc
cargo clippy --all-targets --all-features -- -D warnings
cargo bench --bench bench
```

[`tests/differential.rs`](./tests/differential.rs) is the core of the suite:
random programs, run in the ir-lang reference interpreter before and after
optimization. [`tests/gc.rs`](./tests/gc.rs) does the same for programs with
GC references and safepoints, [`tests/passes.rs`](./tests/passes.rs) pins down
each pass on hand-written IR, [`tests/hostile.rs`](./tests/hostile.rs) feeds
deep, long, and wide functions and tiny budgets, and
[`tests/scale.rs`](./tests/scale.rs) checks the figures quoted above. Every
`rust` example in this README and in [`docs/API.md`](./docs/API.md) is compiled
and run as a doctest.

<hr>
<br>

## Cross-platform support

- Linux (x86_64, aarch64)
- macOS (x86_64, Apple Silicon)
- Windows (x86_64)

The crate uses no operating-system facilities and no platform-specific code; a
function optimizes to the same IR on every platform.

<hr>
<br>

## Contributing

See [`REPS.md`](./REPS.md) for the engineering standards every change is held to, [`dev/DIRECTIVES.md`](./dev/DIRECTIVES.md) for the definition of done, and [`dev/ROADMAP.md`](./dev/ROADMAP.md) for what comes next. Before a PR: `cargo fmt --all`, `cargo clippy --all-targets --all-features -- -D warnings`, and `cargo test --all-features` must be clean.

<br>

<div id="license">
    <h2>License</h2>
    <p>Licensed under either of</p>
    <ul>
        <li><b>Apache License, Version 2.0</b> &mdash; <a href="./LICENSE-APACHE">LICENSE-APACHE</a></li>
        <li><b>MIT License</b> &mdash; <a href="./LICENSE-MIT">LICENSE-MIT</a></li>
    </ul>
    <p>at your option.</p>
</div>

<div align="center">
  <h2></h2>
  <sup>COPYRIGHT <small>&copy;</small> 2026 <strong>James Gober.</strong></sup>
</div>
