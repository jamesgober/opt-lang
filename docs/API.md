# opt-lang &mdash; API Reference

> Complete reference for every public item in `opt-lang`, with examples.
> **Status: pre-1.0 (0.2.0).** The surface is designed across the 0.x series
> and frozen at `1.0.0`, once a backend consumes optimized IR in production
> (LexerSketch decision D18). See [`../dev/ROADMAP.md`](../dev/ROADMAP.md).

<sub>Copyright &copy; 2026 <strong>James Gober</strong>.</sub>

## Table of contents

- [Overview](#overview)
- [Installation](#installation)
- [Quick start](#quick-start)
- [Concepts](#concepts)
  - [The pipeline](#the-pipeline)
  - [What is preserved](#what-is-preserved)
  - [Constant folding and policies](#constant-folding-and-policies)
  - [GC references](#gc-references)
  - [Budgets](#budgets)
  - [Validation](#validation)
  - [Handles and compaction](#handles-and-compaction)
- [`optimize`](#optimize)
- [`Optimizer`](#optimizer)
  - [`Optimizer::new`](#optimizernew)
  - [`Optimizer::passes`](#optimizerpasses)
  - [`Optimizer::max_iterations`](#optimizermax_iterations)
  - [`Optimizer::budget`](#optimizerbudget)
  - [`Optimizer::validate`](#optimizervalidate)
  - [`Optimizer::compact`](#optimizercompact)
  - [`Optimizer::run`](#optimizerrun)
  - [`Optimizer::run_function`](#optimizerrun_function)
- [`PassKind`](#passkind)
- [`run_pass`](#run_pass)
- [`Budget`](#budget)
- [`Stats`](#stats)
- [`PassStats`](#passstats)
- [`OptError`](#opterror)
- [Constants](#constants)
- [Feature flags](#feature-flags)
- [Limits and costs](#limits-and-costs)
- [Stability](#stability)

## Overview

`opt-lang` rewrites `ir_lang` 2.0 functions into smaller, faster functions
that behave identically. Six passes ([`PassKind`](#passkind)) run in a
pipeline to a fixpoint; [`optimize`](#optimize) is the one-call path,
[`Optimizer`](#optimizer) the configured one, and [`run_pass`](#run_pass)
runs a single pass on an `ir_lang::Builder`.

## Installation

```toml
[dependencies]
opt-lang = "0.2"
ir-lang  = "=2.0.0-alpha.1"
```

## Quick start

```rust
use ir_lang::{CmpOp, Linkage, Module, Signature, Type};

// if 1 < 2 { ret 10 } else { ret 20 }
let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[Type::I32]), Linkage::Export)?;
let mut b = m.build(f)?;
let (one, two) = (b.iconst(Type::I32, 1)?, b.iconst(Type::I32, 2)?);
let c = b.compare(CmpOp::Lt, one, two)?;
let (t, e) = (b.create_block(&[])?, b.create_block(&[])?);
b.branch(c, t, &[], e, &[])?;
b.switch_to(t)?;
let ten = b.iconst(Type::I32, 10)?;
b.ret(&[ten])?;
b.switch_to(e)?;
let twenty = b.iconst(Type::I32, 20)?;
b.ret(&[twenty])?;

let stats = opt_lang::optimize(&mut m)?;
assert_eq!((stats.blocks_before(), stats.blocks_after()), (3, 1));
assert!(m.display_function(f).to_string().contains("const 10\n    ret"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Concepts

### The pipeline

A pipeline is a list of passes run in order; one pass over the list is a
*sweep*. Sweeps repeat while any pass changes the function, up to
[`max_iterations`](#optimizermax_iterations), so a function is usually left at
the pipeline's fixpoint ([`Stats::converged`](#stats) counts those). Each
function is optimized on its own, with its own budget. The default pipeline,
[`DEFAULT_PIPELINE`](#constants), is

```text
simplify-cfg, sccp, copy-prop, gvn, licm, dce, simplify-cfg
```

The sweep loop is a `pass_lang::PassManager` run with `run_to_fixpoint`.

### What is preserved

Everything a program can observe: its return values; a trap and its code; a
`check` error edge and the OPS error code it passes; an exception and its
payload; every call (import or not), with its arguments, in order; every store,
atomic, fence, bulk memory operation, and volatile access, in order. What may
change is what cannot be observed: which instructions compute a value, how
many blocks there are, and which non-volatile loads happen (a dead load is
removed; the IR treats an invalid access as undefined behaviour, so removing a
load that would have faulted does not change a defined program).

Calls are never removed or moved, whatever their attributes (`readnone` and
`readonly` are unchecked hints; a callee could still trap or loop).

### Constant folding and policies

Folding follows `specs/OPS.md` exactly. Operands are the constants' bits; the
result is the bits the reference interpreter would compute at run time:

- An operation that succeeds folds to its value.
- An operation whose `error` policy fires is never a value. Inside a `check`
  it becomes a jump along the error edge, passing the OPS code (`1`
  `ArithOverflow`, `2` `DivByZero`, `3` `ShiftOutOfRange`, `4`
  `InvalidConversion`, `5` `InvalidChar`).
- An operation whose `trap` policy fires is never a value either: a plain
  instruction stays as it is (it traps at run time), and a `check` becomes a
  `trap` terminator with the same code.
- A float arithmetic result that is a NaN is not folded (OPS §4 lets a
  machine produce any quiet NaN; folding would pick one payload at compile
  time). Bit-level operations (`bitcast`, `select`, constants) are folded even
  when the bits are a NaN.
- `fma`, and conversions to or from `ptr` and `ref`, are not folded.

A `check` whose operation provably cannot fail, given the constants known
about its operands, becomes the plain operation and a jump: adding or
subtracting a constant zero, multiplying by a constant zero or one, a shift by
a constant amount within the width, a division or remainder by a constant
other than `0` (and `-1` for a signed division), and an `int_cast` to a type
that holds every value of the source type.

```rust
use ir_lang::{BinaryOp, BlockArg, BlockCall, InstData, Linkage, Module, Overflow, Policy, Signature, Type};

// x / 4 with div_zero=error can never fail: the check becomes a plain division.
let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let x = b.param(0)?;
let four = b.iconst(Type::I64, 4)?;
let ok = b.create_block(&[Type::I64])?;
let err = b.create_block(&[Type::U32])?;
let div = Policy::overflow(Overflow::Error).with_div_zero(ir_lang::DivZero::Error);
b.check(
    InstData::Binary { op: BinaryOp::Div, policy: div, args: [x, four] },
    BlockCall::with_args(ok, &[BlockArg::Result(0)]),
    BlockCall::with_args(err, &[BlockArg::ErrorCode]),
)?;
b.switch_to(ok)?;
let q = b.block_param(ok, 0)?;
b.ret(&[q])?;
b.switch_to(err)?;
b.trap(99)?;

opt_lang::optimize(&mut m)?;
let text = m.display_function(f).to_string();
assert!(!text.contains("check") && !text.contains("trap 99"));
assert!(text.contains("div<overflow=wrap,div_zero=trap>"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

### GC references

A `ref`, and every value derived from one (`ref_to_ptr`, and anything
computed from a derived value or passed through a block parameter), is never
turned into a constant, value-numbered, or hoisted: any of those could keep it
live across a safepoint, which the IR's safepoint rules forbid. Such values
are still removed when dead.

### Budgets

Every pass charges its work, in steps, to a [`Budget`](#budget) before doing
it. A step is roughly one instruction, block, edge, or value visited. A pass
the budget cannot pay for does nothing; a function whose budget runs out is
left valid and partly optimized, and is counted by
[`Stats::budget_exhausted`](#stats). Running out is not an error.

The default budget per function is
[`DEFAULT_STEPS_PER_UNIT`](#constants) (256) steps per unit of size
(instructions + blocks + values) plus 65,536. The linear passes never come
near it (the whole default pipeline fits in 160 steps per unit on the typical
benchmark shape); it exists for inputs built to drive the non-linear parts:
nested loop bodies in LICM (a block in `d` nested loops is visited `d` times),
repeated re-examination in copy propagation, and the internal safety limit of
SCCP.

### Validation

The input is always validated before optimization (`OptError::InvalidInput`;
nothing is changed). After every pass that changed the function, the ir-lang
validator runs again when [`validate`](#optimizervalidate) is on (the default
in debug builds) and reports `OptError::InvalidOutput`, which would be a
defect in this crate.

### Handles and compaction

Passes rewrite through the ir-lang `Builder`, which never renumbers: removed
instructions and blocks become tombstones and replaced values forward to their
replacements. By default ([`compact`](#optimizercompact)), every function that
changed is compacted at the end, so handles are renumbered densely and the
printed IR is canonical. Turn compaction off to keep handles stable.

## `optimize`

```rust,ignore
pub fn optimize(module: &mut ir_lang::Module) -> Result<Stats, OptError>
```

Optimizes every function with a body using the default configuration; the
same as `Optimizer::new().run(module)`.

**Errors:** [`OptError::InvalidInput`](#opterror) if a function does not
validate (functions before it are already optimized; it and the ones after are
untouched); the other variants only for a defect in a pass.

```rust
use ir_lang::{Linkage, Module, Signature, Type};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[Type::I32]), Linkage::Export)?;
let mut b = m.build(f)?;
let _unused = b.iconst(Type::I32, 1)?;
let v = b.iconst(Type::I32, 2)?;
b.ret(&[v])?;
let stats = opt_lang::optimize(&mut m)?;
assert_eq!((stats.insts_before(), stats.insts_after()), (2, 1));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Optimizer`

```rust,ignore
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Optimizer { /* private */ }
impl Default for Optimizer
```

The configured optimizer (Tier 2). Built by value: every setter takes and
returns the optimizer, so a configuration reads as one chain. It holds no
state between runs and can be reused.

### `Optimizer::new`

```rust,ignore
pub fn new() -> Optimizer
```

The default configuration: [`DEFAULT_PIPELINE`](#constants),
[`DEFAULT_MAX_ITERATIONS`](#constants) (4) sweeps, the default budget,
validation between passes in debug builds only, and compaction on.

```rust
let opt = opt_lang::Optimizer::new();
assert_eq!(opt, opt_lang::Optimizer::default());
```

### `Optimizer::passes`

```rust,ignore
pub fn passes(self, passes: &[PassKind]) -> Optimizer
```

The passes to run each sweep, in order. A pass may appear more than once; an
empty list runs nothing (it still validates the input and reports sizes).

```rust
use ir_lang::{Linkage, Module, Overflow, Signature, Type};
use opt_lang::{Optimizer, PassKind};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let x = b.param(0)?;
let _dead = b.mul(x, x, Overflow::Wrap)?;
b.ret(&[x])?;
let stats = Optimizer::new().passes(&[]).run(&mut m)?;
assert_eq!(stats.insts_after(), 1); // nothing ran
let stats = Optimizer::new().passes(&[PassKind::Dce]).run(&mut m)?;
assert_eq!(stats.insts_after(), 0);
# Ok::<(), Box<dyn std::error::Error>>(())
```

### `Optimizer::max_iterations`

```rust,ignore
pub fn max_iterations(self, n: usize) -> Optimizer
```

The most sweeps per function. The pipeline stops earlier at its fixpoint (a
sweep that changes nothing). `0` runs nothing.

```rust
use ir_lang::{Linkage, Module, Signature};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
m.build(f)?.ret(&[])?;
let stats = opt_lang::Optimizer::new().max_iterations(0).run(&mut m)?;
assert_eq!(stats.iterations(), 0);
# Ok::<(), Box<dyn std::error::Error>>(())
```

### `Optimizer::budget`

```rust,ignore
pub fn budget(self, steps: u64) -> Optimizer
```

A fixed budget of `steps` per function instead of the size-proportional
default. See [Budgets](#budgets).

```rust
use ir_lang::{Linkage, Module, Signature};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
m.build(f)?.ret(&[])?;
let stats = opt_lang::Optimizer::new().budget(0).run(&mut m)?;
assert_eq!(stats.budget_exhausted(), 1);
# Ok::<(), Box<dyn std::error::Error>>(())
```

### `Optimizer::validate`

```rust,ignore
pub fn validate(self, on: bool) -> Optimizer
```

Whether to run the ir-lang validator after every pass that changed a function
(default: on in debug builds, off in release builds). The input is validated
either way. See [Validation](#validation).

```rust
let checked = opt_lang::Optimizer::new().validate(true);
assert_ne!(checked, opt_lang::Optimizer::new().validate(false));
```

### `Optimizer::compact`

```rust,ignore
pub fn compact(self, on: bool) -> Optimizer
```

Whether to compact every changed function at the end (default on). See
[Handles and compaction](#handles-and-compaction).

```rust
use ir_lang::{Linkage, Module, Signature, Type};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[Type::U8]), Linkage::Export)?;
let mut b = m.build(f)?;
let _dead = b.iconst(Type::U8, 1)?;
let v = b.iconst(Type::U8, 2)?;
b.ret(&[v])?;
opt_lang::Optimizer::new().compact(false).run(&mut m)?;
// The surviving value keeps its handle.
assert!(m.display_function(f).to_string().contains("v1: u8 = const 2"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

### `Optimizer::run`

```rust,ignore
pub fn run(&self, module: &mut ir_lang::Module) -> Result<Stats, OptError>
```

Optimizes every function with a body, in declaration order.

**Errors:** as [`optimize`](#optimize).

```rust
use ir_lang::{Linkage, Module, Signature};

let mut m = Module::new("m");
let _ext = m.declare_function("ext", &Signature::new(&[], &[]), Linkage::Import)?;
let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
m.build(f)?.ret(&[])?;
let stats = opt_lang::Optimizer::new().run(&mut m)?;
assert_eq!(stats.functions(), 1); // the import has no body
# Ok::<(), Box<dyn std::error::Error>>(())
```

### `Optimizer::run_function`

```rust,ignore
pub fn run_function(&self, module: &mut ir_lang::Module, func: ir_lang::FuncId) -> Result<Stats, OptError>
```

Optimizes one function.

**Errors:** [`OptError::Module`](#opterror) if `func` is unknown or has no
body; otherwise as [`optimize`](#optimize).

```rust
use ir_lang::{FuncId, Linkage, Module, Signature};
use opt_lang::{OptError, Optimizer};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
m.build(f)?.ret(&[])?;
assert_eq!(Optimizer::new().run_function(&mut m, f)?.functions(), 1);
assert!(matches!(
    Optimizer::new().run_function(&mut m, FuncId::from_u32(7)),
    Err(OptError::Module(_))
));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `PassKind`

```rust,ignore
#[non_exhaustive]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum PassKind { SimplifyCfg, Sccp, CopyProp, Gvn, Licm, Dce }

impl PassKind {
    pub const ALL: [PassKind; 6];
    pub const fn name(self) -> &'static str;
    pub fn from_name(name: &str) -> Option<PassKind>;
}
impl Display for PassKind // the name
```

One optimization pass. Every pass leaves the function valid, reports whether
it changed anything, and is idempotent (a second run changes nothing).

| Variant | Name | What it does | Cost |
|---|---|---|---|
| `SimplifyCfg` | `simplify-cfg` | Folds a branch on a constant, or with two identical edges, into a jump; folds a switch on a constant; drops switch cases that go where the default goes; removes unreachable blocks; threads edges through empty blocks that only jump on (substituting their parameters; never an unwind edge, never past a block whose parameter is used elsewhere); merges a block into its only predecessor when that predecessor jumps to it. Repeats until nothing changes. | Linear per round; at most 8 rounds per run. |
| `Sccp` | `sccp` | Sparse conditional constant propagation (Wegman–Zadeck) over block parameters and executable edges, including `switch` and `check` edges; see [Constant folding and policies](#constant-folding-and-policies). Leaves unreachable code for `SimplifyCfg`. | Linear (each value is lowered at most twice, each edge becomes executable once). |
| `CopyProp` | `copy-prop` | Replaces a block parameter that receives the same value on every edge from reachable code (edges passing the parameter back to itself are ignored), then removes it; re-examines the parameters that fed on it. | Linear, plus budgeted re-examination. |
| `Gvn` | `gvn` | Dominator-based value numbering of pure operations (constants, arithmetic without trapping policies, comparisons, conversions, `select`, `fma`, address computation); commutative integer operations and comparisons are canonicalized. Applies exact integer identities: `x + 0`, `x - 0`, `x * 1`, `x / 1`, `x \| 0`, `x ^ 0`, `x & -1`, `x & x`, `x \| x`, `min(x, x)`, `max(x, x)`, shifts by zero, `not(not(x))`, `select(c, x, x)`, a `bitcast` back to the original type, a `narrow` of a `zext`/`sext` back to the original type. Loads are not numbered. | Linear; hash-table probes are capped. |
| `Licm` | `licm` | Hoists pure loop-invariant operations (the set GVN numbers) into the loop's preheader, creating one when the loop has something to hoist and no single outside predecessor ending in a jump; inner loops first. | Linear plus the sizes of nested loop bodies (budgeted). |
| `Dce` | `dce` | Removes instructions without side effects whose results are unused, and block parameters that are never used (including loop variables only passed around their loop). Keeps calls, stores, atomics, fences, bulk memory, volatile loads, safepoints, and every operation with a trapping policy. | Linear. |

```rust
use opt_lang::PassKind;

assert_eq!(PassKind::Licm.name(), "licm");
assert_eq!(PassKind::Licm.to_string(), "licm");
assert_eq!(PassKind::from_name("copy-prop"), Some(PassKind::CopyProp));
assert_eq!(PassKind::from_name("inline"), None);
for p in PassKind::ALL {
    assert_eq!(PassKind::from_name(p.name()), Some(p));
}
```

## `run_pass`

```rust,ignore
pub fn run_pass(b: &mut ir_lang::Builder<'_>, pass: PassKind, budget: &mut Budget) -> Result<bool, OptError>
```

Runs one pass on the function a builder edits (Tier 3), for callers with
their own pipeline. Validates the function first, runs the pass, and in debug
builds validates again. Returns whether the pass changed anything. A pass the
budget cannot pay for returns `Ok(false)` and leaves the budget
[exhausted](#budget). The function is not compacted.

**Errors:** [`OptError::InvalidInput`](#opterror) (nothing changed);
`InvalidOutput` or `Build` for a defect in the pass.

```rust
use ir_lang::{Linkage, Module, Overflow, Signature, Type};
use opt_lang::{Budget, PassKind};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let x = b.param(0)?;
let y = b.add(x, x, Overflow::Wrap)?;
let z = b.add(x, x, Overflow::Wrap)?;
let w = b.mul(y, z, Overflow::Wrap)?;
b.ret(&[w])?;

let mut budget = Budget::new(1_000_000);
assert!(opt_lang::run_pass(&mut m.edit(f)?, PassKind::Gvn, &mut budget)?);
assert!(!opt_lang::run_pass(&mut m.edit(f)?, PassKind::Gvn, &mut budget)?);
assert!(budget.remaining() < 1_000_000);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Budget`

```rust,ignore
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Budget { /* private */ }

impl Budget {
    pub const fn new(steps: u64) -> Budget;
    pub const fn unlimited() -> Budget;
    pub const fn remaining(&self) -> u64;
    pub const fn is_exhausted(&self) -> bool;
}
```

A budget of work steps that passes draw from. `new(steps)` holds `steps`;
`unlimited()` holds `u64::MAX`. `remaining` is what is left; `is_exhausted`
says whether a pass was refused or cut short for lack of steps. See
[Budgets](#budgets).

```rust
use ir_lang::{Linkage, Module, Signature};
use opt_lang::{Budget, PassKind};

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
m.build(f)?.ret(&[])?;

let mut none = Budget::new(0);
assert!(!opt_lang::run_pass(&mut m.edit(f)?, PassKind::Sccp, &mut none)?);
assert!(none.is_exhausted());

let mut plenty = Budget::unlimited();
let _ = opt_lang::run_pass(&mut m.edit(f)?, PassKind::Sccp, &mut plenty)?;
assert!(!plenty.is_exhausted());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Stats`

```rust,ignore
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Stats { /* private */ }
impl Default for Stats

impl Stats {
    pub const fn functions(&self) -> usize;
    pub const fn insts_before(&self) -> usize;
    pub const fn insts_after(&self) -> usize;
    pub const fn blocks_before(&self) -> usize;
    pub const fn blocks_after(&self) -> usize;
    pub const fn iterations(&self) -> usize;
    pub const fn converged(&self) -> usize;
    pub const fn budget_exhausted(&self) -> usize;
    pub fn pass(&self, kind: PassKind) -> PassStats;
    pub fn passes(&self) -> &[PassStats];
}
```

What a run did, summed over the functions it optimized:

| Method | Meaning |
|---|---|
| `functions` | Function bodies optimized. |
| `insts_before`, `insts_after` | Live instructions before and after (terminators excluded). |
| `blocks_before`, `blocks_after` | Live blocks before and after. |
| `iterations` | Sweeps run (a sweep runs every pass once). |
| `converged` | Functions whose last sweep changed nothing. |
| `budget_exhausted` | Functions where a pass was refused or cut short by the budget. |
| `pass(kind)` | The counts of one pass ([`PassStats`](#passstats)). |
| `passes()` | The counts of every pass, in [`PassKind::ALL`](#passkind) order. |

```rust
use ir_lang::{Linkage, Module, Overflow, Signature, Type};
use opt_lang::PassKind;

let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
let mut b = m.build(f)?;
let x = b.param(0)?;
let two = b.iconst(Type::I64, 2)?;
let y = b.mul(two, two, Overflow::Wrap)?;
let z = b.add(x, y, Overflow::Wrap)?;
b.ret(&[z])?;

let stats = opt_lang::optimize(&mut m)?;
assert_eq!(stats.functions(), 1);
assert_eq!((stats.insts_before(), stats.insts_after()), (3, 2));
assert_eq!(stats.converged(), 1);
assert_eq!(stats.budget_exhausted(), 0);
assert!(stats.pass(PassKind::Sccp).changes() >= 1);
assert_eq!(stats.passes().len(), PassKind::ALL.len());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `PassStats`

```rust,ignore
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PassStats { /* private */ }

impl PassStats {
    pub const fn kind(&self) -> PassKind;
    pub const fn runs(&self) -> u64;
    pub const fn changes(&self) -> u64;
}
```

How many times one pass ran, over all functions and sweeps, and how many of
those runs changed the function.

```rust
use opt_lang::{PassKind, Stats};

let s = Stats::default().pass(PassKind::Dce);
assert_eq!((s.kind(), s.runs(), s.changes()), (PassKind::Dce, 0, 0));
```

## `OptError`

```rust,ignore
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OptError {
    Module(ir_lang::ModuleError),
    InvalidInput { func: FuncId, error: ValidationError },
    InvalidOutput { func: FuncId, pass: PassKind, error: ValidationError },
    Build { func: FuncId, pass: PassKind, error: BuildError },
}
impl Display, core::error::Error (with source), From<ModuleError>
```

| Variant | Meaning | What to do |
|---|---|---|
| `Module` | The function is unknown or has no body (`run_function`). | Pass a defined function. |
| `InvalidInput` | The function did not validate before optimization; it was not changed. | Fix the IR (the `ValidationError` says where). |
| `InvalidOutput` | A pass left the function invalid (reported when validation between passes is on). | A defect in this crate: report it with the input. |
| `Build` | The IR builder refused a rewrite a pass attempted; the function may be partly rewritten. | A defect in this crate: report it with the input. |

```rust
use ir_lang::{Linkage, Module, Signature};
use opt_lang::OptError;

// A body without a terminator is not valid IR.
let mut m = Module::new("m");
let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
let _ = m.build(f)?;
let err = opt_lang::optimize(&mut m).unwrap_err();
assert!(matches!(err, OptError::InvalidInput { .. }));
assert!(err.to_string().contains("not valid IR"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Constants

```rust,ignore
pub const DEFAULT_PIPELINE: &[PassKind];   // simplify-cfg, sccp, copy-prop, gvn, licm, dce, simplify-cfg
pub const DEFAULT_MAX_ITERATIONS: usize;  // 4
pub const DEFAULT_STEPS_PER_UNIT: u64;    // 256
```

```rust
use opt_lang::{DEFAULT_MAX_ITERATIONS, DEFAULT_PIPELINE, DEFAULT_STEPS_PER_UNIT, PassKind};

assert_eq!(DEFAULT_PIPELINE.first(), Some(&PassKind::SimplifyCfg));
assert_eq!(DEFAULT_PIPELINE.len(), 7);
assert_eq!(DEFAULT_MAX_ITERATIONS, 4);
assert_eq!(DEFAULT_STEPS_PER_UNIT, 256);
```

## Feature flags

| Feature | Default | Effect |
|---|---|---|
| `std` | yes | Forwards to `ir-lang/std` and `pass-lang/std`. Without it the crate is `no_std` and needs only `alloc`; the API and the optimization results are identical. |

## Limits and costs

| What | Bound |
|---|---|
| Recursion over the input | None: every algorithm is iterative. |
| Work per pass | Linear in instructions, values, blocks, and edges, except the budgeted parts named in [`PassKind`](#passkind). |
| `SimplifyCfg` rounds per run | 8 |
| GVN hash-table probe | 16 colliding entries (past that, a redundancy is missed, not searched for) |
| Default budget | 256 steps per unit of size + 65,536, per function |
| Bulk parameter removal | Up to 16 parameters per pass run with the builder's `remove_block_param`; more by rebuilding the blocks (linear in their edges and instructions) |

## Stability

This is a 0.x release: the surface may change in a minor release before
`1.0.0`, and every change is recorded in [`../CHANGELOG.md`](../CHANGELOG.md).
`PassKind` and `OptError` are `#[non_exhaustive]`, so new passes and error
kinds are additive. The dependency on `ir-lang` is pinned to
`=2.0.0-alpha.1` because that release is a pre-release; it moves with
ir-lang's 2.0 series.
