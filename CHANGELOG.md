<h1 align="center">
    <img width="90px" height="auto" src="https://raw.githubusercontent.com/jamesgober/jamesgober/main/media/icons/hexagon-3.svg" alt="Triple Hexagon">
    <br><b>CHANGELOG</b>
</h1>
<p>
  All notable changes to <code>opt-lang</code> will be documented in this file. The format is based on <a href="https://keepachangelog.com/en/1.1.0/">Keep a Changelog</a>,
  and this project adheres to <a href="https://semver.org/spec/v2.0.0.html/">Semantic Versioning</a>.
</p>

---

## [Unreleased]

### Added

### Changed

### Fixed

### Security

---

## [0.3.0] - 2026-10-12

Moves opt-lang to `ir-lang` 2.0.0-alpha.3, the release irgen-lang's output is
moving to, so the family's native path (HIR -> irgen-lang -> ir-lang ->
opt-lang -> backend-lang) can run on one IR version (ISSUES P37, opt-lang's
half). Adds OPS v2 (`pow`, `shift = saturate`) to every pass, replaces the
0.2 rewrite workarounds with the builder operations ir-lang added for them,
and is tested on programs built with ir-lang's SSA-construction API and
automatic statepoint insertion.

### Breaking

- **Requires `ir-lang = "=2.0.0-alpha.3"`** (was `=2.0.0-alpha.1`). The
  public API takes and returns `ir_lang` types (`Module`, `Builder`,
  `FuncId`, `ValidationError`, `BuildError`, ...), so callers must use the same
  ir-lang release. No opt-lang signature changed.
- **Optimized output can contain an `unreachable` terminator** that the input
  did not have: a `check` whose operation must stay a `check` (a signed `pow`,
  which ir-lang always treats as fallible) but whose error edge provably cannot
  be taken now has that edge pointing at one shared `unreachable` block per
  function, so the old error handler can be deleted. A backend reading
  opt-lang's output must accept `unreachable` (it is part of ir-lang 2.0).
- Behaviour follows ir-lang alpha.3's rule (ISSUES P36): a negative `pow`
  exponent is the `NegativeExponent` error (code 6) under every `overflow`
  policy, `trap` included, and is folded to the `check`'s error edge with
  `6`, never to a trap.

### Added

- **OPS v2 constant folding**: integer `pow` (exact, `0 ** 0 = 1`, overflow per
  policy, negative exponent -> `NegativeExponent`), float `pow` through
  ir-lang's shared `ls_pow` (in `core`, so `no_std` folds it too; a NaN
  result is not folded), and `shl`/`shr` under `shift = saturate`. Checked
  against `ir_lang::interp::eval_binary` on every type and policy over edge
  values, random bits, and small exponents near the overflow boundary.
- **Partial folding** (operations with only some operands constant), exact
  under every policy and property-tested against the interpreter: `x ** 0`,
  `x * 0` are constants; `x ** 1`, `x + 0`, `x - 0`, `x * 1`, `x / 1`, shifts
  by zero are the operand; a negative constant exponent, a division by a
  constant zero, and a constant out-of-range `error` shift always raise;
  `saturate` shifts by at least the width are `0` (left; right on unsigned);
  `1 ** y` is `1` whenever it succeeds. SCCP uses it for plain instructions and
  for `check` edges, so a `check` knows which edges can be taken and which
  error code remains.
- **`check` rewrites that respect ir-lang's placement rule**: a `check` that
  cannot raise becomes a plain instruction only when `can_error(policy, type)`
  accepts the plain form. `x ** 2` becomes `x * x` under the same overflow
  policy (plain under `wrap`/`trap`, `check mul<overflow=error>` under
  `error`); a signed `saturate` shift by a known non-negative amount becomes
  a `mask` shift (by `width - 1` past the width, which is the sign fill);
  a `check` that must stay but cannot raise gets its error edge redirected to
  an `unreachable` stub (reused, so the pass stays idempotent). An error edge
  that can fire is never touched.
- GVN applies `x ** 1 = x` (plain integer `pow`) and keeps shifts by zero under
  every shift policy.
- `examples/variables.rs`: a loop lowered with ir-lang's variable API, a signed
  `pow` in a `check`, a GC reference across a call with statepoints from
  `insert_statepoints`, then `optimize` (the square becomes a `mul` and is
  hoisted out of the loop).
- Tests: `tests/variables.rs`, a differential over random programs built with
  `declare_var`/`def_var`/`use_var`/`seal_block`, OPS v2 checks, and a `ref`
  kept across calls with statepoints from `insert_statepoints` (pipeline and
  each pass alone, validated, run before and after); the random-program
  generator now emits `pow` (constant and variable exponents) and `saturate`
  shifts, placed by `can_error`; `insert_statepoints` run on every optimized
  GC and variable program must add nothing; per-pass OPS v2 tests on textual
  IR; hostile `check pow` chains and 10,000 `pow`s by `u64::MAX`; fold tests
  for `pow`, `saturate`, `error_kinds` against `can_error`, and partial folds.
- Benchmarks: an `edit` group measuring the two bulk rewrites
  (`dce-dead-params`: DCE removing 350,000 parameters; `simplify-cfg-merge`:
  merging a 50,000-block chain).

### Changed

- **Instruction moves use `Builder::move_inst`** (O(1), handle and results
  kept) instead of re-inserting a copy and forwarding the old results (LICM
  hoisting, block merging). Measured against 0.2.0's code on alpha.3:
  `edit/simplify-cfg-merge` -32% to -53% (two runs), `pass/simplify-cfg`
  -23% (100k and 1M), `pass/licm` -18% to -28%.
- **Bulk parameter removal uses `Builder::remove_block_params`** (one linear
  pass) instead of removing up to 16 parameters one by one and rebuilding the
  blocks beyond that. Measured: `edit/dce-dead-params` from no change to -16%
  over two runs (0.2's rebuild path was already linear), `pass/dce` and
  `pass/copy-prop` within noise; blocks keep their handles (no block split and
  retarget), and the rebuild code is gone.
- The fallibility of an operation (`fold::error_kinds`) now takes the operand
  type, matching ir-lang's `BinaryOp::can_error(policy, ty)`: a signed `pow`
  can raise `NegativeExponent` and a signed `saturate` shift
  `ShiftOutOfRange` without an `error` field.

### Migration from 0.2

| 0.2.0 | 0.3.0 |
|---|---|
| `ir-lang = "=2.0.0-alpha.1"` | `ir-lang = "=2.0.0-alpha.3"` (see ir-lang's CHANGELOG for its alpha.2 and alpha.3 changes: `can_error(policy, ty)`, signed `pow` always in a `check`) |
| Backends could assume the optimizer adds no `unreachable` | Accept `unreachable` (a dead `check` error edge points at one) |

No opt-lang call site changes.

---

## [0.2.0] - 2026-10-09

The foundation: the six core SSA optimizations for `ir-lang` 2.0, a pipeline that runs them to a fixpoint with the IR validator between passes, and work budgets on every pass. Verified by differential tests against the ir-lang reference interpreter.

### Added

- **`optimize`** (Tier 1): optimizes every function of an `ir_lang::Module` with the default pipeline.
- **`Optimizer`** (Tier 2): `new`, `passes`, `max_iterations`, `budget`, `validate`, `compact`, `run`, `run_function`.
- **`run_pass`** (Tier 3): one pass on an `ir_lang::Builder`, drawing from a `Budget`.
- **`PassKind`**: `SimplifyCfg`, `Sccp`, `CopyProp`, `Gvn`, `Licm`, `Dce`, with `ALL`, `name`, `from_name`, and `Display`; `DEFAULT_PIPELINE`, `DEFAULT_MAX_ITERATIONS`, `DEFAULT_STEPS_PER_UNIT`.
- **`Budget`**, **`Stats`**, **`PassStats`**, and the `#[non_exhaustive]` **`OptError`** (`Module`, `InvalidInput`, `InvalidOutput`, `Build`).
- **SCCP** over block parameters and executable edges, including `switch` and `check` edges: a `check` with constant operands folds to its normal edge, its error edge (with the OPS error code), or a `trap`; a `check` that provably cannot fail becomes the plain operation; a single-kind policy's error code is known on the error edge.
- **Constant folding** that follows `specs/OPS.md` exactly, policy by policy, checked against the interpreter's `eval_*` functions; never folds an operation that would raise into a value; IEEE rounding and square root implemented in `core`, so `no_std` folds identically.
- **GVN**: dominator-based value numbering of pure operations, canonical commutative operands and comparisons, exact integer identities.
- **DCE**: side-effect aware (calls, stores, atomics, fences, bulk memory, volatile loads, safepoints, trapping policies), including dead block parameters and dead loop variables.
- **CFG simplification**: constant and trivial branch folding, switch case pruning, unreachable-block removal, jump threading through empty blocks, block merging.
- **Copy propagation and block-parameter elimination** (trivial block parameters, loops included).
- **LICM**: pure loop-invariant operations hoisted into preheaders (created when needed), inner loops first.
- GC safety: values of type `ref`, and values derived from one, are never made constant, value-numbered, or hoisted.
- Bulk block-parameter removal and instruction moves in linear time on top of the ir-lang builder.
- Tests: differential (random programs before and after, the pipeline, each pass alone, random pass sequences), GC programs with safepoints, per-pass unit tests on textual IR, idempotence, hostile shapes (40,000-deep chains, 10,000-deep dominator trees, 300-deep loop nests, 20,000-case switches, 3,000-parameter blocks), budgets, and scale; criterion benchmarks at 100k and 1M instructions; `optimize` and `pipeline` examples.

### Changed

- Wired `ir-lang = "=2.0.0-alpha.1"` (and its `interp` feature for tests) and `pass-lang = "1"`.

---

## [0.1.0] - 2026-10-08

Initial scaffold and repository bootstrap. No domain logic yet &mdash; this release establishes the structure, tooling, and quality gates the implementation will be built on.

### Added

- `Cargo.toml` with crate metadata, Rust 2024 edition, MSRV 1.85.
- Dual `Apache-2.0 OR MIT` license files.
- `README.md`, `CHANGELOG.md`, and a documentation skeleton.
- `REPS.md` compliance baseline.
- `.github/workflows/ci.yml` CI matrix; `deny.toml`, `clippy.toml`, `rustfmt.toml`.
- `dev/DIRECTIVES.md` and `dev/ROADMAP.md` (committed engineering standards + plan).

[Unreleased]: https://github.com/jamesgober/opt-lang/compare/v0.3.0...HEAD
[0.3.0]: https://github.com/jamesgober/opt-lang/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/jamesgober/opt-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/opt-lang/releases/tag/v0.1.0
