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

[Unreleased]: https://github.com/jamesgober/opt-lang/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/jamesgober/opt-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/opt-lang/releases/tag/v0.1.0
