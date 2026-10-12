# opt-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation (DONE, 2026-10-09)
The core SSA optimizations on ir-lang 2.0, run as a validated, budgeted pipeline.
The ir-lang 2.0 mutation API this phase was blocked on shipped in 2.0.0-alpha.1.
Exit criteria:
- [x] Pass infrastructure on pass-lang, with the ir-lang validator between passes (on in debug builds and tests).
- [x] DCE, SCCP (including `switch` and `check` edges), GVN, CFG simplification, copy propagation and block-parameter elimination, LICM.
- [x] Every pass iterative and budgeted; idempotent; leaves the IR valid.
- [x] Differential tests against the ir-lang reference interpreter; per-pass unit tests; benches at 100k-1M instructions.

Delivered:
- `optimize` (Tier 1), `Optimizer` (Tier 2: `passes`, `max_iterations`, `budget`,
  `validate`, `compact`, `run`, `run_function`), `run_pass` (Tier 3), `PassKind`,
  `Budget`, `Stats`, `PassStats`, `OptError`, `DEFAULT_PIPELINE`,
  `DEFAULT_MAX_ITERATIONS`, `DEFAULT_STEPS_PER_UNIT`.
- SCCP (Wegman-Zadeck) over block parameters and executable edges; `check` folding to
  the normal edge, the error edge with the OPS code, or a `trap`; `check` relaxation
  when the operation provably cannot fail; known error codes for single-kind policies.
- Constant folding exactly per `specs/OPS.md`, checked against `ir_lang::interp::eval_*`
  over every operation, type, and policy; never folds a raising operation into a
  value; NaN arithmetic results are not folded; IEEE rounding and `sqrt` implemented
  in `core` (checked bit for bit against `std`), so `no_std` folds identically.
- GVN (dominator pre-order, scoped by dominance tests, capped probes) with canonical
  commutative operands and comparisons and exact integer identities.
- DCE with side-effect awareness and dead block-parameter (dead loop variable) removal.
- CFG simplification: constant/trivial branch folding, switch case pruning,
  unreachable-block removal, jump threading through empty blocks (never unwind edges,
  never past a block whose parameter is used elsewhere), block merging.
- Copy propagation / trivial block-parameter elimination (worklist, union-find).
- LICM with preheader creation, inner loops first, budgeted loop-body walks.
- GC safety: `ref`s and values derived from them are never made constant,
  value-numbered, or hoisted.
- Linear-time bulk edits over the ir-lang builder: instruction moves by
  re-insert-and-forward; bulk parameter removal by block rebuild when more than 16;
  mid-pipeline compaction when most of a function's arena is tombstones.
- Differential, GC, per-pass, idempotence, hostile-shape, budget, and scale tests;
  criterion benches (pipeline and each pass at 100k and 1M instructions; instruction
  reduction on the typical shape); `optimize` and `pipeline` examples.

Dependency wiring (decided here, recorded per the anti-deferral rule):
- **ir-lang: wired, `=2.0.0-alpha.1`** (exact pin: a pre-release), without default
  features in the library (forwarded by `std`). Its `interp` feature is a
  dev-dependency only: the reference interpreter is the test oracle. The folder does
  **not** call `ir_lang::interp::eval_*` at run time, because `interp` requires `std`
  and opt-lang supports `no_std`; it implements the same semantics in `core` and is
  checked against `eval_*` exhaustively over edge values and randomly.
- **pass-lang: wired, `1`.** The pipeline is a `PassManager` over a per-run session
  (module, function, budget), run with `run_to_fixpoint`. It fits with one workaround
  for ISSUES M49: `PassError` carries only a message, so a pass stores its typed
  `OptError` in the session before failing and the optimizer returns that. The
  `'static` bound on passes is harmless here (the passes are stateless); the dropped
  partial report on failure does not matter (a failure is a defect, returned as an
  error).

Moved out of 0.2.0 (anti-deferral record):
- **`fma` constant folding** -> v0.5.0. `core` has no correctly rounded fused
  multiply-add on the MSRV; an exact one needs wide-precision arithmetic written and
  verified on its own. Until then `fma` is evaluated at run time (correct, just not
  folded).

## v0.3.0 - ir-lang alpha.3 and OPS v2 (DONE, 2026-10-12)
Unblocks the native path (ISSUES P37, opt-lang's half): opt-lang 0.2 and
backend-lang 0.3 pinned ir-lang alpha.1 while irgen-lang 0.2 emits alpha.2.
Exit criteria:
- [x] `ir-lang = "=2.0.0-alpha.3"` (regular and dev with `interp`).
- [x] The 0.2 rewrite workarounds replaced by `Builder::remove_block_params` and
      `Builder::move_inst`, and the difference measured.
- [x] OPS v2 (`pow`, `shift = saturate`) in every pass: folding exactly per
      policy (floats via `ls_pow`), no error edge that can fire is folded away,
      a `check` becomes plain only where `can_error` allows, identities
      property-tested against the interpreter.
- [x] No pass breaks the statepoint (GC-list) invariants; the validator is the
      oracle.
- [x] Differential tests extended to OPS v2 and to programs built with the
      variable API; hostile and huge inputs; property tests for the new folds.

Delivered:
- OPS v2 folding in `fold.rs`: integer `pow` (repeated squaring, overflow per
  policy, a negative exponent is `NegativeExponent` under every policy, P36),
  float `pow` via `ir_lang::ls_pow` (in `core`, so `no_std` folds it), and
  `saturate` shifts; `error_kinds` takes the operand type and is tested equal
  to ir-lang's `can_error` for every operation, policy, and type.
- Partial folding (`fold::binary_partial`): constants, operand identities, and
  the error kinds still possible when only some operands are known. Used by
  SCCP for plain instructions and for `check` edges (feasible edges, known
  error code, normal-edge constant such as `1 ** y`).
- `check` rewrites under ir-lang's placement rule: plain only when
  `can_error` accepts the plain form; `x ** 2` -> `x * x` (plain under
  `wrap`/`trap`, `check mul` under `error`); signed `saturate` shifts by known
  non-negative amounts -> `mask` shifts; a `check` that must stay but cannot
  raise has its dead error edge redirected to a shared `unreachable` stub.
- GVN `x ** 1 = x`.
- `move_inst` in LICM and block merging; `remove_block_params` in DCE and copy
  propagation. Measured (criterion, same machine, against 0.2's code on
  alpha.3; this machine's run-to-run spread is about 10%): block merging 32-53%
  faster on a merge-heavy shape and `simplify-cfg` 23% on the typical shape,
  LICM 18-28%; parameter removal from no change to 16% faster (the rebuild
  path was already linear), with blocks keeping their handles. The whole
  pipeline went from ~69 ms / ~1.12 s (0.2.0's published run) to ~43 ms /
  ~0.89 s at 100k / 1M instructions.
- Tests: `tests/variables.rs` (variable-API programs with OPS v2 checks and
  statepoints from `insert_statepoints`), generator with `pow`/`saturate`,
  `insert_statepoints` adds nothing after optimization (GC and variable
  programs), OPS v2 pass tests, hostile `check pow` chains and huge exponents,
  partial-fold properties; `edit` benchmark group; `variables` example.

Statepoints (decision recorded here): the passes keep the GC-list invariants by
construction (no call or safepoint is moved, no GC list is edited, tracked
values are never made constant, numbered, or hoisted, and every forwarding
keeps uses in place). `insert_statepoints` is **not** re-run after the passes:
it would only cost time, since its input is already valid. Instead the tests
run it on every optimized GC and variable program and require it to add
nothing, beside the validator after every pass.

Dependency wiring:
- **ir-lang: `=2.0.0-alpha.3`** (exact pin, pre-release), regular without
  default features, dev with `interp`. Folding still does not call
  `ir_lang::interp::eval_*` at run time (`interp` requires `std`; opt-lang is
  `no_std`); it implements the semantics in `core` and is tested against
  `eval_*`, as in 0.2. Float `pow` calls `ir_lang::ls_pow` directly (it is in
  `core`).
- **pass-lang: `1`**, unchanged.
- **irgen-lang: not wired** (dev-dependency for realistic input was requested).
  irgen-lang 0.2.0 pins `ir-lang = "=2.0.0-alpha.2"`; Cargo cannot hold two
  semver-compatible pre-releases of one crate, so adding it next to opt-lang's
  `=2.0.0-alpha.3` fails to resolve (checked: "failed to select a version for
  `ir-lang`"). `tests/variables.rs` builds the same kind of input (the SSA
  variable API, `check`ed OPS v2 operations, statepoints) directly. Wire
  irgen-lang as a dev-dependency once it is released on alpha.3 (irgen 0.3,
  which also adds the native end-to-end test, P37).

Found, not fixed here (another crate):
- ir-lang 2.0.0-alpha.3's validator is quadratic on a deep chain of blocks
  whose error edges all join one handler (measured in a debug build: 5,000
  `check`s 0.3 s, 10,000 1.2 s, 20,000 6.7 s), and every optimizer run
  validates its input. That shape is what a front end produces for a long
  function whose fallible operations share one error handler. opt-lang's own
  analyses are linear on it (Lengauer-Tarjan dominators). The hostile tests use
  5,000-long chains for this reason. Reported for the ISSUES ledger.

## v0.5.0 - Implementation
- [ ] Inlining (budgeted, `inline`/`noinline` hints, cost model), SROA of stack aggregates
      (mem2reg), loop canonicalization (dedicated exits), strength reduction
      (0.3.0 already turns `x ** 2` into `x * x`; general `pow` by a constant
      exponent, multiplication by constants, and induction variables are here).
- [ ] Memory optimizations with an alias analysis: redundant load elimination and
      store-to-load forwarding, dead store elimination. (Not in 0.2.0's scope: they need
      memory dependence information that does not exist yet; GVN deliberately skips loads.)
- [ ] Exact `fma` folding (moved from 0.2.0, see above).
- [ ] `invoke` to `call` when the callee is checked `nounwind`, removing dead landing pads.
- [ ] Benchmarks on code generated by a real front end (HIR -> IR lowering), not only
      synthetic shapes.

## v0.9.0 - Hardening
- [ ] Differential fuzzing (cargo-fuzz targets over the textual IR); compile-time budgets
      tuned on real code.

## v1.0.0 - Stable
- [ ] Frozen after backend-lang consumes optimized IR in production (D18).
