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

## v0.5.0 - Implementation
- [ ] Inlining (budgeted, `inline`/`noinline` hints, cost model), SROA of stack aggregates
      (mem2reg), loop canonicalization (dedicated exits), strength reduction.
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
