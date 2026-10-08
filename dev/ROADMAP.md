# opt-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation
- [ ] Pass infrastructure on pass-lang with validator hooks; DCE and SCCP. Blocked on ir-lang 2.0 mutation API for the full set (recorded per the anti-deferral rule).

## v0.5.0 - Implementation
- [ ] GVN, LICM, inlining, SROA, loop canonicalization; benchmarks on generated code.

## v0.9.0 - Hardening
- [ ] Differential fuzzing; compile-time budgets.

## v1.0.0 - Stable
- [ ] Frozen after backend-lang consumes optimized IR in production (D18).
