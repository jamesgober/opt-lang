//! # opt_lang
//!
//! SSA optimizations for [`ir_lang`] 2.0: the IR-to-IR stage of the `-lang`
//! family's native compiler path, between the front end's lowering and
//! instruction selection. It makes a program smaller and faster without
//! changing what it computes, traps with, raises, or writes to memory.
//!
//! ## Quick start
//!
//! One call optimizes every function of a module:
//!
//! ```
//! use ir_lang::{Linkage, Module, Overflow, Signature, Type};
//!
//! // fn f(x: i64) -> i64 { let a = 2 + 3; let b = x * a; let c = x * a; b + c }
//! let mut m = Module::new("demo");
//! let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
//! let mut b = m.build(f)?;
//! let x = b.param(0)?;
//! let (two, three) = (b.iconst(Type::I64, 2)?, b.iconst(Type::I64, 3)?);
//! let a = b.add(two, three, Overflow::Wrap)?;
//! let p = b.mul(x, a, Overflow::Wrap)?;
//! let q = b.mul(x, a, Overflow::Wrap)?;
//! let r = b.add(p, q, Overflow::Wrap)?;
//! b.ret(&[r])?;
//!
//! let stats = opt_lang::optimize(&mut m)?;
//! assert_eq!((stats.insts_before(), stats.insts_after()), (6, 3));
//! let text = m.display_function(f).to_string();
//! assert!(text.contains("v1: i64 = const 5"), "{text}");
//! assert!(text.contains("v2: i64 = mul<overflow=wrap> v0, v1"), "{text}");
//! assert!(text.contains("v3: i64 = add<overflow=wrap> v2, v2"), "{text}");
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ## The passes
//!
//! | Pass | What it does |
//! |---|---|
//! | [`PassKind::SimplifyCfg`] | folds constant and trivial branches, removes unreachable blocks, threads jumps through empty blocks, merges straight-line blocks |
//! | [`PassKind::Sccp`] | sparse conditional constant propagation over block parameters, `switch`, and `check` edges, folding with the exact OPS policies |
//! | [`PassKind::CopyProp`] | replaces block parameters that always receive one value, and removes them |
//! | [`PassKind::Gvn`] | dominator-based value numbering of pure operations |
//! | [`PassKind::Licm`] | hoists pure loop-invariant operations into preheaders |
//! | [`PassKind::Dce`] | removes dead instructions and dead block parameters, keeping every side effect |
//!
//! [`optimize`] runs [`DEFAULT_PIPELINE`] to a fixpoint. [`Optimizer`] chooses
//! the passes, the number of sweeps, the budget, and validation; [`run_pass`]
//! runs one pass on a [`Builder`](ir_lang::Builder) for callers with their own
//! pipeline.
//!
//! ## Guarantees
//!
//! - **Semantics are preserved**: return values, traps and their codes, `check`
//!   errors and their codes, exceptions, and memory effects (stores, atomics,
//!   volatile accesses, calls, and their order) are unchanged. Constant folding
//!   follows `specs/OPS.md` exactly, and an operation whose policy would raise at
//!   run time is never folded into a value. Checked by differential tests that
//!   run random programs before and after optimization in the ir-lang reference
//!   interpreter.
//! - **The IR stays valid**: every pass leaves the function valid under
//!   [`ir_lang::Module::validate`], including the safepoint rules for GC
//!   references. The validator runs after every pass in debug builds and tests.
//! - **Bounded work**: every pass is iterative (no recursion over the input) and
//!   draws from a [`Budget`]; a function whose budget runs out is left valid and
//!   partly optimized.
//!
//! What is not done yet: no memory optimizations (loads are not value-numbered
//! or forwarded, stores are not removed), no inlining, no SROA, no strength
//! reduction, and `fma` is not constant-folded. See `dev/ROADMAP.md`.
//!
//! ## Features
//!
//! - `std` (default): the standard library; without it the crate is `#![no_std]`
//!   and needs only `alloc`. Optimization results are identical either way
//!   (folding implements IEEE rounding and square root itself).

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(unused_must_use)]
#![deny(unused_results)]
#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]
#![deny(clippy::todo)]
#![deny(clippy::unimplemented)]
#![deny(clippy::print_stdout)]
#![deny(clippy::print_stderr)]
#![deny(clippy::dbg_macro)]
#![cfg_attr(test, allow(clippy::unwrap_used, clippy::expect_used))]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod analysis;
mod budget;
mod edit;
mod error;
mod float;
mod fold;
mod passes;
mod pipeline;
mod stats;

pub use budget::Budget;
pub use error::OptError;
pub use pipeline::{
    DEFAULT_MAX_ITERATIONS, DEFAULT_PIPELINE, DEFAULT_STEPS_PER_UNIT, Optimizer, PassKind, run_pass,
};
pub use stats::{PassStats, Stats};

/// Optimizes every function of `module` with the default pipeline (Tier 1).
///
/// The same as `Optimizer::new().run(module)`: [`DEFAULT_PIPELINE`] run to a
/// fixpoint (at most [`DEFAULT_MAX_ITERATIONS`] sweeps), with the default
/// budget, validation between passes in debug builds, and changed functions
/// compacted.
///
/// # Errors
///
/// [`OptError::InvalidInput`] if a function does not validate; the other
/// variants only for a defect in a pass.
///
/// # Examples
///
/// ```
/// use ir_lang::{Linkage, Module, Signature, Type};
///
/// let mut m = Module::new("m");
/// let f = m.declare_function("f", &Signature::new(&[], &[Type::I32]), Linkage::Export)?;
/// let mut b = m.build(f)?;
/// let unused = b.iconst(Type::I32, 1)?;
/// let v = b.iconst(Type::I32, 2)?;
/// b.ret(&[v])?;
/// # let _ = unused;
/// let stats = opt_lang::optimize(&mut m)?;
/// assert_eq!(stats.insts_after(), 1);
/// m.validate()?;
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn optimize(module: &mut ir_lang::Module) -> Result<Stats, OptError> {
    Optimizer::new().run(module)
}

/// Runs the README's examples as doctests, so its claims stay true.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;

/// Runs the API reference's examples as doctests.
#[cfg(doctest)]
#[doc = include_str!("../docs/API.md")]
struct ApiDoctests;
