//! The pass pipeline: which passes run, in what order, how often, and with what
//! checks between them.
//!
//! The pipeline is a [`pass_lang::PassManager`] over one function at a time,
//! run to a fixpoint (bounded by [`Optimizer::max_iterations`]). pass-lang's
//! [`PassError`] carries only a message, so the typed [`OptError`] of a failing
//! pass travels beside it in the session and is returned instead.

use alloc::vec::Vec;
use core::fmt;

use ir_lang::{Builder, FuncId, Module};
use pass_lang::{Outcome, Pass, PassError, PassManager};

use crate::analysis::size;
use crate::passes::{copy_prop, dce, gvn, licm, sccp, simplify_cfg};
use crate::{Budget, OptError, Stats};

/// One optimization pass.
///
/// Every pass leaves the function valid, terminates within a bound linear in
/// the function (plus the budgeted parts named below), and reports whether it
/// changed anything.
///
/// # Examples
///
/// ```
/// use opt_lang::PassKind;
///
/// assert_eq!(PassKind::Sccp.name(), "sccp");
/// assert_eq!(PassKind::from_name("simplify-cfg"), Some(PassKind::SimplifyCfg));
/// assert_eq!(PassKind::ALL.len(), 6);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum PassKind {
    /// CFG simplification: fold branches on constants and identical edges,
    /// remove unreachable blocks, thread jumps through empty blocks, merge
    /// straight-line blocks. Linear per round, at most 8 rounds per run.
    SimplifyCfg,
    /// Sparse conditional constant propagation over block parameters, including
    /// `switch` and `check` edges. Linear.
    Sccp,
    /// Copy propagation and block-parameter elimination (a parameter that
    /// always receives the same value is replaced by it). Linear, plus budgeted
    /// re-examination.
    CopyProp,
    /// Dominator-based global value numbering of pure operations, with a few
    /// exact integer identities. Linear.
    Gvn,
    /// Loop-invariant code motion of pure operations into preheaders. Linear
    /// plus the (budgeted) sizes of nested loop bodies.
    Licm,
    /// Dead-code elimination, side-effect aware, including dead block
    /// parameters. Linear.
    Dce,
}

impl PassKind {
    /// Every pass, in a fixed order.
    pub const ALL: [PassKind; 6] = [
        PassKind::SimplifyCfg,
        PassKind::Sccp,
        PassKind::CopyProp,
        PassKind::Gvn,
        PassKind::Licm,
        PassKind::Dce,
    ];

    /// The pass's name (`simplify-cfg`, `sccp`, `copy-prop`, `gvn`, `licm`,
    /// `dce`).
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::PassKind::CopyProp.name(), "copy-prop");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            PassKind::SimplifyCfg => "simplify-cfg",
            PassKind::Sccp => "sccp",
            PassKind::CopyProp => "copy-prop",
            PassKind::Gvn => "gvn",
            PassKind::Licm => "licm",
            PassKind::Dce => "dce",
        }
    }

    /// Looks a pass up by its name.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::PassKind::from_name("gvn"), Some(opt_lang::PassKind::Gvn));
    /// assert_eq!(opt_lang::PassKind::from_name("inline"), None);
    /// ```
    #[must_use]
    pub fn from_name(name: &str) -> Option<PassKind> {
        PassKind::ALL.into_iter().find(|p| p.name() == name)
    }
}

impl fmt::Display for PassKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The default pipeline, run to a fixpoint: simplify the CFG, propagate
/// constants, propagate copies, number values, hoist invariants, delete dead
/// code, and simplify the CFG again.
///
/// # Examples
///
/// ```
/// use opt_lang::{DEFAULT_PIPELINE, PassKind};
///
/// assert_eq!(DEFAULT_PIPELINE.len(), 7);
/// assert_eq!(DEFAULT_PIPELINE[1], PassKind::Sccp);
/// ```
pub const DEFAULT_PIPELINE: &[PassKind] = &[
    PassKind::SimplifyCfg,
    PassKind::Sccp,
    PassKind::CopyProp,
    PassKind::Gvn,
    PassKind::Licm,
    PassKind::Dce,
    PassKind::SimplifyCfg,
];

/// The default number of pipeline sweeps per function.
///
/// # Examples
///
/// ```
/// assert_eq!(opt_lang::DEFAULT_MAX_ITERATIONS, 4);
/// ```
pub const DEFAULT_MAX_ITERATIONS: usize = 4;

/// The default budget per function, in steps per unit of size (instructions +
/// blocks + values). Far above what the linear passes need; it only binds on
/// inputs built to trigger the non-linear parts.
///
/// # Examples
///
/// ```
/// assert_eq!(opt_lang::DEFAULT_STEPS_PER_UNIT, 256);
/// ```
pub const DEFAULT_STEPS_PER_UNIT: u64 = 256;

fn default_budget(func: &ir_lang::Function) -> u64 {
    let units = (func.inst_count() + func.block_count() + func.value_count()) as u64;
    units
        .saturating_mul(DEFAULT_STEPS_PER_UNIT)
        .saturating_add(1 << 16)
}

fn execute(b: &mut Builder<'_>, pass: PassKind, budget: &mut Budget) -> Result<bool, OptError> {
    // Operands are read through forwarding; flattening it first keeps every
    // read O(1) (a no-op scan when there is none).
    b.resolve_aliases();
    let r = match pass {
        PassKind::SimplifyCfg => simplify_cfg::run(b, budget),
        PassKind::Sccp => sccp::run(b, budget),
        PassKind::CopyProp => copy_prop::run(b, budget),
        PassKind::Gvn => gvn::run(b, budget),
        PassKind::Licm => licm::run(b, budget),
        PassKind::Dce => dce::run(b, budget),
    };
    r.map_err(|error| OptError::Build {
        func: b.id(),
        pass,
        error,
    })
}

/// Runs one pass on the function being edited, for callers that build their
/// own pipeline (Tier 3).
///
/// The function is validated first (passes require valid input); after the
/// pass it is validated again in debug builds. Returns whether the pass changed
/// anything. A pass the budget cannot pay for does nothing and returns
/// `Ok(false)`, with [`Budget::is_exhausted`] set.
///
/// # Errors
///
/// [`OptError::InvalidInput`] if the function does not validate (nothing is
/// changed); [`OptError::InvalidOutput`] or [`OptError::Build`] for a defect in
/// a pass.
///
/// # Examples
///
/// ```
/// use ir_lang::{Linkage, Module, Overflow, Signature, Type};
/// use opt_lang::{Budget, PassKind};
///
/// let mut m = Module::new("m");
/// let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
/// let mut b = m.build(f)?;
/// let x = b.param(0)?;
/// let a = b.add(x, x, Overflow::Wrap)?;
/// let again = b.add(x, x, Overflow::Wrap)?; // the same value
/// let y = b.mul(a, again, Overflow::Wrap)?;
/// b.ret(&[y])?;
///
/// let mut budget = Budget::unlimited();
/// assert!(opt_lang::run_pass(&mut m.edit(f)?, PassKind::Gvn, &mut budget)?);
/// assert!(!opt_lang::run_pass(&mut m.edit(f)?, PassKind::Gvn, &mut budget)?);
/// assert!(m.to_string().contains("mul<overflow=wrap> v1, v1"));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn run_pass(
    b: &mut Builder<'_>,
    pass: PassKind,
    budget: &mut Budget,
) -> Result<bool, OptError> {
    b.validate().map_err(|error| OptError::InvalidInput {
        func: b.id(),
        error,
    })?;
    let changed = execute(b, pass, budget)?;
    if changed && cfg!(debug_assertions) {
        b.validate().map_err(|error| OptError::InvalidOutput {
            func: b.id(),
            pass,
            error,
        })?;
    }
    Ok(changed)
}

/// The unit the pass manager runs on: the module, the function being
/// optimized, and the state passes share.
struct Session<'m> {
    module: &'m mut Module,
    func: FuncId,
    budget: Budget,
    validate: bool,
    /// Whether handles may be renumbered (the caller asked for compaction).
    compact: bool,
    failure: Option<OptError>,
    stats: Stats,
}

/// Compacts the function when most of its arena is tombstones, so later passes
/// walk dense tables. Only when the caller allowed renumbering.
fn maybe_compact(b: &mut Builder<'_>) {
    let func = b.func();
    let (insts, blocks) = size(func);
    if func.inst_count() > 2 * insts + 64 || func.block_count() > 2 * blocks + 64 {
        let _ = b.compact();
    }
}

/// A pipeline step: one pass, wrapped for pass-lang, with validation after it.
struct Step(PassKind);

impl Pass<Session<'_>> for Step {
    fn name(&self) -> &'static str {
        self.0.name()
    }

    fn run(&mut self, s: &mut Session<'_>) -> Result<Outcome, PassError> {
        let pass = self.0;
        let func = s.func;
        let result = match s.module.edit(func) {
            Ok(mut b) => execute(&mut b, pass, &mut s.budget).and_then(|changed| {
                if changed && s.validate {
                    b.validate()
                        .map_err(|error| OptError::InvalidOutput { func, pass, error })?;
                }
                if changed && s.compact {
                    maybe_compact(&mut b);
                }
                Ok(changed)
            }),
            Err(e) => Err(OptError::Module(e)),
        };
        match result {
            Ok(changed) => {
                s.stats.record(pass, changed);
                Ok(Outcome::from_changed(changed))
            }
            Err(e) => {
                s.failure = Some(e);
                Err(PassError::new("see the session's typed error"))
            }
        }
    }
}

/// The configured optimizer (Tier 2): which passes, how many sweeps, what
/// budget, and whether to validate between passes.
///
/// # Examples
///
/// ```
/// use ir_lang::{Linkage, Module, Overflow, Signature, Type};
/// use opt_lang::{Optimizer, PassKind};
///
/// let mut m = Module::new("m");
/// let f = m.declare_function("f", &Signature::new(&[Type::I64], &[Type::I64]), Linkage::Export)?;
/// let mut b = m.build(f)?;
/// let x = b.param(0)?;
/// let unused = b.add(x, x, Overflow::Wrap)?;
/// b.ret(&[x])?;
/// # let _ = unused;
///
/// let stats = Optimizer::new()
///     .passes(&[PassKind::Dce])
///     .max_iterations(2)
///     .validate(true)
///     .run(&mut m)?;
/// assert_eq!((stats.insts_before(), stats.insts_after()), (1, 0));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Optimizer {
    passes: Vec<PassKind>,
    max_iterations: usize,
    budget: Option<u64>,
    validate: bool,
    compact: bool,
}

impl Default for Optimizer {
    fn default() -> Self {
        Optimizer::new()
    }
}

impl Optimizer {
    /// The default configuration: [`DEFAULT_PIPELINE`],
    /// [`DEFAULT_MAX_ITERATIONS`] sweeps, a budget of
    /// [`DEFAULT_STEPS_PER_UNIT`] steps per unit of function size, validation
    /// between passes in debug builds only, and compaction of every changed
    /// function.
    ///
    /// # Examples
    ///
    /// ```
    /// let opt = opt_lang::Optimizer::new();
    /// # let _ = opt;
    /// ```
    #[must_use]
    pub fn new() -> Optimizer {
        Optimizer {
            passes: DEFAULT_PIPELINE.to_vec(),
            max_iterations: DEFAULT_MAX_ITERATIONS,
            budget: None,
            validate: cfg!(debug_assertions),
            compact: true,
        }
    }

    /// The passes to run, in order, each sweep. An empty list does nothing.
    ///
    /// # Examples
    ///
    /// ```
    /// use opt_lang::{Optimizer, PassKind};
    ///
    /// let cleanup = Optimizer::new().passes(&[PassKind::Dce, PassKind::SimplifyCfg]);
    /// # let _ = cleanup;
    /// ```
    #[must_use]
    pub fn passes(mut self, passes: &[PassKind]) -> Optimizer {
        self.passes = passes.to_vec();
        self
    }

    /// The most sweeps per function; the pipeline stops earlier at its fixpoint
    /// (a sweep that changes nothing). `0` runs nothing.
    ///
    /// # Examples
    ///
    /// ```
    /// use ir_lang::{Linkage, Module, Signature};
    ///
    /// let mut m = Module::new("m");
    /// let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
    /// m.build(f)?.ret(&[])?;
    /// let stats = opt_lang::Optimizer::new().max_iterations(0).run(&mut m)?;
    /// assert_eq!(stats.iterations(), 0);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn max_iterations(mut self, n: usize) -> Optimizer {
        self.max_iterations = n;
        self
    }

    /// A fixed budget of `steps` per function, instead of the default
    /// size-proportional one.
    ///
    /// # Examples
    ///
    /// ```
    /// use ir_lang::{Linkage, Module, Signature};
    ///
    /// let mut m = Module::new("m");
    /// let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
    /// m.build(f)?.ret(&[])?;
    /// let stats = opt_lang::Optimizer::new().budget(0).run(&mut m)?;
    /// assert_eq!(stats.budget_exhausted(), 1);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn budget(mut self, steps: u64) -> Optimizer {
        self.budget = Some(steps);
        self
    }

    /// Whether to run the ir-lang validator after every pass that changed the
    /// function (default: on in debug builds, off in release builds). The input
    /// is always validated.
    ///
    /// # Examples
    ///
    /// ```
    /// let checked = opt_lang::Optimizer::new().validate(true);
    /// assert_ne!(checked, opt_lang::Optimizer::new().validate(false));
    /// ```
    #[must_use]
    pub fn validate(mut self, on: bool) -> Optimizer {
        self.validate = on;
        self
    }

    /// Whether to compact every changed function at the end (default on):
    /// renumber values, blocks, and instructions densely and drop removed
    /// entities. With it off, handles stay stable and removed entities remain as
    /// tombstones.
    ///
    /// # Examples
    ///
    /// ```
    /// let opt = opt_lang::Optimizer::new().compact(false);
    /// # let _ = opt;
    /// ```
    #[must_use]
    pub fn compact(mut self, on: bool) -> Optimizer {
        self.compact = on;
        self
    }

    /// Optimizes every function with a body.
    ///
    /// # Errors
    ///
    /// [`OptError::InvalidInput`] if a function does not validate (functions
    /// before it are already optimized; it and the ones after are untouched);
    /// [`OptError::InvalidOutput`] or [`OptError::Build`] for a defect in a
    /// pass.
    ///
    /// See [`Optimizer`] for an example.
    pub fn run(&self, module: &mut Module) -> Result<Stats, OptError> {
        let funcs: Vec<FuncId> = module
            .functions()
            .filter(|&f| module.function(f).is_some())
            .collect();
        self.run_on(module, &funcs)
    }

    /// Optimizes one function.
    ///
    /// # Errors
    ///
    /// [`OptError::Module`] if `func` is unknown or has no body; otherwise as
    /// [`run`](Optimizer::run).
    ///
    /// # Examples
    ///
    /// ```
    /// use ir_lang::{Linkage, Module, Signature, Type};
    ///
    /// let mut m = Module::new("m");
    /// let f = m.declare_function("f", &Signature::new(&[], &[Type::U8]), Linkage::Export)?;
    /// let mut b = m.build(f)?;
    /// let v = b.iconst(Type::U8, 7)?;
    /// let _dead = b.iconst(Type::U8, 8)?;
    /// b.ret(&[v])?;
    /// let stats = opt_lang::Optimizer::new().run_function(&mut m, f)?;
    /// assert_eq!(stats.insts_after(), 1);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn run_function(&self, module: &mut Module, func: FuncId) -> Result<Stats, OptError> {
        if module.function(func).is_none() {
            let _ = module.edit(func)?;
        }
        self.run_on(module, &[func])
    }

    fn run_on(&self, module: &mut Module, funcs: &[FuncId]) -> Result<Stats, OptError> {
        let mut total = Stats::default();
        let first = match funcs.first() {
            Some(&f) => f,
            None => return Ok(total),
        };
        let mut pm: PassManager<Session<'_>> = PassManager::new();
        for &p in &self.passes {
            let _ = pm.add(Step(p));
        }
        let mut s = Session {
            module,
            func: first,
            budget: Budget::unlimited(),
            validate: self.validate,
            compact: self.compact,
            failure: None,
            stats: Stats::default(),
        };
        for &f in funcs {
            s.module
                .validate_function(f)
                .map_err(|error| OptError::InvalidInput { func: f, error })?;
            let Some(body) = s.module.function(f) else {
                continue;
            };
            let (insts, blocks) = size(body);
            let steps = self.budget.unwrap_or_else(|| default_budget(body));
            s.func = f;
            s.budget = Budget::new(steps);
            s.stats = Stats::default();
            let report = match pm.run_to_fixpoint(&mut s, self.max_iterations) {
                Ok(r) => r,
                Err(e) => {
                    // A step records its typed error before failing, so the
                    // fallback (naming the failing pass) is never used.
                    return Err(s.failure.take().unwrap_or(OptError::Build {
                        func: f,
                        pass: PassKind::from_name(e.pass()).unwrap_or(PassKind::Dce),
                        error: ir_lang::BuildError::UnknownBlock {
                            block: ir_lang::Block::from_u32(u32::MAX),
                        },
                    }));
                }
            };
            if self.compact && report.changes() > 0 {
                let _ = s.module.edit(f)?.compact();
            }
            let (insts_after, blocks_after) = s.module.function(f).map_or((0, 0), size);
            let mut st = core::mem::take(&mut s.stats);
            st.functions = 1;
            st.insts_before = insts;
            st.blocks_before = blocks;
            st.insts_after = insts_after;
            st.blocks_after = blocks_after;
            st.iterations = report.iterations();
            st.converged = usize::from(report.converged());
            st.budget_exhausted = usize::from(s.budget.is_exhausted());
            total.merge(&st);
        }
        Ok(total)
    }
}
