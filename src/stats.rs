//! What an optimization run did.

use crate::pipeline::PassKind;

/// How often one pass ran and how often it changed something.
///
/// # Examples
///
/// ```
/// use ir_lang::{Linkage, Module, Signature, Type};
/// use opt_lang::PassKind;
///
/// let mut m = Module::new("m");
/// let f = m.declare_function("f", &Signature::new(&[], &[Type::I32]), Linkage::Export)?;
/// let mut b = m.build(f)?;
/// let dead = b.iconst(Type::I32, 1)?;
/// let live = b.iconst(Type::I32, 2)?;
/// b.ret(&[live])?;
/// # let _ = dead;
/// let stats = opt_lang::optimize(&mut m)?;
/// let dce = stats.pass(PassKind::Dce);
/// assert!(dce.runs() >= 1 && dce.changes() >= 1);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PassStats {
    kind: PassKind,
    runs: u64,
    changes: u64,
}

impl PassStats {
    /// The pass.
    ///
    /// # Examples
    ///
    /// ```
    /// use opt_lang::{PassKind, Stats};
    ///
    /// assert_eq!(Stats::default().pass(PassKind::Gvn).kind(), PassKind::Gvn);
    /// ```
    #[must_use]
    pub const fn kind(&self) -> PassKind {
        self.kind
    }

    /// How many times it ran (over all functions and iterations).
    ///
    /// # Examples
    ///
    /// ```
    /// use opt_lang::{PassKind, Stats};
    ///
    /// assert_eq!(Stats::default().pass(PassKind::Sccp).runs(), 0);
    /// ```
    #[must_use]
    pub const fn runs(&self) -> u64 {
        self.runs
    }

    /// How many of those runs changed the function.
    ///
    /// # Examples
    ///
    /// ```
    /// use opt_lang::{PassKind, Stats};
    ///
    /// assert_eq!(Stats::default().pass(PassKind::Licm).changes(), 0);
    /// ```
    #[must_use]
    pub const fn changes(&self) -> u64 {
        self.changes
    }
}

/// The result of an optimization run: sizes before and after, iterations, and
/// per-pass counts.
///
/// Sizes count live instructions (terminators excluded) and live blocks.
///
/// # Examples
///
/// ```
/// use ir_lang::{CmpOp, Linkage, Module, Signature, Type};
///
/// // if 1 < 2 { ret 10 } else { ret 20 }: folds to `ret 10`.
/// let mut m = Module::new("m");
/// let f = m.declare_function("f", &Signature::new(&[], &[Type::I32]), Linkage::Export)?;
/// let mut b = m.build(f)?;
/// let (one, two) = (b.iconst(Type::I32, 1)?, b.iconst(Type::I32, 2)?);
/// let c = b.compare(CmpOp::Lt, one, two)?;
/// let (t, e) = (b.create_block(&[])?, b.create_block(&[])?);
/// b.branch(c, t, &[], e, &[])?;
/// b.switch_to(t)?;
/// let ten = b.iconst(Type::I32, 10)?;
/// b.ret(&[ten])?;
/// b.switch_to(e)?;
/// let twenty = b.iconst(Type::I32, 20)?;
/// b.ret(&[twenty])?;
///
/// let stats = opt_lang::optimize(&mut m)?;
/// assert_eq!(stats.functions(), 1);
/// assert_eq!((stats.insts_before(), stats.blocks_before()), (5, 3));
/// assert_eq!((stats.insts_after(), stats.blocks_after()), (1, 1));
/// assert_eq!(stats.converged(), 1);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Stats {
    pub(crate) functions: usize,
    pub(crate) insts_before: usize,
    pub(crate) insts_after: usize,
    pub(crate) blocks_before: usize,
    pub(crate) blocks_after: usize,
    pub(crate) iterations: usize,
    pub(crate) converged: usize,
    pub(crate) budget_exhausted: usize,
    pub(crate) passes: [PassStats; PassKind::ALL.len()],
}

impl Default for Stats {
    fn default() -> Self {
        let mut passes = [PassStats {
            kind: PassKind::Dce,
            runs: 0,
            changes: 0,
        }; PassKind::ALL.len()];
        for (slot, kind) in passes.iter_mut().zip(PassKind::ALL) {
            slot.kind = kind;
        }
        Stats {
            functions: 0,
            insts_before: 0,
            insts_after: 0,
            blocks_before: 0,
            blocks_after: 0,
            iterations: 0,
            converged: 0,
            budget_exhausted: 0,
            passes,
        }
    }
}

impl Stats {
    pub(crate) fn record(&mut self, kind: PassKind, changed: bool) {
        if let Some(p) = self.passes.iter_mut().find(|p| p.kind == kind) {
            p.runs += 1;
            p.changes += u64::from(changed);
        }
    }

    pub(crate) fn merge(&mut self, other: &Stats) {
        self.functions += other.functions;
        self.insts_before += other.insts_before;
        self.insts_after += other.insts_after;
        self.blocks_before += other.blocks_before;
        self.blocks_after += other.blocks_after;
        self.iterations += other.iterations;
        self.converged += other.converged;
        self.budget_exhausted += other.budget_exhausted;
        for (a, b) in self.passes.iter_mut().zip(other.passes.iter()) {
            a.runs += b.runs;
            a.changes += b.changes;
        }
    }

    /// The number of function bodies optimized.
    ///
    /// See [`Stats`] for an example.
    #[must_use]
    pub const fn functions(&self) -> usize {
        self.functions
    }

    /// Live instructions before optimization (terminators excluded).
    ///
    /// See [`Stats`] for an example.
    #[must_use]
    pub const fn insts_before(&self) -> usize {
        self.insts_before
    }

    /// Live instructions after optimization (terminators excluded).
    ///
    /// See [`Stats`] for an example.
    #[must_use]
    pub const fn insts_after(&self) -> usize {
        self.insts_after
    }

    /// Live blocks before optimization.
    ///
    /// See [`Stats`] for an example.
    #[must_use]
    pub const fn blocks_before(&self) -> usize {
        self.blocks_before
    }

    /// Live blocks after optimization.
    ///
    /// See [`Stats`] for an example.
    #[must_use]
    pub const fn blocks_after(&self) -> usize {
        self.blocks_after
    }

    /// Pipeline sweeps run, summed over functions (a sweep runs every pass once).
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::Stats::default().iterations(), 0);
    /// ```
    #[must_use]
    pub const fn iterations(&self) -> usize {
        self.iterations
    }

    /// Functions whose last sweep changed nothing (they reached the pipeline's
    /// fixpoint within the iteration limit).
    ///
    /// See [`Stats`] for an example.
    #[must_use]
    pub const fn converged(&self) -> usize {
        self.converged
    }

    /// Functions where a pass was skipped or cut short because the budget ran
    /// out. Those functions are valid but may be less optimized.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::Stats::default().budget_exhausted(), 0);
    /// ```
    #[must_use]
    pub const fn budget_exhausted(&self) -> usize {
        self.budget_exhausted
    }

    /// The counts of one pass.
    ///
    /// See [`PassStats`] for an example.
    #[must_use]
    pub fn pass(&self, kind: PassKind) -> PassStats {
        self.passes
            .iter()
            .copied()
            .find(|p| p.kind == kind)
            .unwrap_or(PassStats {
                kind,
                runs: 0,
                changes: 0,
            })
    }

    /// The counts of every pass, in [`PassKind::ALL`] order.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::Stats::default().passes().len(), opt_lang::PassKind::ALL.len());
    /// ```
    #[must_use]
    pub fn passes(&self) -> &[PassStats] {
        &self.passes
    }
}
