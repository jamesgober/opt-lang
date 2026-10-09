//! The work budget that bounds every pass.

/// A budget of work steps that every pass draws from.
///
/// A step is one unit of analysis or rewrite work (roughly: one instruction,
/// block, edge, or value visited). Each pass charges its cost before it changes
/// anything; a pass that cannot be paid for does nothing and marks the budget
/// exhausted, so the function is always left valid. Every pass is linear in the
/// function except where noted on [`PassKind`](crate::PassKind), and those
/// non-linear parts (nested loops in LICM, repeated re-examination in copy
/// propagation, hash collisions in GVN) are charged step by step, so a hostile
/// function cannot make optimization take more than `budget` steps.
///
/// # Examples
///
/// ```
/// use opt_lang::Budget;
///
/// let mut b = Budget::new(10);
/// assert_eq!(b.remaining(), 10);
/// assert!(!b.is_exhausted());
/// assert!(Budget::unlimited().remaining() > 1 << 60);
/// # let _ = &mut b;
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Budget {
    remaining: u64,
    exhausted: bool,
}

impl Budget {
    /// A budget of `steps` steps.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::Budget::new(5).remaining(), 5);
    /// ```
    #[must_use]
    pub const fn new(steps: u64) -> Budget {
        Budget {
            remaining: steps,
            exhausted: false,
        }
    }

    /// A budget that never runs out in practice (`u64::MAX` steps).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!opt_lang::Budget::unlimited().is_exhausted());
    /// ```
    #[must_use]
    pub const fn unlimited() -> Budget {
        Budget::new(u64::MAX)
    }

    /// The steps left.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(opt_lang::Budget::new(0).remaining(), 0);
    /// ```
    #[must_use]
    pub const fn remaining(&self) -> u64 {
        self.remaining
    }

    /// Whether a pass was refused (or stopped early) because the budget ran out.
    ///
    /// # Examples
    ///
    /// ```
    /// use ir_lang::{Linkage, Module, Signature};
    /// use opt_lang::{Budget, PassKind};
    ///
    /// let mut m = Module::new("m");
    /// let f = m.declare_function("f", &Signature::new(&[], &[]), Linkage::Export)?;
    /// m.build(f)?.ret(&[])?;
    /// let mut budget = Budget::new(0);
    /// let changed = opt_lang::run_pass(&mut m.edit(f)?, PassKind::Dce, &mut budget)?;
    /// assert!(!changed && budget.is_exhausted());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub const fn is_exhausted(&self) -> bool {
        self.exhausted
    }

    /// Takes `steps` if they are available; otherwise marks the budget exhausted
    /// and returns `false` (taking nothing).
    pub(crate) fn charge(&mut self, steps: u64) -> bool {
        if self.remaining >= steps {
            self.remaining -= steps;
            true
        } else {
            self.exhausted = true;
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_charge_takes_or_refuses() {
        let mut b = Budget::new(10);
        assert!(b.charge(4));
        assert_eq!(b.remaining(), 6);
        assert!(!b.charge(7));
        assert!(b.is_exhausted());
        assert_eq!(b.remaining(), 6);
        assert!(b.charge(6));
        assert_eq!(b.remaining(), 0);
    }
}
