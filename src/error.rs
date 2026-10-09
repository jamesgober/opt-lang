//! The error type of the optimizer.

use core::fmt;

use ir_lang::{BuildError, FuncId, ModuleError, ValidationError};

use crate::pipeline::PassKind;

/// Why optimization stopped.
///
/// Optimizing a valid function never fails: [`OptError::InvalidInput`] means
/// the IR handed in was not valid (nothing was changed), and the other variants
/// mean a pass produced IR the validator rejects, which is a defect in this crate
/// (please report it with the input). A function that runs out of
/// [budget](crate::Budget) is not an error: it is left valid, partly optimized,
/// and counted in [`Stats::budget_exhausted`](crate::Stats::budget_exhausted).
///
/// # Examples
///
/// ```
/// use ir_lang::{FuncId, Module};
/// use opt_lang::OptError;
///
/// let mut m = Module::new("m");
/// let err = opt_lang::Optimizer::new()
///     .run_function(&mut m, FuncId::from_u32(3))
///     .unwrap_err();
/// assert!(matches!(err, OptError::Module(_)));
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum OptError {
    /// The function is unknown or has no body.
    Module(ModuleError),
    /// The function did not validate before optimization; it was left untouched.
    InvalidInput {
        /// The function.
        func: FuncId,
        /// What the validator reported.
        error: ValidationError,
    },
    /// A pass left the function invalid (a defect in this crate). Reported only
    /// when validation between passes is on, which it is by default in debug
    /// builds and tests.
    InvalidOutput {
        /// The function.
        func: FuncId,
        /// The pass that ran last.
        pass: PassKind,
        /// What the validator reported.
        error: ValidationError,
    },
    /// The IR builder refused a rewrite a pass attempted (a defect in this
    /// crate). The function may be partly rewritten.
    Build {
        /// The function.
        func: FuncId,
        /// The pass.
        pass: PassKind,
        /// What the builder reported.
        error: BuildError,
    },
}

impl fmt::Display for OptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OptError::Module(e) => write!(f, "{e}"),
            OptError::InvalidInput { func, error } => {
                write!(f, "function {func} is not valid IR: {error}")
            }
            OptError::InvalidOutput { func, pass, error } => write!(
                f,
                "pass `{}` left function {func} invalid: {error}",
                pass.name()
            ),
            OptError::Build { func, pass, error } => write!(
                f,
                "pass `{}` could not rewrite function {func}: {error}",
                pass.name()
            ),
        }
    }
}

impl core::error::Error for OptError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            OptError::Module(e) => Some(e),
            OptError::InvalidInput { error, .. } | OptError::InvalidOutput { error, .. } => {
                Some(error)
            }
            OptError::Build { error, .. } => Some(error),
        }
    }
}

impl From<ModuleError> for OptError {
    fn from(e: ModuleError) -> Self {
        OptError::Module(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use core::error::Error;

    #[test]
    fn test_display_names_the_pass_and_function() {
        let e = OptError::Build {
            func: FuncId::from_u32(2),
            pass: PassKind::Gvn,
            error: BuildError::CapacityExceeded,
        };
        let text = e.to_string();
        assert!(text.contains("gvn") && text.contains("f2"), "{text}");
        assert!(e.source().is_some());
        let m = OptError::from(ModuleError::NotDefined {
            func: FuncId::from_u32(1),
        });
        assert!(m.source().is_some());
        assert!(!m.to_string().is_empty());
    }
}
