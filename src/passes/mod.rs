//! The optimization passes. Each is `run(&mut Builder, &mut Budget) ->
//! Result<bool, BuildError>`: it returns whether it changed the function, never
//! leaves it invalid, and charges its work to the budget before doing it.

pub(crate) mod copy_prop;
pub(crate) mod dce;
pub(crate) mod gvn;
pub(crate) mod licm;
pub(crate) mod sccp;
pub(crate) mod simplify_cfg;
