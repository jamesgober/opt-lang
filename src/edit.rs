//! Rewrite helpers shared by the passes, built on the ir-lang `Builder`.
//!
//! The two bulk rewrites every optimizer needs come from the builder itself
//! since ir-lang 2.0.0-alpha.2: `move_inst` relinks an instruction in O(1)
//! (handle and results kept), and `remove_block_params` drops any number of
//! parameters, with their edge arguments, in one linear pass. opt-lang 0.2
//! emulated both (re-insert and forward; block rebuilds); see the 0.3.0
//! release notes for the measured difference.

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{
    Block, BuildError, Builder, Call, CallTarget, Function, InstData, Position, Terminator, Type,
    ValidationErrorKind, Value,
};

/// The error for an internal inconsistency the builder would not otherwise
/// report (an instruction without the result it must have).
pub(crate) fn inconsistent() -> BuildError {
    BuildError::Invalid(ValidationErrorKind::ResultMismatch)
}

/// The position at the start of `block` (before its first instruction).
pub(crate) fn block_start(func: &Function, block: Block) -> Position {
    match func.first_inst(block) {
        Some(i) => Position::Before(i),
        None => Position::End(block),
    }
}

/// Inserts `const ty bits` at `pos` and returns its value.
pub(crate) fn constant(
    b: &mut Builder<'_>,
    pos: Position,
    ty: Type,
    bits: u64,
) -> Result<Value, BuildError> {
    b.set_position(pos)?;
    let inst = b.insert(InstData::Const { ty, bits })?;
    b.results(inst).first().ok_or_else(inconsistent)
}

/// Calls `f` on the values a call reads.
fn call_operands(call: &Call, f: &mut impl FnMut(Value)) {
    if let CallTarget::Indirect { callee, .. } = call.target {
        f(callee);
    }
    call.args.iter().copied().for_each(&mut *f);
    call.gc.iter().copied().for_each(f);
}

/// Calls `f` on the values a terminator itself reads (not its edge arguments).
pub(crate) fn own_operands(term: &Terminator, mut f: impl FnMut(Value)) {
    match term {
        Terminator::Branch { cond, .. } => f(*cond),
        Terminator::Switch { value, .. } => f(*value),
        Terminator::Return { values } => values.iter().copied().for_each(f),
        Terminator::TailCall(call) | Terminator::Invoke { call, .. } => {
            call_operands(call, &mut f);
        }
        Terminator::Check { op, .. } => op.for_each_operand(f),
        Terminator::Resume { payload } => f(*payload),
        _ => {}
    }
}

/// The number of uses of every value (through forwarding) in the live blocks:
/// instruction operands, terminator operands, and edge arguments.
pub(crate) fn use_counts(func: &Function) -> Vec<u32> {
    let mut uses = vec![0u32; func.value_count()];
    let mut count = |v: Value| {
        if let Some(u) = uses.get_mut(func.resolve(v).index()) {
            *u = u.saturating_add(1);
        }
    };
    for block in func.blocks() {
        for inst in func.insts(block) {
            if let Some(data) = func.inst(inst) {
                data.for_each_operand(&mut count);
            }
        }
        if let Some(term) = func.terminator(block) {
            term.for_each_operand(&mut count);
        }
    }
    uses
}

/// Takes `block`'s terminator off, lets `f` change it, and puts it back (the
/// builder checks it again).
pub(crate) fn rewrite_terminator(
    b: &mut Builder<'_>,
    block: Block,
    f: impl FnOnce(&mut Terminator),
) -> Result<(), BuildError> {
    let Some(mut term) = b.remove_terminator(block)? else {
        return Ok(());
    };
    f(&mut term);
    b.switch_to(block)?;
    b.set_terminator(term)
}

/// Replaces `block`'s terminator with `term`.
pub(crate) fn replace_terminator(
    b: &mut Builder<'_>,
    block: Block,
    term: Terminator,
) -> Result<(), BuildError> {
    let _ = b.remove_terminator(block)?;
    b.switch_to(block)?;
    b.set_terminator(term)
}

/// Removes block parameters in bulk with the builder's linear
/// `remove_block_params`. `plans` lists, per block (never the entry), which
/// parameters to keep. Every removed parameter must have no remaining use (the
/// caller replaced or proved them dead).
pub(crate) fn remove_params(
    b: &mut Builder<'_>,
    plans: &[(Block, Vec<bool>)],
) -> Result<(), BuildError> {
    let entry = b.func().entry();
    let mut gone: Vec<Value> = Vec::new();
    for (block, keep) in plans {
        if *block == entry || !b.func().is_live_block(*block) {
            continue;
        }
        let params = b.func().block_params(*block);
        gone.extend(
            params
                .iter()
                .zip(keep)
                .filter(|(_, k)| !**k)
                .map(|(p, _)| *p),
        );
    }
    if gone.is_empty() {
        return Ok(());
    }
    b.remove_block_params(&gone)
}
