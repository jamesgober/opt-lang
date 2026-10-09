//! Rewrite helpers shared by the passes, built on the ir-lang `Builder`.
//!
//! The builder has no "move instruction" operation and its
//! `remove_block_param` costs time linear in the number of blocks, so the two
//! rewrites every optimizer needs in bulk are provided here in linear time:
//! moving an instruction (re-inserting a copy and forwarding its results) and
//! removing many block parameters at once (rebuilding the block when the count
//! is large).

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{
    Block, BuildError, Builder, Call, CallTarget, Function, Inst, InstData, Position, Terminator,
    Type, ValidationErrorKind, Value,
};

use crate::analysis::{Cfg, EdgeRef, edge_mut};

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

/// A copy of `inst`'s data with every operand resolved through forwarding.
pub(crate) fn resolved_data(func: &Function, inst: Inst) -> Option<InstData> {
    let mut data = func.inst(inst)?.clone();
    data.map_operands(|v| func.resolve(v));
    Some(data)
}

/// Moves `inst` to the end of `block` (before its terminator): a copy is
/// inserted there, the old results forward to the new ones, and the old
/// instruction is removed. Returns the new instruction.
pub(crate) fn move_to_end(
    b: &mut Builder<'_>,
    inst: Inst,
    block: Block,
) -> Result<Inst, BuildError> {
    let data = resolved_data(b.func(), inst).ok_or(BuildError::UnknownInst { inst })?;
    b.set_position(Position::End(block))?;
    let new = b.insert(data)?;
    let (old_r, new_r) = (b.results(inst), b.results(new));
    for (o, n) in old_r.iter().zip(new_r.iter()) {
        b.replace_all_uses(o, n)?;
    }
    b.remove_inst(inst)?;
    Ok(new)
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

/// Removing at most this many parameters in a function uses the builder's
/// `remove_block_param` (linear in the blocks per call); more rebuilds the
/// blocks, which is linear in the edges and moved instructions overall.
const IN_PLACE_LIMIT: usize = 16;

/// Removes block parameters in bulk. `plans` lists, per block (never the entry),
/// which parameters to keep. Every removed parameter must have no remaining use
/// (the caller replaced or proved them dead). `cfg` must describe the function
/// as it is now.
pub(crate) fn remove_params(
    b: &mut Builder<'_>,
    cfg: &Cfg,
    plans: &[(Block, Vec<bool>)],
) -> Result<(), BuildError> {
    let removed: usize = plans
        .iter()
        .map(|(_, keep)| keep.iter().filter(|&&k| !k).count())
        .sum();
    if removed == 0 {
        return Ok(());
    }
    let entry = b.func().entry();
    if removed <= IN_PLACE_LIMIT {
        for (block, keep) in plans {
            if *block == entry {
                continue;
            }
            for idx in (0..keep.len()).rev() {
                if !keep[idx] {
                    b.remove_block_param(*block, idx)?;
                }
            }
        }
        return Ok(());
    }
    // Where each original block's terminator lives now (a rebuilt block's moved
    // to its replacement).
    let mut home: Vec<u32> = (0..b.func().block_count() as u32).collect();
    let mut group: Vec<EdgeRef> = Vec::new();
    for (block, keep) in plans {
        let block = *block;
        if block == entry || !b.func().is_live_block(block) {
            continue;
        }
        let params: Vec<Value> = b.func().block_params(block).to_vec();
        // Move the body and the terminator to a fresh block.
        let new = match b.func().first_inst(block) {
            Some(first) => b.split_block(first)?,
            None => {
                let new = b.create_block(&[])?;
                if let Some(term) = b.remove_terminator(block)? {
                    b.switch_to(new)?;
                    b.set_terminator(term)?;
                }
                new
            }
        };
        if let Some(h) = home.get_mut(block.index()) {
            *h = new.as_u32();
        }
        for (k, &p) in params.iter().enumerate() {
            if keep.get(k).copied().unwrap_or(true) {
                let ty = b
                    .func()
                    .value_type(p)
                    .ok_or(BuildError::UnknownValue { value: p })?;
                let q = b.add_block_param(new, ty)?;
                b.replace_all_uses(p, q)?;
            }
        }
        // Retarget every incoming edge, one terminator rewrite per source block.
        let preds = cfg.preds(block.index());
        let mut i = 0;
        while i < preds.len() {
            let from = preds[i].from;
            group.clear();
            while i < preds.len() && preds[i].from == from {
                group.push(preds[i]);
                i += 1;
            }
            let src = Block::from_u32(home.get(from as usize).copied().unwrap_or(from));
            if !b.func().is_live_block(src) {
                continue;
            }
            rewrite_terminator(b, src, |term| {
                for e in &group {
                    if let Some(dest) = edge_mut(term, e.idx as usize) {
                        if dest.block == block {
                            dest.block = new;
                            let mut k = 0;
                            dest.args.retain(|_| {
                                let kept = keep.get(k).copied().unwrap_or(true);
                                k += 1;
                                kept
                            });
                        }
                    }
                }
            })?;
        }
        b.remove_block(block)?;
    }
    Ok(())
}
