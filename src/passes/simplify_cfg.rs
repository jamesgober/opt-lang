//! Control-flow graph simplification.
//!
//! Each round does, in order:
//!
//! 1. **Fold trivial terminators**: a branch on a constant or with two identical
//!    edges becomes a jump; a switch on a constant becomes a jump; switch cases
//!    that go where the default goes (with the same arguments) are dropped, and a
//!    switch left without cases becomes a jump.
//! 2. **Remove unreachable blocks** (not reachable from the entry).
//! 3. **Thread trivial jumps**: an edge into an empty block that only jumps on
//!    (`b(x): jump c(x, k)`) goes straight to the final target, with the block's
//!    parameters substituted. Chains are followed once each (memoized), and a
//!    cycle of empty blocks is left alone. Unwind edges are never redirected (a
//!    landing pad may only be reached by unwind edges).
//! 4. **Merge blocks**: a block that ends in a jump to a block with no other
//!    predecessor absorbs it.
//!
//! Rounds repeat until nothing changes (at most [`MAX_ROUNDS`]), so one run
//! reaches the pass's fixpoint on all but adversarial inputs. Cost per round:
//! linear in blocks, edges, edge arguments, and moved instructions.

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{
    Block, BlockArg, BlockCall, BuildError, Builder, Function, InstData, Terminator, Value,
    ValueDef,
};

use crate::Budget;
use crate::analysis::{Cfg, NONE, edge_mut, is_unwind_edge};
use crate::edit::{move_to_end, replace_terminator, rewrite_terminator, use_counts};

/// The most rounds one run performs.
pub(crate) const MAX_ROUNDS: usize = 8;

fn round_cost(func: &Function) -> u64 {
    3 * (func.inst_count() + func.block_count() + func.value_count()) as u64 + 16
}

/// Runs CFG simplification; returns whether anything changed.
pub(crate) fn run(b: &mut Builder<'_>, budget: &mut Budget) -> Result<bool, BuildError> {
    let mut changed = false;
    for _ in 0..MAX_ROUNDS {
        if !budget.charge(round_cost(b.func())) {
            break;
        }
        let mut round = fold_terminators(b)?;
        round |= remove_unreachable(b)?;
        round |= thread_jumps(b)?;
        round |= remove_unreachable(b)?;
        round |= merge_blocks(b)?;
        if !round {
            break;
        }
        changed = true;
    }
    Ok(changed)
}

/// The constant bits of `v`, if it is defined by a `const`.
fn const_bits(func: &Function, v: Value) -> Option<u64> {
    match func.inst(func.defining_inst(func.resolve(v))?)? {
        InstData::Const { bits, .. } => Some(*bits),
        _ => None,
    }
}

/// Whether two edges are the same (target and arguments, through forwarding).
fn same_edge(func: &Function, a: &BlockCall, b: &BlockCall) -> bool {
    a.block == b.block
        && a.args.len() == b.args.len()
        && a.args.iter().zip(&b.args).all(|(x, y)| match (x, y) {
            (BlockArg::Value(x), BlockArg::Value(y)) => func.resolve(*x) == func.resolve(*y),
            _ => x == y,
        })
}

fn fold_terminators(b: &mut Builder<'_>) -> Result<bool, BuildError> {
    let func = b.func();
    let mut plans: Vec<(Block, Terminator)> = Vec::new();
    for block in func.blocks() {
        let Some(term) = func.terminator(block) else {
            continue;
        };
        match term {
            Terminator::Branch {
                cond,
                then_dest,
                else_dest,
            } => {
                if let Some(c) = const_bits(func, *cond) {
                    let dest = if c & 1 == 1 { then_dest } else { else_dest };
                    plans.push((block, Terminator::Jump(dest.clone())));
                } else if same_edge(func, then_dest, else_dest) {
                    plans.push((block, Terminator::Jump(then_dest.clone())));
                }
            }
            Terminator::Switch {
                value,
                cases,
                default,
            } => {
                if let Some(c) = const_bits(func, *value) {
                    let dest = cases
                        .iter()
                        .find(|k| k.value == c)
                        .map_or(default, |k| &k.dest);
                    plans.push((block, Terminator::Jump(dest.clone())));
                } else if cases.iter().any(|k| same_edge(func, &k.dest, default)) {
                    let kept: Vec<_> = cases
                        .iter()
                        .filter(|k| !same_edge(func, &k.dest, default))
                        .cloned()
                        .collect();
                    let t = if kept.is_empty() {
                        Terminator::Jump(default.clone())
                    } else {
                        Terminator::Switch {
                            value: *value,
                            cases: kept,
                            default: default.clone(),
                        }
                    };
                    plans.push((block, t));
                } else if cases.is_empty() {
                    plans.push((block, Terminator::Jump(default.clone())));
                }
            }
            _ => {}
        }
    }
    let changed = !plans.is_empty();
    for (block, term) in plans {
        replace_terminator(b, block, term)?;
    }
    Ok(changed)
}

fn remove_unreachable(b: &mut Builder<'_>) -> Result<bool, BuildError> {
    let func = b.func();
    let cfg = Cfg::new(func);
    let dead: Vec<Block> = func
        .blocks()
        .filter(|bl| !cfg.reachable(bl.index()))
        .collect();
    let changed = !dead.is_empty();
    for block in dead {
        b.remove_block(block)?;
    }
    Ok(changed)
}

/// Where an empty forwarding block finally sends control: the target and the
/// arguments, expressed in the forwarder's own parameters (and outer values).
#[derive(Clone)]
struct Forward {
    target: Block,
    args: Vec<BlockArg>,
}

/// `args` with every parameter of `block` replaced by the matching `actual`.
fn substitute(
    func: &Function,
    block: Block,
    args: &[BlockArg],
    actual: &[BlockArg],
) -> Vec<BlockArg> {
    args.iter()
        .map(|a| match a {
            BlockArg::Value(v) => match func.value_def(func.resolve(*v)) {
                Some(ValueDef::Param { block: pb, index }) if pb == block => {
                    actual.get(index as usize).copied().unwrap_or(*a)
                }
                _ => BlockArg::Value(func.resolve(*v)),
            },
            other => *other,
        })
        .collect()
}

fn thread_jumps(b: &mut Builder<'_>) -> Result<bool, BuildError> {
    let func = b.func();
    let cfg = Cfg::new(func);
    let n = func.block_count();
    let entry = func.entry();
    // A forwarder: not the entry, reachable, no instructions, a jump elsewhere,
    // not entered by an unwind edge, and its parameters used only by its own
    // jump (a parameter can be used further down, in blocks it dominates; such
    // a block cannot be bypassed).
    let uses = use_counts(func);
    let mut forwarder = vec![false; n];
    for &bl in &cfg.rpo {
        let block = Block::from_u32(bl);
        if block == entry || func.first_inst(block).is_some() {
            continue;
        }
        let Some(Terminator::Jump(dest)) = func.terminator(block) else {
            continue;
        };
        if dest.block == block {
            continue;
        }
        let local_only = func.block_params(block).iter().all(|&p| {
            let here = dest
                .args
                .iter()
                .filter(|a| matches!(a, BlockArg::Value(v) if func.resolve(*v) == p))
                .count();
            uses.get(p.index()).copied().unwrap_or(0) as usize == here
        });
        if !local_only {
            continue;
        }
        let landing = cfg.preds(bl as usize).iter().any(|e| {
            func.terminator(Block::from_u32(e.from))
                .is_some_and(|t| is_unwind_edge(t, e.idx as usize))
        });
        if !landing {
            forwarder[bl as usize] = true;
        }
    }
    // Resolve every forwarder's final target, following chains iteratively.
    // 0 = unresolved, 1 = in progress, 2 = resolved.
    let mut state = vec![0u8; n];
    let mut fwd: Vec<Option<Forward>> = vec![None; n];
    let mut chain: Vec<u32> = Vec::new();
    for start in 0..n {
        if !forwarder[start] || state[start] != 0 {
            continue;
        }
        chain.clear();
        let mut cur = start as u32;
        loop {
            state[cur as usize] = 1;
            chain.push(cur);
            let Some(Terminator::Jump(dest)) = func.terminator(Block::from_u32(cur)) else {
                break;
            };
            let next = dest.block.as_u32();
            if forwarder.get(next as usize).copied().unwrap_or(false) && state[next as usize] == 0 {
                cur = next;
            } else {
                break;
            }
        }
        // Unwind the chain: the last forwarder jumps to a non-forwarder, a
        // resolved forwarder, or one in progress (a cycle).
        while let Some(x) = chain.pop() {
            let block = Block::from_u32(x);
            let Some(Terminator::Jump(dest)) = func.terminator(block) else {
                state[x as usize] = 2;
                continue;
            };
            let next = dest.block.as_u32();
            let own = Forward {
                target: dest.block,
                args: dest
                    .args
                    .iter()
                    .map(|a| match a {
                        BlockArg::Value(v) => BlockArg::Value(func.resolve(*v)),
                        other => *other,
                    })
                    .collect(),
            };
            let f = match (state.get(next as usize), fwd.get(next as usize)) {
                (Some(2), Some(Some(nf))) if forwarder[next as usize] => Forward {
                    target: nf.target,
                    args: substitute(func, dest.block, &nf.args, &own.args),
                },
                _ => own,
            };
            fwd[x as usize] = Some(f);
            state[x as usize] = 2;
        }
    }
    // Redirect edges from reachable blocks into forwarders.
    let mut plans: Vec<(Block, Vec<(usize, BlockCall)>)> = Vec::new();
    for &bl in &cfg.rpo {
        let block = Block::from_u32(bl);
        let Some(term) = func.terminator(block) else {
            continue;
        };
        let mut edits = Vec::new();
        for (k, dest) in term.successors().enumerate() {
            if is_unwind_edge(term, k)
                || !forwarder.get(dest.block.index()).copied().unwrap_or(false)
            {
                continue;
            }
            let Some(Some(f)) = fwd.get(dest.block.index()) else {
                continue;
            };
            if f.target == dest.block || f.target == entry {
                continue;
            }
            let args = substitute(func, dest.block, &f.args, &dest.args);
            edits.push((k, BlockCall::with_args(f.target, &args)));
        }
        if !edits.is_empty() {
            plans.push((block, edits));
        }
    }
    let changed = !plans.is_empty();
    for (block, edits) in plans {
        rewrite_terminator(b, block, |term| {
            for (k, new) in edits {
                if let Some(slot) = edge_mut(term, k) {
                    *slot = new;
                }
            }
        })?;
    }
    Ok(changed)
}

fn merge_blocks(b: &mut Builder<'_>) -> Result<bool, BuildError> {
    let (rpo, pred_count, entry) = {
        let func = b.func();
        let cfg = Cfg::new(func);
        let counts: Vec<u32> = (0..cfg.len()).map(|i| cfg.preds(i).len() as u32).collect();
        (cfg.rpo.clone(), counts, func.entry())
    };
    let mut changed = false;
    for bl in rpo {
        let block = Block::from_u32(bl);
        // Absorb successors while the block ends in a jump to a block it alone
        // reaches.
        loop {
            let func = b.func();
            if !func.is_live_block(block) {
                break;
            }
            let Some(Terminator::Jump(dest)) = func.terminator(block) else {
                break;
            };
            let next = dest.block;
            if next == block
                || next == entry
                || !func.is_live_block(next)
                || pred_count.get(next.index()).copied().unwrap_or(NONE) != 1
            {
                break;
            }
            let args: Vec<BlockArg> = dest.args.clone();
            let params: Vec<Value> = func.block_params(next).to_vec();
            let insts: Vec<_> = func.insts(next).collect();
            for (p, a) in params.iter().zip(&args) {
                if let BlockArg::Value(v) = a {
                    b.replace_all_uses(*p, *v)?;
                }
            }
            let _ = b.remove_terminator(block)?;
            for inst in insts {
                let _ = move_to_end(b, inst, block)?;
            }
            if let Some(term) = b.remove_terminator(next)? {
                b.switch_to(block)?;
                b.set_terminator(term)?;
            }
            b.remove_block(next)?;
            changed = true;
        }
    }
    Ok(changed)
}
