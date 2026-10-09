//! Copy propagation and block-parameter elimination.
//!
//! A block parameter that receives the same value `v` on every edge from
//! reachable code (ignoring edges that pass the parameter back to itself, as a
//! loop does) is a copy of `v`: its uses are forwarded to `v` and the parameter
//! is removed, with the matching argument on every incoming edge. Replacing one
//! parameter can make others trivial (a parameter fed only by it), so the pass
//! re-examines exactly those, until none is left: the "trivial phi" removal of
//! Braun et al., on block parameters.
//!
//! `v` dominates the block whenever this applies (every first arrival into the
//! block comes along an edge that passes `v`), so the forwarding is valid SSA,
//! and the safepoint rules are unaffected (the parameter and `v` are tracked
//! alike, and their live ranges join at the block boundary).
//!
//! Cost: linear in edge arguments, plus one re-examination of a parameter per
//! replacement among its inputs (charged to the budget step by step; when the
//! budget runs out, the replacements found so far are applied, which is valid).

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{Block, BlockArg, BuildError, Builder, Value, ValueDef};

use crate::Budget;
use crate::analysis::{Cfg, NONE, edge};
use crate::edit::remove_params;

fn find(repl: &mut [u32], v: u32) -> u32 {
    let mut r = v;
    while let Some(&next) = repl.get(r as usize) {
        if next == NONE {
            break;
        }
        r = next;
    }
    let mut x = v;
    while let Some(&next) = repl.get(x as usize) {
        if next == NONE || next == r {
            break;
        }
        repl[x as usize] = r;
        x = next;
    }
    r
}

/// Runs copy propagation; returns whether any parameter was removed.
pub(crate) fn run(b: &mut Builder<'_>, budget: &mut Budget) -> Result<bool, BuildError> {
    let func = b.func();
    let cfg = Cfg::new(func);
    let cost = 2 * (func.value_count() + func.block_count() + cfg.edge_count()) as u64;
    if !budget.charge(cost) {
        return Ok(false);
    }
    let nv = func.value_count();
    let entry = func.entry();
    // Users: for every value, the parameters it is passed to (a linked list per
    // value, so a replaced value's users can be handed to its replacement in
    // O(1)).
    let mut head = vec![NONE; nv];
    let mut tail = vec![NONE; nv];
    let mut user: Vec<u32> = Vec::new();
    let mut next: Vec<u32> = Vec::new();
    let mut params: Vec<u32> = Vec::new();
    for &bl in &cfg.rpo {
        let block = Block::from_u32(bl);
        if block != entry {
            params.extend(func.block_params(block).iter().map(|p| p.as_u32()));
        }
        let Some(term) = func.terminator(block) else {
            continue;
        };
        for dest in term.successors() {
            if dest.block == entry || !cfg.reachable(dest.block.index()) {
                continue;
            }
            let targets = func.block_params(dest.block);
            for (arg, &p) in dest.args.iter().zip(targets) {
                if let BlockArg::Value(v) = arg {
                    let v = func.resolve(*v).index();
                    if v >= nv {
                        continue;
                    }
                    let e = user.len() as u32;
                    user.push(p.as_u32());
                    next.push(NONE);
                    if tail[v] == NONE {
                        head[v] = e;
                    } else {
                        next[tail[v] as usize] = e;
                    }
                    tail[v] = e;
                }
            }
        }
    }
    let mut repl = vec![NONE; nv];
    let mut queued = vec![false; nv];
    let mut work: Vec<u32> = params.iter().rev().copied().collect();
    for &p in &params {
        queued[p as usize] = true;
    }
    let mut any = false;
    while let Some(p) = work.pop() {
        queued[p as usize] = false;
        if repl[p as usize] != NONE {
            continue;
        }
        let Some(ValueDef::Param { block, index }) = func.value_def(Value::from_u32(p)) else {
            continue;
        };
        let preds = cfg.preds(block.index());
        if !budget.charge(preds.len() as u64 + 1) {
            break;
        }
        let mut same = NONE;
        let mut trivial = true;
        for e in preds {
            if !cfg.reachable(e.from as usize) {
                continue;
            }
            let arg = func
                .terminator(Block::from_u32(e.from))
                .and_then(|t| edge(t, e.idx as usize))
                .and_then(|d| d.args.get(index as usize));
            let Some(BlockArg::Value(v)) = arg else {
                trivial = false;
                break;
            };
            let a = find(&mut repl, func.resolve(*v).as_u32());
            if a == p {
                continue;
            }
            if same == NONE {
                same = a;
            } else if same != a {
                trivial = false;
                break;
            }
        }
        if !trivial || same == NONE {
            continue;
        }
        repl[p as usize] = same;
        any = true;
        // Re-examine the parameters `p` was passed to, then hand them to `same`.
        let mut e = head[p as usize];
        while e != NONE {
            let q = user[e as usize];
            if !queued[q as usize] && repl[q as usize] == NONE {
                queued[q as usize] = true;
                work.push(q);
            }
            e = next[e as usize];
        }
        let s = same as usize;
        if head[p as usize] != NONE {
            if tail[s] == NONE {
                head[s] = head[p as usize];
            } else {
                next[tail[s] as usize] = head[p as usize];
            }
            tail[s] = tail[p as usize];
            head[p as usize] = NONE;
            tail[p as usize] = NONE;
        }
    }
    if !any {
        return Ok(false);
    }
    // Apply: forward each replaced parameter to its final value, then remove the
    // parameters (and their arguments) in bulk.
    let mut plans: Vec<(Block, Vec<bool>)> = Vec::new();
    let mut forward: Vec<(Value, Value)> = Vec::new();
    for &bl in &cfg.rpo {
        let block = Block::from_u32(bl);
        if block == entry {
            continue;
        }
        let ps = func.block_params(block);
        if ps.iter().any(|p| repl[p.index()] != NONE) {
            let keep = ps.iter().map(|p| repl[p.index()] == NONE).collect();
            for &p in ps {
                if repl[p.index()] != NONE {
                    forward.push((p, Value::from_u32(find(&mut repl, p.as_u32()))));
                }
            }
            plans.push((block, keep));
        }
    }
    for (p, v) in forward {
        b.replace_all_uses(p, v)?;
    }
    remove_params(b, &cfg, &plans)?;
    Ok(true)
}
