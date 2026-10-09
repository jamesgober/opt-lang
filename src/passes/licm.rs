//! Loop-invariant code motion.
//!
//! Natural loops are found from back edges (an edge into a block that dominates
//! its source); loops sharing a header are one loop. A pure instruction (no side
//! effects, no memory access: the same set GVN numbers) whose operands are all
//! defined outside the loop, or by instructions hoisted before it, is moved to
//! the loop's preheader. Pure instructions never trap or fault, so hoisting one
//! out of a conditionally executed block is safe; loads, calls, and anything
//! with a trapping or raising policy stay where they are. Values of type `ref`
//! and values derived from one are never hoisted (the safepoint rules).
//!
//! A preheader is the loop's single outside predecessor when that block ends in
//! a jump to the header; otherwise one is created (and every edge entering the
//! loop from outside is redirected to it), but only for loops that have
//! something to hoist. Loops entered by an unwind edge are skipped. Inner loops
//! are processed first, so an invariant moves out of every loop it is
//! invariant in.
//!
//! Cost: linear in instructions and edges, plus the sizes of all loop bodies (a
//! block in `d` nested loops is visited `d` times), charged to the budget.

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{Block, BlockCall, BuildError, Builder, ConvOp, Function, InstData, Value};

use crate::Budget;
use crate::analysis::{
    Cfg, DomTree, NONE, def_block, edge_mut, is_tracked, is_unwind_edge, tracked_values,
};
use crate::edit::{move_to_end, rewrite_terminator};

struct Loop {
    header: u32,
    /// Body blocks (header included), in reverse postorder.
    blocks: Vec<u32>,
    depth: u32,
}

struct Analysis {
    cfg: Cfg,
    loops: Vec<Loop>,
    tracked: Option<Vec<bool>>,
}

/// Finds the natural loops; `None` if the budget ran out.
fn analyze(func: &Function, budget: &mut Budget) -> Option<Analysis> {
    let cfg = Cfg::new(func);
    let dom = DomTree::new(&cfg);
    let tracked = tracked_values(func, &cfg);
    // Back edges grouped by header.
    let mut latches: Vec<(u32, u32)> = Vec::new();
    for &t in &cfg.rpo {
        for &h in cfg.succs(t as usize) {
            if dom.dominates(h, t) {
                latches.push((h, t));
            }
        }
    }
    latches.sort_unstable();
    latches.dedup();
    let mut loops = Vec::new();
    let mut stamp = vec![NONE; cfg.len()];
    let mut stack: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < latches.len() {
        let h = latches[i].0;
        let id = loops.len() as u32;
        stamp[h as usize] = id;
        let mut blocks = vec![h];
        while i < latches.len() && latches[i].0 == h {
            let t = latches[i].1;
            i += 1;
            if stamp[t as usize] != id {
                stamp[t as usize] = id;
                blocks.push(t);
                stack.push(t);
            }
        }
        while let Some(x) = stack.pop() {
            let preds = cfg.preds(x as usize);
            if !budget.charge(preds.len() as u64 + 1) {
                return None;
            }
            for e in preds {
                let p = e.from;
                if cfg.reachable(p as usize) && stamp[p as usize] != id {
                    stamp[p as usize] = id;
                    blocks.push(p);
                    stack.push(p);
                }
            }
        }
        blocks.sort_unstable_by_key(|&b| cfg.rpo_index[b as usize]);
        loops.push(Loop {
            header: h,
            blocks,
            depth: dom.depth.get(h as usize).copied().unwrap_or(0),
        });
    }
    // Inner loops (deeper headers) first.
    loops.sort_by(|a, b| b.depth.cmp(&a.depth).then(a.header.cmp(&b.header)));
    Some(Analysis {
        cfg,
        loops,
        tracked,
    })
}

/// Whether an instruction may be hoisted (pure, single result, not tracked).
fn hoistable(tracked: &Option<Vec<bool>>, data: &InstData, r: Value) -> bool {
    if data.has_side_effects() || is_tracked(tracked, r) {
        return false;
    }
    match data {
        InstData::Const { .. }
        | InstData::Unary { .. }
        | InstData::Binary { .. }
        | InstData::Fma { .. }
        | InstData::Compare { .. }
        | InstData::Select { .. }
        | InstData::StackAddr { .. }
        | InstData::GlobalAddr { .. }
        | InstData::FuncAddr { .. }
        | InstData::FieldAddr { .. }
        | InstData::ElemAddr { .. }
        | InstData::PtrOffset { .. } => true,
        InstData::Convert { op, .. } => *op != ConvOp::RefToPtr,
        _ => false,
    }
}

/// The invariant instructions of `lp`, in an order where each comes after the
/// ones it depends on. `stamp` marks the loop's blocks with `id`.
fn candidates(
    func: &Function,
    a: &Analysis,
    lp: &Loop,
    stamp: &mut [u32],
    id: u32,
    hoisted: &mut Vec<bool>,
) -> Vec<ir_lang::Inst> {
    for &b in &lp.blocks {
        stamp[b as usize] = id;
    }
    if hoisted.len() < func.value_count() {
        hoisted.resize(func.value_count(), false);
    }
    let mut out = Vec::new();
    for &b in &lp.blocks {
        for inst in func.insts(Block::from_u32(b)) {
            let Some(data) = func.inst(inst) else {
                continue;
            };
            let results = func.results(inst);
            let Some(r) = results.first() else {
                continue;
            };
            if results.len() != 1 || !hoistable(&a.tracked, data, r) {
                continue;
            }
            let mut invariant = true;
            data.for_each_operand(|v| {
                let v = func.resolve(v);
                let inside =
                    def_block(func, v).is_none_or(|db| stamp.get(db.index()).copied() == Some(id));
                if inside && !hoisted.get(v.index()).copied().unwrap_or(false) {
                    invariant = false;
                }
            });
            if invariant {
                if let Some(h) = hoisted.get_mut(r.index()) {
                    *h = true;
                }
                out.push(inst);
            }
        }
    }
    // Reset the marks for the next loop.
    for &inst in &out {
        if let Some(r) = func.results(inst).first() {
            if let Some(h) = hoisted.get_mut(r.index()) {
                *h = false;
            }
        }
    }
    out
}

/// The loop's preheader if it has one: the single outside predecessor edge
/// comes from a block ending in a jump.
fn existing_preheader(
    func: &Function,
    a: &Analysis,
    lp: &Loop,
    stamp: &[u32],
    id: u32,
) -> Option<Block> {
    let mut found = None;
    for e in a.cfg.preds(lp.header as usize) {
        if !a.cfg.reachable(e.from as usize) || stamp[e.from as usize] == id {
            continue;
        }
        if found.is_some() {
            return None;
        }
        found = Some(e.from);
    }
    let p = Block::from_u32(found?);
    matches!(func.terminator(p), Some(ir_lang::Terminator::Jump(_))).then_some(p)
}

/// Creates a preheader for `lp`, redirecting every reachable outside edge into
/// the header to it. Returns `false` (changing nothing) if an outside edge is an
/// unwind edge.
fn make_preheader(
    b: &mut Builder<'_>,
    a: &Analysis,
    lp: &Loop,
    stamp: &[u32],
    id: u32,
) -> Result<bool, BuildError> {
    let func = b.func();
    let header = Block::from_u32(lp.header);
    let mut sources: Vec<(u32, u32)> = Vec::new();
    for e in a.cfg.preds(lp.header as usize) {
        if !a.cfg.reachable(e.from as usize) || stamp[e.from as usize] == id {
            continue;
        }
        let Some(term) = func.terminator(Block::from_u32(e.from)) else {
            continue;
        };
        if is_unwind_edge(term, e.idx as usize) {
            return Ok(false);
        }
        sources.push((e.from, e.idx));
    }
    if sources.is_empty() {
        return Ok(false);
    }
    let types: Vec<_> = func
        .block_params(header)
        .iter()
        .filter_map(|&p| func.value_type(p))
        .collect();
    let ph = b.create_block(&types)?;
    let args: Vec<Value> = b.func().block_params(ph).to_vec();
    b.switch_to(ph)?;
    b.jump(header, &args)?;
    let mut i = 0;
    while i < sources.len() {
        let from = sources[i].0;
        let mut idxs = Vec::new();
        while i < sources.len() && sources[i].0 == from {
            idxs.push(sources[i].1);
            i += 1;
        }
        rewrite_terminator(b, Block::from_u32(from), |term| {
            for k in idxs {
                if let Some(dest) = edge_mut(term, k as usize) {
                    if dest.block == header {
                        *dest = BlockCall::with_args(ph, &dest.args);
                    }
                }
            }
        })?;
    }
    Ok(true)
}

/// Runs LICM; returns whether anything changed.
pub(crate) fn run(b: &mut Builder<'_>, budget: &mut Budget) -> Result<bool, BuildError> {
    let cost = 3 * (b.func().inst_count() + b.func().block_count() + b.func().value_count()) as u64;
    if !budget.charge(cost) {
        return Ok(false);
    }
    let Some(first) = analyze(b.func(), budget) else {
        return Ok(false);
    };
    if first.loops.is_empty() {
        return Ok(false);
    }
    let n = first.cfg.len();
    let mut stamp = vec![NONE; n];
    let mut hoisted: Vec<bool> = Vec::new();
    // Phase A: give every loop with something to hoist a preheader.
    let mut created = false;
    for (id, lp) in first.loops.iter().enumerate() {
        let id = id as u32;
        let func = b.func();
        if !budget.charge(lp.blocks.len() as u64) {
            return Ok(created);
        }
        if candidates(func, &first, lp, &mut stamp, id, &mut hoisted).is_empty() {
            continue;
        }
        if existing_preheader(func, &first, lp, &stamp, id).is_none() {
            created |= make_preheader(b, &first, lp, &stamp, id)?;
        }
    }
    let a = if created {
        match analyze(b.func(), budget) {
            Some(a) => a,
            None => return Ok(true),
        }
    } else {
        first
    };
    // Phase B: hoist, inner loops first.
    let mut stamp = vec![NONE; a.cfg.len()];
    let mut changed = created;
    for (id, lp) in a.loops.iter().enumerate() {
        let id = id as u32;
        if !budget.charge(lp.blocks.len() as u64) {
            break;
        }
        let func = b.func();
        let cands = candidates(func, &a, lp, &mut stamp, id, &mut hoisted);
        if cands.is_empty() {
            continue;
        }
        let Some(ph) = existing_preheader(func, &a, lp, &stamp, id) else {
            continue;
        };
        for inst in cands {
            let _ = move_to_end(b, inst, ph)?;
        }
        changed = true;
    }
    Ok(changed)
}
