//! Dead-code elimination.
//!
//! A mark-and-sweep over values: everything a side effect, a terminator, or a
//! live block parameter needs is live; the rest is removed. Instructions with
//! side effects ([`InstData::has_side_effects`]: calls, stores, atomics, fences,
//! bulk memory, volatile loads, safepoints, and operations whose policy can trap)
//! are always kept, as are terminators, so `check` error edges, `invoke` unwind
//! edges, and traps are untouched. Block parameters that are only passed around
//! in a cycle without ever being used (a dead loop variable) are removed too,
//! with the matching edge arguments.
//!
//! Cost: linear in instructions, values, and edges; one run reaches the fixpoint.

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{Block, BlockArg, BuildError, Builder, ValueDef};

use crate::Budget;
use crate::analysis::{Cfg, edge};
use crate::edit::{own_operands, remove_params};

/// Runs DCE; returns whether anything was removed.
pub(crate) fn run(b: &mut Builder<'_>, budget: &mut Budget) -> Result<bool, BuildError> {
    let func = b.func();
    let cfg = Cfg::new(func);
    let cost =
        (func.inst_count() + func.value_count() + func.block_count() + cfg.edge_count()) as u64 * 2;
    if !budget.charge(cost) {
        return Ok(false);
    }
    let entry = func.entry();
    let mut live_value = vec![false; func.value_count()];
    let mut live_inst = vec![false; func.inst_count()];
    let mut work: Vec<u32> = Vec::new();

    for block in func.blocks() {
        for inst in func.insts(block) {
            let Some(data) = func.inst(inst) else {
                continue;
            };
            if data.has_side_effects() {
                live_inst[inst.index()] = true;
                data.for_each_operand(|v| work.push(func.resolve(v).as_u32()));
            }
        }
        if let Some(term) = func.terminator(block) {
            own_operands(term, |v| work.push(func.resolve(v).as_u32()));
        }
    }

    while let Some(v) = work.pop() {
        let Some(slot) = live_value.get_mut(v as usize) else {
            continue;
        };
        if *slot {
            continue;
        }
        *slot = true;
        match func.value_def(ir_lang::Value::from_u32(v)) {
            Some(ValueDef::Result { inst, .. }) => {
                if let Some(l) = live_inst.get_mut(inst.index()) {
                    if !*l {
                        *l = true;
                        if let Some(data) = func.inst(inst) {
                            data.for_each_operand(|o| work.push(func.resolve(o).as_u32()));
                        }
                    }
                }
            }
            Some(ValueDef::Param { block, index }) if block != entry => {
                for e in cfg.preds(block.index()) {
                    let Some(term) = func.terminator(Block::from_u32(e.from)) else {
                        continue;
                    };
                    if let Some(dest) = edge(term, e.idx as usize) {
                        if let Some(BlockArg::Value(a)) = dest.args.get(index as usize) {
                            work.push(func.resolve(*a).as_u32());
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // Sweep: dead instructions, then dead parameters.
    let mut dead_insts = Vec::new();
    let mut plans: Vec<(Block, Vec<bool>)> = Vec::new();
    for block in func.blocks() {
        for inst in func.insts(block) {
            if !live_inst[inst.index()] {
                dead_insts.push(inst);
            }
        }
        if block != entry {
            let params = func.block_params(block);
            if params.iter().any(|p| !live_value[p.index()]) {
                let keep = params.iter().map(|p| live_value[p.index()]).collect();
                plans.push((block, keep));
            }
        }
    }
    let changed = !dead_insts.is_empty() || !plans.is_empty();
    for inst in dead_insts {
        b.remove_inst(inst)?;
    }
    remove_params(b, &cfg, &plans)?;
    Ok(changed)
}
