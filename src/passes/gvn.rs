//! Global value numbering of pure operations (dominator-based).
//!
//! The reachable blocks are walked in dominator-tree pre-order. Each pure
//! instruction (no side effects; constants, arithmetic, comparisons,
//! conversions, `select`, `fma`, and address computation) is keyed by its
//! operation and its operands' value numbers, with commutative integer
//! operations and comparisons put in a canonical operand order. An instruction
//! whose key was already computed in a dominating position is replaced by that
//! earlier value and removed.
//!
//! A few algebraic identities that never change a result or a trap are applied
//! on the way (integers and `bool` only): `x + 0`, `x - 0`, `x * 1`, `x / 1`,
//! `x | 0`, `x ^ 0`, `x & -1`, `x & x`, `x | x`, `min(x, x)`, `max(x, x)`,
//! `x << 0`, `x >> 0`, `not(not(x))`, `select(c, x, x)`, a `bitcast` back to the
//! original type, and a `narrow` of a `zext`/`sext` back to the original type.
//! Float identities are not applied (`x + 0.0` is not `x` for `x = -0.0`).
//!
//! Loads are not numbered (there is no memory dependence analysis yet), nor are
//! values of type `ref` or derived from one (their liveness is constrained by the
//! safepoint rules).
//!
//! Cost: linear in instructions; each hash-table probe looks at no more than a
//! fixed number of colliding entries, so adversarial collisions cannot make the
//! pass quadratic (they only make it miss redundancies).

use alloc::vec;
use alloc::vec::Vec;
use core::hash::{Hash, Hasher};

use ir_lang::{
    BinaryOp, Block, BuildError, Builder, CmpOp, ConvOp, Function, Inst, InstData, Type, UnaryOp,
    Value,
};

use crate::Budget;
use crate::analysis::{Cfg, DomTree, NONE, is_tracked, tracked_values};

/// FxHash: a fast, deterministic hash for the value-number table.
struct Fx(u64);

impl Hasher for Fx {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut w = [0u8; 8];
            w[..chunk.len()].copy_from_slice(chunk);
            self.write_u64(u64::from_le_bytes(w));
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.write_u64(u64::from(i));
    }

    fn write_u32(&mut self, i: u32) {
        self.write_u64(u64::from(i));
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }

    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }
}

/// Probes past this many colliding entries give up (no replacement).
const MAX_PROBE: usize = 16;

struct Entry {
    hash: u64,
    key: InstData,
    value: Value,
    block: u32,
    next: u32,
}

/// Whether an instruction is a candidate for numbering.
fn pure(data: &InstData) -> bool {
    if data.has_side_effects() {
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

/// Union-find style forwarding of planned replacements.
fn find(repl: &mut [u32], v: Value) -> Value {
    let mut r = v.as_u32();
    while let Some(&next) = repl.get(r as usize) {
        if next == NONE {
            break;
        }
        r = next;
    }
    // Path compression.
    let mut x = v.as_u32();
    while let Some(&next) = repl.get(x as usize) {
        if next == NONE || next == r {
            break;
        }
        repl[x as usize] = r;
        x = next;
    }
    Value::from_u32(r)
}

struct Gvn<'f> {
    func: &'f Function,
    repl: Vec<u32>,
}

impl Gvn<'_> {
    fn canon(&mut self, v: Value) -> Value {
        let r = self.func.resolve(v);
        find(&mut self.repl, r)
    }

    fn const_bits(&self, v: Value) -> Option<u64> {
        match self.func.inst(self.func.defining_inst(v)?)? {
            InstData::Const { bits, .. } => Some(*bits),
            _ => None,
        }
    }

    fn def_data(&self, v: Value) -> Option<&InstData> {
        self.func.inst(self.func.defining_inst(v)?)
    }

    /// An existing value the instruction always equals, by an identity.
    fn identity(&mut self, data: &InstData) -> Option<Value> {
        let func = self.func;
        match data {
            InstData::Binary { op, args, .. } => {
                let (a, b) = (args[0], args[1]);
                let ty = func.value_type(a)?;
                if ty == Type::Bool {
                    return match op {
                        BinaryOp::And | BinaryOp::Or if a == b => Some(a),
                        BinaryOp::And if self.const_bits(b) == Some(1) => Some(a),
                        BinaryOp::And if self.const_bits(a) == Some(1) => Some(b),
                        BinaryOp::Or | BinaryOp::Xor if self.const_bits(b) == Some(0) => Some(a),
                        BinaryOp::Or | BinaryOp::Xor if self.const_bits(a) == Some(0) => Some(b),
                        _ => None,
                    };
                }
                if !ty.is_int() {
                    return None;
                }
                let ones = {
                    let w = ty.int_bits().unwrap_or(64);
                    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
                };
                let (ca, cb) = (self.const_bits(a), self.const_bits(b));
                match op {
                    BinaryOp::Add | BinaryOp::Or | BinaryOp::Xor if cb == Some(0) => Some(a),
                    BinaryOp::Add | BinaryOp::Or | BinaryOp::Xor if ca == Some(0) => Some(b),
                    BinaryOp::Sub | BinaryOp::Shl | BinaryOp::Shr if cb == Some(0) => Some(a),
                    BinaryOp::Mul if cb == Some(1) => Some(a),
                    BinaryOp::Mul if ca == Some(1) => Some(b),
                    BinaryOp::Div | BinaryOp::FloorDiv if cb == Some(1) => Some(a),
                    BinaryOp::And if cb == Some(ones) => Some(a),
                    BinaryOp::And if ca == Some(ones) => Some(b),
                    BinaryOp::And | BinaryOp::Or | BinaryOp::Min | BinaryOp::Max if a == b => {
                        Some(a)
                    }
                    _ => None,
                }
            }
            InstData::Unary {
                op: UnaryOp::Not,
                arg,
                ..
            } => match self.def_data(*arg)? {
                InstData::Unary {
                    op: UnaryOp::Not,
                    arg: inner,
                    ..
                } => {
                    let inner = *inner;
                    Some(self.canon(inner))
                }
                _ => None,
            },
            InstData::Select { args, .. } if args[0] == args[1] => Some(args[0]),
            InstData::Convert { op, to, arg, .. } => {
                let inner = match (op, self.def_data(*arg)?) {
                    (
                        ConvOp::Bitcast,
                        InstData::Convert {
                            op: ConvOp::Bitcast,
                            arg: inner,
                            ..
                        },
                    ) => *inner,
                    (
                        ConvOp::Narrow,
                        InstData::Convert {
                            op: ConvOp::Zext | ConvOp::Sext,
                            arg: inner,
                            ..
                        },
                    ) => *inner,
                    _ => return None,
                };
                let inner = self.canon(inner);
                (func.value_type(inner) == Some(*to)).then_some(inner)
            }
            _ => None,
        }
    }
}

/// Puts commutative operands and comparisons into a canonical form.
fn normalize(func: &Function, data: &mut InstData) {
    match data {
        InstData::Binary { op, args, .. } => {
            let ty = func.value_type(args[0]);
            let int_like = ty.is_some_and(|t| t.is_int() || t == Type::Bool);
            let commutes = matches!(
                op,
                BinaryOp::Add
                    | BinaryOp::Mul
                    | BinaryOp::And
                    | BinaryOp::Or
                    | BinaryOp::Xor
                    | BinaryOp::Min
                    | BinaryOp::Max
            );
            if int_like && commutes && args[1] < args[0] {
                args.swap(0, 1);
            }
        }
        InstData::Compare { op, args } => match op {
            CmpOp::Gt => {
                *op = CmpOp::Lt;
                args.swap(0, 1);
            }
            CmpOp::Ge => {
                *op = CmpOp::Le;
                args.swap(0, 1);
            }
            CmpOp::Eq | CmpOp::Ne if args[1] < args[0] => args.swap(0, 1),
            _ => {}
        },
        _ => {}
    }
}

/// Runs GVN; returns whether anything was replaced.
pub(crate) fn run(b: &mut Builder<'_>, budget: &mut Budget) -> Result<bool, BuildError> {
    let func = b.func();
    let cost = 4 * (func.inst_count() + func.value_count() + func.block_count()) as u64;
    if !budget.charge(cost) {
        return Ok(false);
    }
    let cfg = Cfg::new(func);
    let dom = DomTree::new(&cfg);
    let tracked = tracked_values(func, &cfg);
    let mut g = Gvn {
        func,
        repl: vec![NONE; func.value_count()],
    };
    let mut candidates = 0usize;
    for &bl in &dom.preorder {
        candidates += func.insts(Block::from_u32(bl)).count();
    }
    let size = (2 * candidates + 2).next_power_of_two();
    let mask = (size - 1) as u64;
    let mut heads = vec![NONE; size];
    let mut entries: Vec<Entry> = Vec::with_capacity(candidates);
    // (instruction, its result, the value replacing it)
    let mut replaced: Vec<(Inst, Value, Value)> = Vec::new();

    for &bl in &dom.preorder {
        for inst in func.insts(Block::from_u32(bl)) {
            let Some(data) = func.inst(inst) else {
                continue;
            };
            let results = func.results(inst);
            let Some(r) = results.first() else {
                continue;
            };
            if results.len() != 1 || func.resolve(r) != r || is_tracked(&tracked, r) {
                continue;
            }
            // Identities first: they hold for trapping policies too (none of
            // them can overflow or divide by zero), so they also remove
            // instructions the table below must skip.
            let identity_candidate = matches!(
                data,
                InstData::Unary { .. }
                    | InstData::Binary { .. }
                    | InstData::Convert { .. }
                    | InstData::Select { .. }
            );
            if !pure(data) && !identity_candidate {
                continue;
            }
            let mut key = data.clone();
            key.map_operands(|v| g.canon(v));
            if let Some(w) = g.identity(&key) {
                if w != r && func.value_type(w) == func.value_type(r) {
                    g.repl[r.index()] = w.as_u32();
                    replaced.push((inst, r, w));
                    continue;
                }
            }
            if !pure(data) {
                continue;
            }
            normalize(func, &mut key);
            let mut h = Fx(0);
            key.hash(&mut h);
            let hash = h.finish();
            let slot = (hash & mask) as usize;
            let mut idx = heads[slot];
            let mut probes = 0;
            let mut settled = false;
            while idx != NONE && probes < MAX_PROBE {
                probes += 1;
                let e = &mut entries[idx as usize];
                if e.hash == hash && e.key == key {
                    if dom.dominates(e.block, bl) {
                        let leader = e.value;
                        g.repl[r.index()] = leader.as_u32();
                        replaced.push((inst, r, leader));
                    } else {
                        // The earlier entry's subtree is finished: take its place.
                        e.value = r;
                        e.block = bl;
                    }
                    settled = true;
                    break;
                }
                idx = e.next;
            }
            if !settled && probes < MAX_PROBE {
                entries.push(Entry {
                    hash,
                    key,
                    value: r,
                    block: bl,
                    next: heads[slot],
                });
                heads[slot] = (entries.len() - 1) as u32;
            }
        }
    }
    if replaced.is_empty() {
        return Ok(false);
    }
    let mut repl = g.repl;
    for (inst, r, _) in replaced {
        let target = find(&mut repl, r);
        b.replace_all_uses(r, target)?;
        b.remove_inst(inst)?;
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_compresses_paths() {
        let mut repl = vec![1, 2, NONE, NONE];
        assert_eq!(find(&mut repl, Value::from_u32(0)), Value::from_u32(2));
        assert_eq!(repl[0], 2);
        assert_eq!(find(&mut repl, Value::from_u32(3)), Value::from_u32(3));
    }

    #[test]
    fn test_hasher_is_deterministic() {
        let key = InstData::Const {
            ty: Type::I32,
            bits: 7,
        };
        let (mut a, mut b) = (Fx(0), Fx(0));
        key.hash(&mut a);
        key.hash(&mut b);
        assert_eq!(a.finish(), b.finish());
    }
}
