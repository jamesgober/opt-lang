//! Function analyses shared by the passes: the control-flow graph with its
//! edges, reachability and reverse postorder, the dominator tree, and the set of
//! values the safepoint rules track.
//!
//! Every analysis is a dense table indexed by handle, built in time linear in the
//! function (the dominator tree in `O(E log V)`), iteratively, so a deep or wide
//! function cannot overflow the stack.

use alloc::vec;
use alloc::vec::Vec;

use ir_lang::{
    Block, BlockArg, BlockCall, ConvOp, Function, InstData, Terminator, Type, Value, ValueDef,
};

/// "No entity" in the dense tables.
pub(crate) const NONE: u32 = u32::MAX;

/// The `idx`-th outgoing edge of a terminator, in [`Terminator::successors`]
/// order (switch cases, then the default; then/else; normal, then unwind/error).
pub(crate) fn edge(term: &Terminator, idx: usize) -> Option<&BlockCall> {
    match term {
        Terminator::Jump(c) => (idx == 0).then_some(c),
        Terminator::Branch {
            then_dest,
            else_dest,
            ..
        } => match idx {
            0 => Some(then_dest),
            1 => Some(else_dest),
            _ => None,
        },
        Terminator::Switch { cases, default, .. } => match idx.cmp(&cases.len()) {
            core::cmp::Ordering::Less => cases.get(idx).map(|c| &c.dest),
            core::cmp::Ordering::Equal => Some(default),
            core::cmp::Ordering::Greater => None,
        },
        Terminator::Invoke { normal, unwind, .. } => match idx {
            0 => Some(normal),
            1 => Some(unwind),
            _ => None,
        },
        Terminator::Check { normal, error, .. } => match idx {
            0 => Some(normal),
            1 => Some(error),
            _ => None,
        },
        _ => None,
    }
}

/// Mutable access to the `idx`-th outgoing edge.
pub(crate) fn edge_mut(term: &mut Terminator, idx: usize) -> Option<&mut BlockCall> {
    match term {
        Terminator::Jump(c) => (idx == 0).then_some(c),
        Terminator::Branch {
            then_dest,
            else_dest,
            ..
        } => match idx {
            0 => Some(then_dest),
            1 => Some(else_dest),
            _ => None,
        },
        Terminator::Switch { cases, default, .. } => {
            let n = cases.len();
            match idx.cmp(&n) {
                core::cmp::Ordering::Less => cases.get_mut(idx).map(|c| &mut c.dest),
                core::cmp::Ordering::Equal => Some(default),
                core::cmp::Ordering::Greater => None,
            }
        }
        Terminator::Invoke { normal, unwind, .. } => match idx {
            0 => Some(normal),
            1 => Some(unwind),
            _ => None,
        },
        Terminator::Check { normal, error, .. } => match idx {
            0 => Some(normal),
            1 => Some(error),
            _ => None,
        },
        _ => None,
    }
}

/// Whether the `idx`-th edge of `term` is an exception (unwind) edge. Those are
/// never redirected: a landing pad may only be reached by unwind edges.
pub(crate) fn is_unwind_edge(term: &Terminator, idx: usize) -> bool {
    matches!(term, Terminator::Invoke { .. }) && idx == 1
}

/// One control-flow edge: the `idx`-th successor of `from`'s terminator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct EdgeRef {
    pub(crate) from: u32,
    pub(crate) idx: u32,
}

/// The control-flow graph of the live blocks.
pub(crate) struct Cfg {
    /// Successor block of every edge, grouped by source (`succ_start`).
    succ_start: Vec<u32>,
    succ: Vec<u32>,
    /// Incoming edges of every block (from every live block), grouped by target.
    pred_start: Vec<u32>,
    preds: Vec<EdgeRef>,
    /// Reachable blocks in reverse postorder from the entry.
    pub(crate) rpo: Vec<u32>,
    /// Position of each block in `rpo`, or `NONE` if unreachable (or removed).
    pub(crate) rpo_index: Vec<u32>,
}

impl Cfg {
    /// Builds the graph of `func`. Cost: linear in blocks and edges.
    pub(crate) fn new(func: &Function) -> Cfg {
        let n = func.block_count();
        let mut succ_start = vec![0u32; n + 1];
        let mut succ = Vec::new();
        let mut in_count = vec![0u32; n + 1];
        for b in 0..n {
            let block = Block::from_u32(b as u32);
            if func.is_live_block(block) {
                if let Some(term) = func.terminator(block) {
                    for dest in term.successors() {
                        let t = dest.block.as_u32();
                        succ.push(t);
                        if let Some(c) = in_count.get_mut(t as usize + 1) {
                            *c += 1;
                        }
                    }
                }
            }
            succ_start[b + 1] = succ.len() as u32;
        }
        for i in 0..n {
            in_count[i + 1] += in_count[i];
        }
        let mut fill = in_count.clone();
        let mut preds = vec![EdgeRef { from: 0, idx: 0 }; succ.len()];
        for b in 0..n {
            let (lo, hi) = (succ_start[b] as usize, succ_start[b + 1] as usize);
            for (k, &t) in succ[lo..hi].iter().enumerate() {
                if let Some(slot) = fill.get_mut(t as usize) {
                    if let Some(p) = preds.get_mut(*slot as usize) {
                        *p = EdgeRef {
                            from: b as u32,
                            idx: k as u32,
                        };
                    }
                    *slot += 1;
                }
            }
        }
        let mut cfg = Cfg {
            succ_start,
            succ,
            pred_start: in_count,
            preds,
            rpo: Vec::new(),
            rpo_index: vec![NONE; n],
        };
        cfg.compute_rpo(func.entry().index());
        cfg
    }

    fn compute_rpo(&mut self, entry: usize) {
        let n = self.rpo_index.len();
        if entry >= n {
            return;
        }
        let mut visited = vec![false; n];
        let mut post = Vec::with_capacity(n);
        // (block, next successor position)
        let mut stack: Vec<(u32, u32)> = vec![(entry as u32, 0)];
        visited[entry] = true;
        while let Some(top) = stack.last_mut() {
            let (b, k) = *top;
            let succs = self.succs(b as usize);
            if let Some(&s) = succs.get(k as usize) {
                top.1 += 1;
                if let Some(v) = visited.get_mut(s as usize) {
                    if !*v {
                        *v = true;
                        stack.push((s, 0));
                    }
                }
            } else {
                post.push(b);
                let _ = stack.pop();
            }
        }
        post.reverse();
        for (i, &b) in post.iter().enumerate() {
            self.rpo_index[b as usize] = i as u32;
        }
        self.rpo = post;
    }

    /// The number of block handles covered.
    pub(crate) fn len(&self) -> usize {
        self.rpo_index.len()
    }

    /// The successor blocks of `b`, one per edge, in edge order.
    pub(crate) fn succs(&self, b: usize) -> &[u32] {
        let lo = self.succ_start.get(b).copied().unwrap_or(0) as usize;
        let hi = self.succ_start.get(b + 1).copied().unwrap_or(0) as usize;
        self.succ.get(lo..hi).unwrap_or(&[])
    }

    /// The incoming edges of `b` from every live block.
    pub(crate) fn preds(&self, b: usize) -> &[EdgeRef] {
        let lo = self.pred_start.get(b).copied().unwrap_or(0) as usize;
        let hi = self.pred_start.get(b + 1).copied().unwrap_or(0) as usize;
        self.preds.get(lo..hi).unwrap_or(&[])
    }

    /// Whether `b` is reachable from the entry.
    pub(crate) fn reachable(&self, b: usize) -> bool {
        self.rpo_index.get(b).is_some_and(|&i| i != NONE)
    }

    /// The total number of edges.
    pub(crate) fn edge_count(&self) -> usize {
        self.succ.len()
    }
}

/// The dominator tree of the reachable blocks.
pub(crate) struct DomTree {
    /// Pre-order and post-order numbers in the tree, for O(1) dominance tests.
    pre: Vec<u32>,
    post: Vec<u32>,
    /// Reachable blocks in dominator-tree pre-order (children by RPO).
    pub(crate) preorder: Vec<u32>,
    /// Depth of each block in the tree (entry 0).
    pub(crate) depth: Vec<u32>,
}

impl DomTree {
    /// Lengauer–Tarjan with path compression, iterative: `O(E log V)`.
    pub(crate) fn new(cfg: &Cfg) -> DomTree {
        let n = cfg.len();
        let mut idom = vec![NONE; n];
        // DFS numbering over reachable blocks: the RPO is a valid DFS order for
        // parents only if taken from a DFS; recompute a DFS preorder here.
        let entry = cfg.rpo.first().copied();
        let mut dfnum = vec![NONE; n];
        let mut vertex: Vec<u32> = Vec::new();
        let mut parent: Vec<u32> = Vec::new();
        if let Some(entry) = entry {
            let mut stack: Vec<(u32, u32)> = vec![(entry, NONE)];
            while let Some((b, p)) = stack.pop() {
                if dfnum[b as usize] != NONE {
                    continue;
                }
                dfnum[b as usize] = vertex.len() as u32;
                vertex.push(b);
                parent.push(p);
                let succs = cfg.succs(b as usize);
                for &s in succs.iter().rev() {
                    if dfnum.get(s as usize).is_some_and(|&d| d == NONE) {
                        stack.push((s, dfnum[b as usize]));
                    }
                }
            }
        }
        // `parent` holds the DFS number of the parent at push time; a block pushed
        // twice keeps the parent of the push that numbered it, which is the one
        // popped first, and that is a valid DFS-tree parent.
        let m = vertex.len();
        let mut semi: Vec<u32> = (0..m as u32).collect();
        let mut label: Vec<u32> = (0..m as u32).collect();
        let mut ancestor = vec![NONE; m];
        let mut dom = vec![NONE; m];
        let mut bucket_head = vec![NONE; m];
        let mut bucket_next = vec![NONE; m];
        let mut path: Vec<u32> = Vec::new();

        // eval(v): the vertex with minimal semi on the compressed ancestor path.
        let eval = |v: u32,
                    ancestor: &mut Vec<u32>,
                    label: &mut Vec<u32>,
                    semi: &Vec<u32>,
                    path: &mut Vec<u32>|
         -> u32 {
            if ancestor[v as usize] == NONE {
                return v;
            }
            // Collect the path up to the root of v's tree in the forest.
            path.clear();
            let mut u = v;
            while ancestor[u as usize] != NONE && ancestor[ancestor[u as usize] as usize] != NONE {
                path.push(u);
                u = ancestor[u as usize];
            }
            // Compress from the top down.
            while let Some(w) = path.pop() {
                let a = ancestor[w as usize];
                if semi[label[a as usize] as usize] < semi[label[w as usize] as usize] {
                    label[w as usize] = label[a as usize];
                }
                ancestor[w as usize] = ancestor[a as usize];
            }
            label[v as usize]
        };

        for w in (1..m).rev() {
            let wb = vertex[w] as usize;
            for e in cfg.preds(wb) {
                let v = dfnum.get(e.from as usize).copied().unwrap_or(NONE);
                if v == NONE {
                    continue; // unreachable predecessor
                }
                let u = eval(v, &mut ancestor, &mut label, &semi, &mut path);
                if semi[u as usize] < semi[w] {
                    semi[w] = semi[u as usize];
                }
            }
            let s = semi[w] as usize;
            bucket_next[w] = bucket_head[s];
            bucket_head[s] = w as u32;
            let p = parent[w];
            ancestor[w] = p;
            // Process the bucket of the parent.
            let mut v = bucket_head[p as usize];
            bucket_head[p as usize] = NONE;
            while v != NONE {
                let next = bucket_next[v as usize];
                let u = eval(v, &mut ancestor, &mut label, &semi, &mut path);
                dom[v as usize] = if semi[u as usize] < semi[v as usize] {
                    u
                } else {
                    p
                };
                v = next;
            }
        }
        for w in 1..m {
            if dom[w] != semi[w] {
                dom[w] = dom[dom[w] as usize];
            }
        }
        for w in 1..m {
            idom[vertex[w] as usize] = vertex[dom[w] as usize];
        }

        // Children lists (ordered by RPO) for the tree walks.
        let mut child_count = vec![0u32; n + 1];
        for &b in &cfg.rpo {
            let d = idom[b as usize];
            if d != NONE {
                child_count[d as usize + 1] += 1;
            }
        }
        for i in 0..n {
            child_count[i + 1] += child_count[i];
        }
        let mut fill = child_count.clone();
        let mut children = vec![0u32; m.saturating_sub(1)];
        for &b in &cfg.rpo {
            let d = idom[b as usize];
            if d != NONE {
                let slot = &mut fill[d as usize];
                if let Some(c) = children.get_mut(*slot as usize) {
                    *c = b;
                }
                *slot += 1;
            }
        }
        let mut pre = vec![NONE; n];
        let mut post = vec![NONE; n];
        let mut depth = vec![0u32; n];
        let mut preorder = Vec::with_capacity(m);
        if let Some(entry) = entry {
            let (mut pc, mut qc) = (0u32, 0u32);
            let mut stack: Vec<(u32, u32)> = vec![(entry, 0)];
            pre[entry as usize] = pc;
            pc += 1;
            preorder.push(entry);
            while let Some(top) = stack.last_mut() {
                let (b, k) = *top;
                let lo = child_count[b as usize] + k;
                if lo < child_count[b as usize + 1] {
                    top.1 += 1;
                    let c = children[lo as usize];
                    pre[c as usize] = pc;
                    pc += 1;
                    depth[c as usize] = depth[b as usize] + 1;
                    preorder.push(c);
                    stack.push((c, 0));
                } else {
                    post[b as usize] = qc;
                    qc += 1;
                    let _ = stack.pop();
                }
            }
        }
        DomTree {
            pre,
            post,
            preorder,
            depth,
        }
    }

    /// Whether `a` dominates `b` (both reachable). A block dominates itself.
    pub(crate) fn dominates(&self, a: u32, b: u32) -> bool {
        let (pa, pb) = (
            self.pre.get(a as usize).copied().unwrap_or(NONE),
            self.pre.get(b as usize).copied().unwrap_or(NONE),
        );
        let (qa, qb) = (
            self.post.get(a as usize).copied().unwrap_or(NONE),
            self.post.get(b as usize).copied().unwrap_or(NONE),
        );
        pa != NONE && pb != NONE && pa <= pb && qb <= qa
    }
}

/// The block that defines `v` (its parameter's block or its instruction's
/// block), if it is defined.
pub(crate) fn def_block(func: &Function, v: Value) -> Option<Block> {
    match func.value_def(v)? {
        ValueDef::Param { block, .. } => Some(block),
        ValueDef::Result { inst, .. } => func.inst_block(inst),
        _ => None,
    }
}

/// Whether an instruction kind propagates "derived from a `ref`" from its
/// operands to its results (as the validator's safepoint rules define it, plus
/// comparisons, to stay conservative).
fn propagates(data: &InstData) -> bool {
    matches!(
        data,
        InstData::Unary { .. }
            | InstData::Binary { .. }
            | InstData::Fma { .. }
            | InstData::Convert { .. }
            | InstData::Select { .. }
            | InstData::FieldAddr { .. }
            | InstData::ElemAddr { .. }
            | InstData::PtrOffset { .. }
            | InstData::Compare { .. }
    )
}

/// The values the safepoint rules track: every `ref`, and every value derived
/// from one. Passes never value-number, hoist, or turn into constants a tracked
/// value, since moving one across a safepoint would break the IR's GC rules.
///
/// This is a superset of the validator's set (it also follows comparisons and a
/// `check`'s result), which is the safe direction. Returns `None` when the
/// function has no `ref` at all (the common case, and free).
pub(crate) fn tracked_values(func: &Function, cfg: &Cfg) -> Option<Vec<bool>> {
    let nv = func.value_count();
    let mut tracked = vec![false; nv];
    let mut any = false;
    for (i, t) in tracked.iter_mut().enumerate() {
        if func.value_type(Value::from_u32(i as u32)) == Some(Type::Ref) {
            *t = true;
            any = true;
        }
    }
    let mut ref_to_ptr = false;
    for &b in &cfg.rpo {
        for inst in func.insts(Block::from_u32(b)) {
            if let Some(InstData::Convert {
                op: ConvOp::RefToPtr,
                ..
            }) = func.inst(inst)
            {
                ref_to_ptr = true;
            }
        }
    }
    if !any && !ref_to_ptr {
        return None;
    }
    // Edges value -> value derived from it, then a worklist from the roots.
    let mut edges: Vec<(u32, u32)> = Vec::new();
    let mut work: Vec<u32> = Vec::new();
    for (i, &t) in tracked.iter().enumerate() {
        if t {
            work.push(i as u32);
        }
    }
    for &b in &cfg.rpo {
        let block = Block::from_u32(b);
        for inst in func.insts(block) {
            let Some(data) = func.inst(inst) else {
                continue;
            };
            let results = func.results(inst);
            if let InstData::Convert {
                op: ConvOp::RefToPtr,
                ..
            } = data
            {
                for r in results {
                    work.push(r.as_u32());
                }
            }
            if propagates(data) {
                data.for_each_operand(|op| {
                    for r in results {
                        edges.push((func.resolve(op).as_u32(), r.as_u32()));
                    }
                });
            }
        }
        if let Some(term) = func.terminator(block) {
            let mut check_ops: Vec<u32> = Vec::new();
            if let Terminator::Check { op, .. } = term {
                op.for_each_operand(|v| check_ops.push(func.resolve(v).as_u32()));
            }
            for dest in term.successors() {
                let params = func.block_params(dest.block);
                for (arg, &p) in dest.args.iter().zip(params) {
                    match arg {
                        BlockArg::Value(v) => edges.push((func.resolve(*v).as_u32(), p.as_u32())),
                        BlockArg::Result(_) => {
                            for &o in &check_ops {
                                edges.push((o, p.as_u32()));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    edges.sort_unstable();
    while let Some(v) = work.pop() {
        if let Some(t) = tracked.get_mut(v as usize) {
            *t = true;
        }
        let lo = edges.partition_point(|&(from, _)| from < v);
        for &(from, to) in edges.get(lo..).unwrap_or(&[]) {
            if from != v {
                break;
            }
            if let Some(t) = tracked.get_mut(to as usize) {
                if !*t {
                    *t = true;
                    work.push(to);
                }
            }
        }
    }
    Some(tracked)
}

/// Whether `v` is tracked, given the (optional) table.
pub(crate) fn is_tracked(tracked: &Option<Vec<bool>>, v: Value) -> bool {
    tracked
        .as_ref()
        .is_some_and(|t| t.get(v.index()).copied().unwrap_or(false))
}

/// The number of live instructions and live blocks of `func`.
pub(crate) fn size(func: &Function) -> (usize, usize) {
    let mut insts = 0;
    let mut blocks = 0;
    for b in func.blocks() {
        blocks += 1;
        insts += func.insts(b).count();
    }
    (insts, blocks)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ir_lang::{CmpOp, Linkage, Module, Signature};

    /// Diamond with a loop: entry -> head; head -> body | exit; body -> head.
    fn looped() -> (Module, ir_lang::FuncId) {
        let mut m = Module::new("t");
        let f = m
            .declare_function("f", &Signature::new(&[Type::I64], &[]), Linkage::Export)
            .unwrap();
        let mut b = m.build(f).unwrap();
        let x = b.param(0).unwrap();
        let head = b.create_block(&[]).unwrap();
        let body = b.create_block(&[]).unwrap();
        let exit = b.create_block(&[]).unwrap();
        b.jump(head, &[]).unwrap();
        b.switch_to(head).unwrap();
        let c = b.compare(CmpOp::Lt, x, x).unwrap();
        b.branch(c, body, &[], exit, &[]).unwrap();
        b.switch_to(body).unwrap();
        b.jump(head, &[]).unwrap();
        b.switch_to(exit).unwrap();
        b.ret(&[]).unwrap();
        (m, f)
    }

    #[test]
    fn test_cfg_and_dominators_of_a_loop() {
        let (m, f) = looped();
        let func = m.function(f).unwrap();
        let cfg = Cfg::new(func);
        assert_eq!(cfg.rpo.len(), 4);
        assert_eq!(cfg.preds(1).len(), 2);
        let dom = DomTree::new(&cfg);
        assert!(dom.dominates(0, 1));
        assert!(dom.dominates(1, 2));
        assert!(dom.dominates(1, 3));
        assert_eq!(dom.depth[2], 2);
        assert!(!dom.dominates(2, 3));
        assert!(dom.dominates(0, 0));
        assert_eq!(dom.preorder[0], 0);
    }

    #[test]
    fn test_unreachable_blocks_are_outside_the_tree() {
        let mut m = Module::new("t");
        let f = m
            .declare_function("f", &Signature::new(&[], &[]), Linkage::Export)
            .unwrap();
        let mut b = m.build(f).unwrap();
        let dead = b.create_block(&[]).unwrap();
        b.ret(&[]).unwrap();
        b.switch_to(dead).unwrap();
        b.ret(&[]).unwrap();
        let func = m.function(f).unwrap();
        let cfg = Cfg::new(func);
        assert!(!cfg.reachable(1));
        let dom = DomTree::new(&cfg);
        assert!(!dom.dominates(0, 1));
        assert_eq!(tracked_values(func, &cfg), None);
    }

    #[test]
    fn test_dominators_match_a_brute_force_reference() {
        // Random CFGs: compare with "a dominates b iff b is unreachable from the
        // entry once a is removed".
        let mut seed = 0x1234_5678_9abc_def1u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let n = (next() % 12 + 2) as usize;
            let mut m = Module::new("t");
            let f = m
                .declare_function("f", &Signature::new(&[Type::Bool], &[]), Linkage::Export)
                .unwrap();
            let mut b = m.build(f).unwrap();
            let c = b.param(0).unwrap();
            let blocks: Vec<Block> = (1..n).map(|_| b.create_block(&[]).unwrap()).collect();
            let mut all = vec![b.func().entry()];
            all.extend(&blocks);
            let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
            for i in 0..n {
                b.switch_to(all[i]).unwrap();
                let k = next() % 3;
                if k == 0 || n == 1 {
                    b.ret(&[]).unwrap();
                } else {
                    let t = 1 + (next() as usize) % (n - 1);
                    let e = 1 + (next() as usize) % (n - 1);
                    if k == 1 {
                        b.jump(all[t], &[]).unwrap();
                        succ[i].push(t);
                    } else {
                        b.branch(c, all[t], &[], all[e], &[]).unwrap();
                        succ[i].push(t);
                        succ[i].push(e);
                    }
                }
            }
            let func = m.function(f).unwrap();
            let cfg = Cfg::new(func);
            let dom = DomTree::new(&cfg);
            let reach_without = |skip: usize| {
                let mut seen = vec![false; n];
                let mut stack = vec![0usize];
                if skip == 0 {
                    return seen;
                }
                seen[0] = true;
                while let Some(x) = stack.pop() {
                    for &s in &succ[x] {
                        if s != skip && !seen[s] {
                            seen[s] = true;
                            stack.push(s);
                        }
                    }
                }
                seen
            };
            let full = reach_without(usize::MAX);
            for a in 0..n {
                let without = reach_without(a);
                for bb in 0..n {
                    if !full[a] || !full[bb] {
                        continue;
                    }
                    let expect = a == bb || !without[bb];
                    assert_eq!(dom.dominates(a as u32, bb as u32), expect, "{a} dom {bb}");
                }
            }
        }
    }
}
