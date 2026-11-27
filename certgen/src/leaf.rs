//! Bit-parallel evaluation of leaves, mirroring the Lean definitions `RACert.Problem.leaf`.

use crate::problem::Problem;

pub enum Tab {
    F,
    T,
    M(Vec<u64>),
}

pub struct Evaluator<'a> {
    pub p: &'a Problem,
    pub b: usize,
    pub words: usize,
    pub mask: u64,
    pats: Vec<Tab>,
    pub terms: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>,
}

impl<'a> Evaluator<'a> {
    pub fn new(p: &'a Problem, b: usize) -> Self {
        let bits: usize = 1 << b;
        let words = bits.div_ceil(64);
        let mask = if bits >= 64 { u64::MAX } else { (1u64 << bits) - 1 };
        let mut pats = vec![];
        for i in 0..b {
            let mut v = vec![0u64; words];
            for beta in 0..bits {
                if (beta >> i) & 1 == 1 {
                    v[beta / 64] |= 1 << (beta % 64);
                }
            }
            pats.push(Tab::M(v));
        }
        let terms = p.quads.iter().map(|&x| p.quad_terms(x)).collect();
        Evaluator { p, b, words, mask, pats, terms }
    }

    fn tab(&self, code: usize, alpha: u64) -> &Tab {
        match code {
            0 => &Tab::F,
            1 => &Tab::T,
            c if c - 2 < self.b => &self.pats[c - 2],
            c if (alpha >> (c - 2 - self.b)) & 1 == 1 => &Tab::T,
            _ => &Tab::F,
        }
    }

    fn dot(&self, terms: &[(usize, usize)], alpha: u64) -> Tab {
        let mut acc: Option<Vec<u64>> = None;
        for &(i, j) in terms {
            match (self.tab(i, alpha), self.tab(j, alpha)) {
                (Tab::F, _) | (_, Tab::F) => continue,
                (Tab::T, Tab::T) => return Tab::T,
                (Tab::T, Tab::M(m)) | (Tab::M(m), Tab::T) => {
                    let dst = acc.get_or_insert_with(|| vec![0; self.words]);
                    for (a, x) in dst.iter_mut().zip(m) {
                        *a |= x;
                    }
                }
                (Tab::M(m1), Tab::M(m2)) => {
                    let dst = acc.get_or_insert_with(|| vec![0; self.words]);
                    for ((a, x), y) in dst.iter_mut().zip(m1).zip(m2) {
                        *a |= x & y;
                    }
                }
            }
        }
        acc.map_or(Tab::F, Tab::M)
    }

    /// Number of assignments of the low `b` variables satisfying the formula, the remaining
    /// variables being given by the bits of `alpha`.
    pub fn leaf(&self, alpha: u64) -> u64 {
        self.leaf_terms(alpha, &self.terms)
    }

    /// Evaluate a residual formula on the same packed coordinate columns.
    pub fn leaf_terms(&self, alpha: u64, terms: &[(Vec<(usize, usize)>, Vec<(usize, usize)>)]) -> u64 {
        let mut bad = vec![0u64; self.words];
        for (l, r) in terms {
            let lt = self.dot(l, alpha);
            let rt = self.dot(r, alpha);
            match (lt, rt) {
                (Tab::F, Tab::F) | (Tab::T, Tab::T) => {}
                (Tab::F, Tab::T) | (Tab::T, Tab::F) => return 0,
                (Tab::F, Tab::M(m)) | (Tab::M(m), Tab::F) => bad.iter_mut().zip(&m).for_each(|(a, b)| *a |= b),
                (Tab::T, Tab::M(m)) | (Tab::M(m), Tab::T) => bad.iter_mut().zip(&m).for_each(|(a, b)| *a |= !b),
                (Tab::M(m1), Tab::M(m2)) => bad.iter_mut().zip(m1.iter().zip(&m2)).for_each(|(a, (x, y))| *a |= x ^ y),
            }
        }
        let mut cnt = 0u64;
        for (i, w) in bad.iter().enumerate() {
            let m = if i + 1 == self.words { self.mask } else { u64::MAX };
            cnt += (!w & m).count_ones() as u64;
        }
        cnt
    }
}

/// All leaves `alpha = 0 .. 2^(nvars-b)`, computed in parallel.
pub fn all_leaves(p: &Problem, b: usize) -> Vec<u64> {
    let t = p.nvars - b;
    let total: u64 = 1 << t;
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(10) as u64;
    let ev = Evaluator::new(p, b);
    let mut out = vec![0u64; total as usize];
    let chunk = (total / nthreads).max(1) as usize;
    std::thread::scope(|sc| {
        for (ci, slice) in out.chunks_mut(chunk).enumerate() {
            let ev = &ev;
            sc.spawn(move || {
                for (i, o) in slice.iter_mut().enumerate() {
                    *o = ev.leaf((ci * chunk + i) as u64);
                }
            });
        }
    });
    out
}

/// Memoised sides of the quadruple conditions, keyed by the high bits they read.
struct SideCache<'a> {
    ev: &'a Evaluator<'a>,
    masks: Vec<(u64, u64)>,
    cache: std::collections::HashMap<(u32, u8, u64), std::rc::Rc<Tab>>,
    bytes: usize,
    limit: usize,
}

impl<'a> SideCache<'a> {
    fn new(ev: &'a Evaluator<'a>, limit_bytes: usize) -> Self {
        let masks = ev.p.quads.iter().map(|&x| ev.p.quad_masks(x, ev.b)).collect();
        SideCache { ev, masks, cache: std::collections::HashMap::new(), bytes: 0, limit: limit_bytes }
    }

    fn side(&mut self, qi: usize, side: u8, r: u64) -> std::rc::Rc<Tab> {
        if let Some(t) = self.cache.get(&(qi as u32, side, r)) {
            return t.clone();
        }
        let terms = if side == 0 { &self.ev.terms[qi].0 } else { &self.ev.terms[qi].1 };
        let t = std::rc::Rc::new(self.ev.dot(terms, r));
        if let Tab::M(m) = &*t {
            self.bytes += m.len() * 8;
        }
        if self.bytes > self.limit {
            self.cache.clear();
            self.bytes = 0;
        }
        self.cache.insert((qi as u32, side, r), t.clone());
        t
    }

    /// Accumulate violations at the selected word indices, or over the entire table.
    fn violations(&mut self, group: &[usize], a: u64, selected: Option<&[usize]>, bad: &mut [u64]) {
        bad.fill(0);
        for &qi in group {
            let (m1, m2) = self.masks[qi];
            let lt = self.side(qi, 0, a & m1);
            let rt = self.side(qi, 1, a & m2);
            match (&*lt, &*rt) {
                (Tab::F, Tab::F) | (Tab::T, Tab::T) => {}
                (Tab::F, Tab::T) | (Tab::T, Tab::F) => {
                    bad.fill(u64::MAX);
                    return;
                }
                (Tab::F, Tab::M(m)) | (Tab::M(m), Tab::F) => add_words(bad, selected, |i| m[i]),
                (Tab::T, Tab::M(m)) | (Tab::M(m), Tab::T) => add_words(bad, selected, |i| !m[i]),
                (Tab::M(l), Tab::M(r)) => add_words(bad, selected, |i| l[i] ^ r[i]),
            }
        }
    }
}

fn add_words(bad: &mut [u64], selected: Option<&[usize]>, word: impl Fn(usize) -> u64) {
    if let Some(indices) = selected {
        for (dst, &i) in bad.iter_mut().zip(indices) {
            *dst |= word(i);
        }
    } else {
        for (i, dst) in bad.iter_mut().enumerate() {
            *dst |= word(i);
        }
    }
}

/// Per-worker cache and scratch space for the eliminated-variable evaluator.
pub struct MemoEval<'a> {
    sides: SideCache<'a>,
    groups: Vec<Vec<usize>>,
    active: Vec<usize>,
    weights: Vec<Vec<u64>>,
    bad0: Vec<u64>,
    bad1: Vec<u64>,
}

impl<'a> MemoEval<'a> {
    pub fn new(ev: &'a Evaluator<'a>, m: usize, tags: &[Option<usize>], limit: usize) -> Self {
        let mut groups = vec![Vec::new(); m + 1];
        for (qi, &tag) in tags.iter().enumerate() {
            if let Some(group) = tag {
                groups[group].push(qi);
            }
        }
        MemoEval {
            sides: SideCache::new(ev, limit),
            groups,
            active: Vec::new(),
            weights: vec![vec![0; ev.words]; m + 1],
            bad0: vec![0; ev.words],
            bad1: vec![0; ev.words],
        }
    }

    /// Number of low assignments compatible with the given high bits.
    pub fn leaf_elim(&mut self, alpha: u64) -> u64 {
        let m = self.groups.len() - 1;
        let a0 = alpha << m;
        let words = self.sides.ev.words;
        let good = &mut self.weights[0];
        self.sides.violations(&self.groups[0], a0, None, good);
        for w in good.iter_mut() {
            *w = !*w;
        }
        good[words - 1] &= self.sides.ev.mask;
        if m == 0 {
            return good.iter().map(|w| u64::from(w.count_ones())).sum();
        }

        // Compact sparse tables once. Dense tables retain sequential, vectorisable reads.
        self.active.clear();
        self.active.extend((0..words).filter(|&w| good[w] != 0));
        if self.active.is_empty() {
            return 0;
        }
        let selected = if self.active.len() <= words / 2 {
            for (dst, &src) in self.active.iter().enumerate() {
                good[dst] = good[src];
            }
            Some(self.active.as_slice())
        } else {
            None
        };
        let len = selected.map_or(words, |indices| indices.len());
        let forced = &mut self.bad0[..len];
        let free = &mut self.bad1[..len];
        for (i, group) in self.groups[1..].iter().enumerate() {
            self.sides.violations(group, a0, selected, forced);
            self.sides.violations(group, a0 | (1 << i), selected, free);
            for (x, y) in forced.iter_mut().zip(free.iter_mut()) {
                let (b0, b1) = (*x, *y);
                *x = b0 ^ b1;
                *y = !(b0 | b1);
            }
            // Descend so that row j-1 still contains the previous variable's weights.
            for j in (1..=i + 1).rev() {
                let (lower, upper) = self.weights.split_at_mut(j);
                let prev = &lower[j - 1];
                let dst = &mut upper[0];
                if j == i + 1 {
                    for w in 0..len {
                        dst[w] = prev[w] & free[w];
                    }
                } else {
                    for w in 0..len {
                        dst[w] = (dst[w] & forced[w]) | (prev[w] & free[w]);
                    }
                }
            }
            for (x, f) in self.weights[0].iter_mut().zip(forced.iter()) {
                *x &= f;
            }
        }
        self.weights.iter().enumerate().map(|(j, row)| {
            row[..len].iter().map(|w| u64::from(w.count_ones())).sum::<u64>() << j
        }).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sys::Sys;

    #[test]
    fn reused_tables_agree_with_enumerating_the_eliminated_variables() {
        let sys = Sys::new(4, 0);
        let rep: Vec<_> = (0..sys.k).collect();
        for (b, m) in [(2, 2), (6, 2), (10, 2), (10, 0)] {
            let p = Problem::new(&sys, &rep, &|p, roots| {
                let loops = [p.tcode(1, 1, 1), p.tcode(2, 2, 2)];
                let mut order: Vec<_> = roots.into_iter().filter(|r| !loops[..m].contains(r)).collect();
                order.splice(b..b, loops[..m].iter().copied());
                order
            });
            let ev = Evaluator::new(&p, b);
            let mut memo = MemoEval::new(&ev, m, &p.quad_tags(b, m), 4096);
            let high_mask = (1 << (p.nvars - b - m)) - 1;
            for i in 0..32 {
                let alpha = (i * 7919) & high_mask;
                let expected: u64 = (0..1 << m).map(|z| ev.leaf((alpha << m) | z)).sum();
                assert_eq!(memo.leaf_elim(alpha), expected);
            }
        }
    }
}

/// A binary tree of quadruples (indices into `Problem::quads`) with masks, mirroring
/// `RACert.QTree`.
/// A classified side of a condition (mirroring `RACert.Side`): the mask of its high variables,
/// its items `(mask, code)` and its fixed terms.
pub type Side = (u64, Vec<(u64, usize)>, Vec<usize>);

/// The classification of the terms of one side (mirroring `RACert.classify`).
pub fn classify(b: usize, terms: &[(usize, usize)]) -> Side {
    if terms.iter().any(|&(i, j)| i == 1 && j == 1) {
        return (0, vec![(0, 0)], vec![]);
    }
    let hm = |c: usize| -> u64 { if c < b + 2 { 0 } else { 1 << (c - 2 - b) } };
    let lv = |c: usize| -> usize { if c < 2 || c >= b + 2 { 0 } else { c - 1 } };
    let mut items = vec![];
    let mut fixed = vec![];
    for &(c1, c2) in terms {
        if c1 == 0 || c2 == 0 {
            continue;
        }
        let tm = hm(c1) | hm(c2);
        let (l1, l2) = (lv(c1), lv(c2));
        if l1 == 0 {
            if l2 == 0 || tm != 0 {
                items.push((tm, l2));
            } else {
                fixed.push((l2 - 1) * 64 + (l2 - 1));
            }
        } else if l2 == 0 {
            if tm != 0 {
                items.push((tm, l1));
            } else {
                fixed.push((l1 - 1) * 64 + (l1 - 1));
            }
        } else {
            fixed.push((l1 - 1).min(l2 - 1) * 64 + (l1 - 1).max(l2 - 1));
        }
    }
    let mask = items.iter().fold(0, |m, it| m | it.0);
    (mask, items, fixed)
}

fn side_lean(s: &Side) -> String {
    let items: Vec<String> = s.1.iter().map(|(tm, c)| format!("({}, {})", tm, c)).collect();
    let fixed: Vec<String> = s.2.iter().map(|c| format!("{}", c)).collect();
    format!("({}, [{}], [{}])", s.0, items.join(", "), fixed.join(", "))
}

pub enum QTree {
    Leaf { qi: usize, x: usize, m1: u64, m2: u64, sl: Side, sr: Side },
    Node { id: usize, ml: u64, l: Box<QTree>, mr: u64, r: Box<QTree> },
}

impl QTree {
    pub fn mask(&self) -> u64 {
        match self {
            QTree::Leaf { m1, m2, .. } => m1 | m2,
            QTree::Node { ml, mr, .. } => ml | mr,
        }
    }

    /// The leaf of the quadruple with index `qi` and code `x`.
    pub fn leaf(p: &Problem, b: usize, qi: usize, x: usize) -> QTree {
        let (l, r) = p.quad_terms(x);
        let (sl, sr) = (classify(b, &l), classify(b, &r));
        QTree::Leaf { qi, x, m1: sl.0, m2: sr.0, sl, sr }
    }

    /// A balanced tree over the given quadruples `(index, code)`, in order.
    pub fn balanced(p: &Problem, b: usize, items: &[(usize, usize)], next_id: &mut usize) -> QTree {
        if items.len() == 1 {
            return QTree::leaf(p, b, items[0].0, items[0].1);
        }
        let mid = items.len().div_ceil(2);
        let l = QTree::balanced(p, b, &items[..mid], next_id);
        let r = QTree::balanced(p, b, &items[mid..], next_id);
        *next_id += 1;
        QTree::Node { id: *next_id, ml: l.mask(), l: Box::new(l), mr: r.mask(), r: Box::new(r) }
    }

    /// The Lean term.
    pub fn lean(&self) -> String {
        match self {
            QTree::Leaf { x, sl, sr, .. } => format!(".leaf {} {} {}", x, side_lean(sl), side_lean(sr)),
            QTree::Node { ml, l, mr, r, .. } => format!(".node {} ({}) {} ({})", ml, l.lean(), mr, r.lean()),
        }
    }

    pub fn entries(&self, out: &mut Vec<(usize, u64, u64)>) {
        match self {
            QTree::Leaf { x, m1, m2, .. } => out.push((*x, *m1, *m2)),
            QTree::Node { l, r, .. } => {
                l.entries(out);
                r.entries(out);
            }
        }
    }
}

/// Simulation of the kernel's work for the leaves checked in one declaration with
/// `RACert.Problem.leafE`: `keys` are the canonical big-number expressions already evaluated,
/// `memo` the subtrees already evaluated (by node and masked high variables).
pub struct Sim<'a> {
    pub terms: &'a [(Vec<(usize, usize)>, Vec<(usize, usize)>)],
    pub b: usize,
    pub keys: std::collections::HashSet<u64>,
    pub memo: std::collections::HashMap<(usize, u64), u64>,
    /// Big operations by category: residuals, xor, tree, weights, population counts.
    pub cat: [usize; 5],
    /// Evaluated tree nodes and sides (a measure of the small reduction steps).
    pub visits: usize,
}

fn h3(tag: u8, a: u64, c: u64, d: u64) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    (tag, a, c, d).hash(&mut h);
    h.finish() | 2
}

impl<'a> Sim<'a> {
    pub fn new(terms: &'a [(Vec<(usize, usize)>, Vec<(usize, usize)>)], b: usize) -> Self {
        Sim { terms, b, keys: Default::default(), memo: Default::default(), cat: [0; 5], visits: 0 }
    }

    pub fn reset(&mut self) {
        self.keys.clear();
        self.memo.clear();
    }

    /// Value of one side: 0 false, 1 true, else the key of its table.
    fn side(&mut self, qi: usize, sd: u8, r: u64) -> u64 {
        let b = self.b;
        let terms = if sd == 0 { &self.terms[qi].0 } else { &self.terms[qi].1 };
        let kind = |code: usize| -> u8 {
            match code { 0 => 0, 1 => 1, c => { let j = c - 2; if j < b { 2 } else { ((r >> (j - b)) & 1) as u8 } } }
        };
        if let Some(&v) = self.memo.get(&(1_000_000 + 2 * qi + sd as usize, r)) {
            return v;
        }
        self.visits += 1;
        let mut val: Option<u64> = None;
        let mut acc: u64 = 0;
        for &(i, j) in terms {
            let (x, y) = (kind(i), kind(j));
            if x == 0 || y == 0 { continue; }
            if x == 1 && y == 1 { val = Some(1); break; }
            let term = if x == 2 && y == 2 {
                let k = h3(1, i.min(j) as u64, i.max(j) as u64, 0);
                if self.keys.insert(k) { self.cat[0] += 1; }
                k
            } else if x == 2 { h3(0, i as u64, 0, 0) } else { h3(0, j as u64, 0, 0) };
            acc = if acc == 0 { term } else {
                let k = h3(2, acc, term, 0);
                if self.keys.insert(k) { self.cat[0] += 1; }
                k
            };
        }
        let v = val.unwrap_or(acc);
        self.memo.insert((1_000_000 + 2 * qi + sd as usize, r), v);
        v
    }

    /// The violations of a tree: 0 none, else a key.
    pub fn viol(&mut self, t: &QTree, rho: u64) -> u64 {
        match t {
            QTree::Leaf { qi, m1, m2, .. } => {
                self.visits += 1;
                let vl = self.side(*qi, 0, rho & m1);
                let vr = self.side(*qi, 1, rho & m2);
                if vl == vr { return 0; }
                let q = h3(3, vl, vr, 0);
                if self.keys.insert(q) { self.cat[1] += 1; }
                q
            }
            QTree::Node { id, ml, l, mr, r } => {
                if let Some(&v) = self.memo.get(&(*id, rho)) {
                    return v;
                }
                self.visits += 1;
                let a = self.viol(l, rho & ml);
                let c = self.viol(r, rho & mr);
                let v = if c == 0 { a } else if a == 0 { c } else {
                    let k = h3(4, a, c, 0);
                    if self.keys.insert(k) { self.cat[2] += 1; }
                    k
                };
                self.memo.insert((*id, rho), v);
                v
            }
        }
    }

    /// One more leaf.
    pub fn leaf(&mut self, qt: &QTree, ow: &[QTree], alpha: u64) {
        let m = ow.len();
        let a0 = alpha << m;
        let bad = self.viol(qt, a0);
        let mut e: Vec<u64> = vec![h3(6, bad, 0, 0)];
        if self.keys.insert(e[0]) { self.cat[3] += 1; }
        for (i, t) in ow.iter().enumerate() {
            let mk = t.mask();
            let b0 = self.viol(t, a0 & mk);
            let b1 = self.viol(t, (a0 | 1 << i) & mk);
            let f = h3(7, b0, b1, 0);
            if self.keys.insert(f) { self.cat[3] += 1; }
            let r = h3(8, b0, b1, 0);
            if self.keys.insert(r) { self.cat[3] += 2; }
            let mut next = vec![];
            let mut prev = 0u64;
            for &x in &e {
                let k = h3(9, x, prev, f ^ r.rotate_left(17));
                if self.keys.insert(k) { self.cat[3] += if prev == 0 { 1 } else { 3 }; }
                next.push(k);
                prev = x;
            }
            let k = h3(9, 0, prev, r);
            if self.keys.insert(k) { self.cat[3] += 1; }
            next.push(k);
            e = next;
        }
        // the weighted population count (`RACert.wtotF`) of the m + 1 tables
        const WPOP: [usize; 9] = [0, 16, 23, 32, 37, 51, 56, 65, 70];
        let key = e.iter().fold(0u64, |a, &x| h3(20, a, x, 0));
        if self.keys.insert(key) { self.cat[4] += WPOP[e.len().min(8)]; }
    }
}
