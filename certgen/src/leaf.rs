//! Bit-parallel evaluation of leaves, mirroring the Lean definitions `RACert.Problem.leaf`.

use crate::problem::Problem;

#[derive(Clone)]
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
    pats: Vec<Vec<u64>>,
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
            pats.push(v);
        }
        let terms = p.quads.iter().map(|&x| p.quad_terms(x)).collect();
        Evaluator { p, b, words, mask, pats, terms }
    }

    fn tab(&self, code: usize, alpha: u64) -> Tab {
        match code {
            0 => Tab::F,
            1 => Tab::T,
            c => {
                let j = c - 2;
                if j < self.b {
                    Tab::M(self.pats[j].clone())
                } else if (alpha >> (j - self.b)) & 1 == 1 {
                    Tab::T
                } else {
                    Tab::F
                }
            }
        }
    }

    fn dot(&self, terms: &[(usize, usize)], vt: &[Tab]) -> Tab {
        let mut acc: Option<Vec<u64>> = None;
        for &(i, j) in terms {
            let (x, y) = (&vt[i], &vt[j]);
            let prod: &[u64];
            let tmp: Vec<u64>;
            match (x, y) {
                (Tab::F, _) | (_, Tab::F) => continue,
                (Tab::T, Tab::T) => return Tab::T,
                (Tab::T, Tab::M(m)) | (Tab::M(m), Tab::T) => prod = m,
                (Tab::M(m1), Tab::M(m2)) => {
                    tmp = m1.iter().zip(m2).map(|(a, b)| a & b).collect();
                    prod = &tmp;
                }
            }
            match &mut acc {
                None => acc = Some(prod.to_vec()),
                Some(a) => a.iter_mut().zip(prod).for_each(|(a, b)| *a |= b),
            }
        }
        match acc {
            None => Tab::F,
            Some(a) => Tab::M(a),
        }
    }

    /// Number of assignments of the low `b` variables satisfying the formula, the remaining
    /// variables being given by the bits of `alpha`.
    pub fn leaf(&self, alpha: u64) -> u64 {
        // table of each class code
        let vt: Vec<Tab> = (0..self.p.nvars + 2).map(|c| self.tab(c, alpha)).collect();
        let mut bad = vec![0u64; self.words];
        for (l, r) in &self.terms {
            let lt = self.dot(l, &vt);
            let rt = self.dot(r, &vt);
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

/// Leaf evaluator memoising the two sides of every quadruple's condition on the high variables
/// they depend on (mirroring `RACert.Problem.leafR`).
pub struct MemoEval<'a> {
    ev: &'a Evaluator<'a>,
    masks: Vec<(u64, u64)>,
    cache: std::collections::HashMap<(u32, u8, u64), std::rc::Rc<Tab>>,
    bytes: usize,
    limit: usize,
}

impl<'a> MemoEval<'a> {
    pub fn new(ev: &'a Evaluator<'a>, limit_bytes: usize) -> Self {
        let masks = ev.p.quads.iter().map(|&x| ev.p.quad_masks(x, ev.b)).collect();
        MemoEval { ev, masks, cache: std::collections::HashMap::new(), bytes: 0, limit: limit_bytes }
    }

    fn side(&mut self, qi: usize, side: u8, r: u64) -> std::rc::Rc<Tab> {
        if let Some(t) = self.cache.get(&(qi as u32, side, r)) {
            return t.clone();
        }
        let terms = if side == 0 { &self.ev.terms[qi].0 } else { &self.ev.terms[qi].1 };
        // only the bits of `r` selected by the mask matter for these terms
        let vt: Vec<Tab> = (0..self.ev.p.nvars + 2).map(|c| self.ev.tab(c, r)).collect();
        let t = std::rc::Rc::new(self.ev.dot(terms, &vt));
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

    /// Add the violations of the condition `qi` under the high assignment `a` to `bad`.
    fn violations(&mut self, qi: usize, a: u64, bad: &mut [u64]) {
        let (m1, m2) = self.masks[qi];
        let lt = self.side(qi, 0, a & m1);
        let rt = self.side(qi, 1, a & m2);
        match (&*lt, &*rt) {
            (Tab::F, Tab::F) | (Tab::T, Tab::T) => {}
            (Tab::F, Tab::T) | (Tab::T, Tab::F) => bad.iter_mut().for_each(|a| *a = u64::MAX),
            (Tab::F, Tab::M(m)) | (Tab::M(m), Tab::F) => bad.iter_mut().zip(m).for_each(|(a, b)| *a |= b),
            (Tab::T, Tab::M(m)) | (Tab::M(m), Tab::T) => bad.iter_mut().zip(m).for_each(|(a, b)| *a |= !b),
            (Tab::M(m1), Tab::M(m2)) => bad.iter_mut().zip(m1.iter().zip(m2)).for_each(|(a, (x, y))| *a |= x ^ y),
        }
    }

    /// The leaf `alpha` of the problem with `b + m` low variables, the last `m` of which are
    /// eliminated (mirroring `RACert.Problem.leafE`); `tags` as given by `Problem::quad_tags`.
    pub fn leaf_elim(&mut self, alpha: u64, m: usize, tags: &[Option<usize>]) -> u64 {
        let words = self.ev.words;
        let a0 = alpha << m;
        let mut bad = vec![0u64; words];
        for qi in 0..tags.len() {
            if tags[qi] == Some(0) {
                self.violations(qi, a0, &mut bad);
            }
        }
        let last = self.ev.mask;
        let mut e: Vec<Vec<u64>> = vec![bad.iter().map(|w| !w).collect()];
        *e[0].last_mut().unwrap() &= last;
        if e[0].iter().all(|&w| w == 0) {
            return 0;
        }
        for i in 0..m {
            let mut b0 = vec![0u64; words];
            let mut b1 = vec![0u64; words];
            for qi in 0..tags.len() {
                if tags[qi] == Some(i + 1) {
                    self.violations(qi, a0, &mut b0);
                    self.violations(qi, a0 | 1 << i, &mut b1);
                }
            }
            // forced: exactly one value admissible; free: both
            let mut next: Vec<Vec<u64>> = vec![vec![0u64; words]; e.len() + 1];
            for j in 0..e.len() {
                for w in 0..words {
                    let f = b0[w] ^ b1[w];
                    let r = !(b0[w] | b1[w]);
                    next[j][w] |= e[j][w] & f;
                    next[j + 1][w] |= e[j][w] & r;
                }
            }
            e = next;
        }
        e.iter().enumerate().map(|(j, v)| (v.iter().map(|w| w.count_ones() as u64).sum::<u64>()) << j).sum()
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
