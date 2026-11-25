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

/// Operation counts of one leaf as evaluated by the kernel (distinct big-number operations):
/// (ands, ors, xors, bad-ors, quads with equal non-constant sides).
pub fn op_counts(ev: &Evaluator, alpha: u64) -> (usize, usize, usize, usize, usize) {
    use std::collections::HashSet;
    let p = ev.p;
    let b = ev.b;
    // 0 false, 1 true, 2 table
    let kind = |code: usize| -> u8 {
        match code {
            0 => 0,
            1 => 1,
            c => { let j = c - 2; if j < b { 2 } else { ((alpha >> (j - b)) & 1) as u8 } }
        }
    };
    let mut ands: HashSet<(usize, usize)> = HashSet::new();
    let (mut ors, mut xors, mut bors, mut eqs) = (0, 0, 0, 0);
    // returns (constant?, canonical description)
    let dot = |terms: &[(usize, usize)], ands: &mut HashSet<(usize, usize)>, ors: &mut usize| -> (u8, Vec<(usize, usize)>) {
        let mut desc: Vec<(usize, usize)> = vec![];
        let mut acc_real = false;
        for &(i, j) in terms {
            let (x, y) = (kind(i), kind(j));
            if x == 0 || y == 0 { continue; }
            if x == 1 && y == 1 { return (1, vec![]); }
            if x == 2 && y == 2 { ands.insert((i, j)); desc.push((i.min(j), i.max(j))); }
            else if x == 2 { desc.push((i, i)); } else { desc.push((j, j)); }
            if acc_real { *ors += 1; }
            acc_real = true;
        }
        if desc.is_empty() { (0, desc) } else { desc.sort(); desc.dedup(); (2, desc) }
    };
    for (l, r) in &ev.terms {
        let (kl, dl) = dot(l, &mut ands, &mut ors);
        let (kr, dr) = dot(r, &mut ands, &mut ors);
        if kl != 2 && kr != 2 {
            if kl != kr { break; }
            continue;
        }
        if kl == 2 && kr == 2 && dl == dr { eqs += 1; }
        xors += 1;
        bors += 1;
    }
    let _ = p;
    (ands.len(), ors, xors, bors, eqs)
}

/// Keys of the big-number operations a "symbolic" evaluator would perform for one leaf, where
/// every operation is identified by its canonical expression (so that equal expressions are
/// computed once per declaration by the kernel's cache).
pub fn op_keys(ev: &Evaluator, alpha: u64, keys: &mut std::collections::HashSet<u64>) -> usize {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let b = ev.b;
    let kind = |code: usize| -> u8 {
        match code {
            0 => 0,
            1 => 1,
            c => { let j = c - 2; if j < b { 2 } else { ((alpha >> (j - b)) & 1) as u8 } }
        }
    };
    let h2 = |tag: u8, a: u64, c: u64| -> u64 { let mut h = DefaultHasher::new(); (tag, a, c).hash(&mut h); h.finish() };
    let mut count = 0usize;
    // value: 0 = false, 1 = true, otherwise hash of canonical expression (>= 2)
    let dot = |terms: &[(usize, usize)], keys: &mut std::collections::HashSet<u64>, count: &mut usize| -> u64 {
        let mut acc: u64 = 0;
        for &(i, j) in terms {
            let (x, y) = (kind(i), kind(j));
            if x == 0 || y == 0 { continue; }
            if x == 1 && y == 1 { return 1; }
            let term = if x == 2 && y == 2 {
                let k = h2(1, i.min(j) as u64, i.max(j) as u64) | 2;
                if keys.insert(k) { *count += 1; }
                k
            } else if x == 2 { h2(0, i as u64, 0) | 2 } else { h2(0, j as u64, 0) | 2 };
            acc = if acc == 0 { term } else {
                let k = h2(2, acc, term) | 2;
                if keys.insert(k) { *count += 1; }
                k
            };
        }
        acc
    };
    let mut bad: u64 = 0;
    for (l, r) in &ev.terms {
        let vl = dot(l, keys, &mut count);
        let vr = dot(r, keys, &mut count);
        if vl <= 1 && vr <= 1 {
            if vl != vr { break; }
            continue;
        }
        if vl == vr { continue; }
        let (a, c) = (vl.min(vr), vl.max(vr));
        let x = h2(3, a, c) | 2;
        if keys.insert(x) { count += 1; }
        bad = if bad == 0 { x } else {
            let k = h2(4, bad, x) | 2;
            if keys.insert(k) { count += 1; }
            k
        };
    }
    count
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

    pub fn leaf(&mut self, alpha: u64) -> u64 {
        let words = self.ev.words;
        let mut bad = vec![0u64; words];
        for qi in 0..self.masks.len() {
            let (m1, m2) = self.masks[qi];
            let lt = self.side(qi, 0, alpha & m1);
            let rt = self.side(qi, 1, alpha & m2);
            match (&*lt, &*rt) {
                (Tab::F, Tab::F) | (Tab::T, Tab::T) => {}
                (Tab::F, Tab::T) | (Tab::T, Tab::F) => return 0,
                (Tab::F, Tab::M(m)) | (Tab::M(m), Tab::F) => bad.iter_mut().zip(m).for_each(|(a, b)| *a |= b),
                (Tab::T, Tab::M(m)) | (Tab::M(m), Tab::T) => bad.iter_mut().zip(m).for_each(|(a, b)| *a |= !b),
                (Tab::M(m1), Tab::M(m2)) => bad.iter_mut().zip(m1.iter().zip(m2)).for_each(|(a, (x, y))| *a |= x ^ y),
            }
        }
        let mut cnt = 0u64;
        for (i, w) in bad.iter().enumerate() {
            let m = if i + 1 == words { self.ev.mask } else { u64::MAX };
            cnt += (!w & m).count_ones() as u64;
        }
        cnt
    }
}

/// Number of distinct big-number operations the kernel performs for one more leaf with the
/// memoised evaluator (`RACert.Problem.leafR`), given the set `keys` of canonical expressions
/// already evaluated in the current declaration. `qm` are the blocks of quadruple indices.
pub fn op_keys_memo(ev: &Evaluator, masks: &[(u64, u64)], blocks: &[Vec<usize>], alpha: u64, keys: &mut std::collections::HashSet<u64>, cat: &mut [usize; 6]) -> usize {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let b = ev.b;
    let h3 = |tag: u8, a: u64, c: u64, d: u64| -> u64 { let mut h = DefaultHasher::new(); (tag, a, c, d).hash(&mut h); h.finish() | 2 };
    let mut count = 0usize;
    // value of one side: 0 false, 1 true, else key of its canonical expression
    let side = |qi: usize, sd: u8, r: u64, keys: &mut std::collections::HashSet<u64>, count: &mut usize, cat: &mut [usize; 6]| -> u64 {
        let terms = if sd == 0 { &ev.terms[qi].0 } else { &ev.terms[qi].1 };
        let kind = |code: usize| -> u8 {
            match code { 0 => 0, 1 => 1, c => { let j = c - 2; if j < b { 2 } else { ((r >> (j - b)) & 1) as u8 } } }
        };
        // is the value a constant?
        let mut any = false;
        for &(i, j) in terms {
            let (x, y) = (kind(i), kind(j));
            if x == 0 || y == 0 { continue; }
            if x == 1 && y == 1 { return 1; }
            any = true;
        }
        if !any { return 0; }
        let key = h3(10 + sd, qi as u64, r, 0);
        if keys.insert(key) {
            // first evaluation of this residual: its internal operations
            let mut acc: u64 = 0;
            for &(i, j) in terms {
                let (x, y) = (kind(i), kind(j));
                if x == 0 || y == 0 { continue; }
                let term = if x == 2 && y == 2 {
                    let k = h3(1, i.min(j) as u64, i.max(j) as u64, 0);
                    if keys.insert(k) { *count += 1; cat[1] += 1; }
                    k
                } else if x == 2 { h3(0, i as u64, 0, 0) } else { h3(0, j as u64, 0, 0) };
                acc = if acc == 0 { term } else {
                    let k = h3(2, acc, term, 0);
                    if keys.insert(k) { *count += 1; cat[2] += 1; }
                    k
                };
            }
        }
        key
    };
    if std::env::var("CERTGEN_TREE").is_ok() {
        // balanced tree of disjunctions over all quadruples in order
        let order: Vec<usize> = blocks.iter().flatten().cloned().collect();
        let mut vals: Vec<u64> = vec![];
        for &qi in &order {
            let (m1, m2) = masks[qi];
            let vl = side(qi, 0, alpha & m1, keys, &mut count, cat);
            let vr = side(qi, 1, alpha & m2, keys, &mut count, cat);
            if vl <= 1 && vr <= 1 {
                if vl != vr { return count; }
                vals.push(0);
                continue;
            }
            let q = h3(3, vl, vr, 0);
            if keys.insert(q) { count += 1; cat[3] += 1; }
            vals.push(q);
        }
        while vals.len() > 1 {
            let mut next = vec![];
            for pair in vals.chunks(2) {
                let v = if pair.len() == 1 || pair[1] == 0 { pair[0] } else if pair[0] == 0 { pair[1] } else {
                    let k = h3(6, pair[0], pair[1], 0);
                    if keys.insert(k) { count += 1; cat[4] += 1; }
                    k
                };
                next.push(v);
            }
            vals = next;
        }
        return count;
    }
    let mut bad: u64 = 0;
    for blk in blocks {
        let mut acc: u64 = 0;
        for &qi in blk {
            let (m1, m2) = masks[qi];
            let vl = side(qi, 0, alpha & m1, keys, &mut count, cat);
            let vr = side(qi, 1, alpha & m2, keys, &mut count, cat);
            if vl <= 1 && vr <= 1 {
                if vl != vr { return count; }
                continue;
            }
            let q = h3(3, vl, vr, 0);
            if keys.insert(q) { count += 1; cat[3] += 1; } // xor (not counted when the two sides are equal tables; unknown here)
            acc = if acc == 0 { q } else {
                let k = h3(4, acc, q, 0);
                if keys.insert(k) { count += 1; cat[4] += 1; }
                k
            };
        }
        if acc != 0 {
            bad = if bad == 0 { acc } else {
                let k = h3(5, bad, acc, 0);
                if keys.insert(k) { count += 1; cat[5] += 1; }
                k
            };
        }
    }
    count
}
