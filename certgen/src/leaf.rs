//! Bit-parallel evaluation of leaves, mirroring the Lean definitions `RACert.Problem.leaf`.

use crate::problem::Problem;

#[derive(Clone)]
enum Tab {
    F,
    T,
    M(Vec<u64>),
}

pub struct Evaluator<'a> {
    p: &'a Problem,
    b: usize,
    words: usize,
    mask: u64,
    pats: Vec<Vec<u64>>,
    terms: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>,
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
