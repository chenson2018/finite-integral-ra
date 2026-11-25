//! The counting problem attached to a symmetry `sigma`, with its certificate data.

use crate::sys::{inverse, Sys};
use std::collections::VecDeque;

pub struct Problem {
    pub s: usize,
    pub n: usize,
    pub k: usize,
    pub conv: Vec<usize>,
    pub perm: Vec<usize>,
    pub pinv: Vec<usize>,
    /// Number of variables.
    pub nvars: usize,
    /// Class of each triple `(a*k+b)*k+c`: 0 absent, 1 present, `j+2` variable `j`.
    pub cls: Vec<usize>,
    /// Code of the representative triple of each variable.
    pub reps: Vec<usize>,
    /// Word (base 8, first digit applied first) leading from each triple to its representative.
    pub path: Vec<u128>,
    /// Codes `((r*k+u)*k+t)*k+p` of the quadruples to check.
    pub quads: Vec<usize>,
    /// Word (base 4) leading from each quadruple into `quads`.
    pub wit: Vec<u128>,
}

/// Breadth-first search over an orbit: `fwd[d-1]` are the generators (digit `d`), `bwd[d-1]`
/// their inverses. Returns, for every element `x` of the orbit of `root`, a word `w` (in base
/// `base`, first digit applied first) such that following `w` from `x` leads to `root`.
fn orbit_words(root: usize, bwd: &[&dyn Fn(usize) -> usize], base: u128) -> Vec<(usize, u128)> {
    let mut out = vec![(root, 0u128)];
    let mut seen = std::collections::HashMap::new();
    seen.insert(root, 0u128);
    let mut q = VecDeque::new();
    q.push_back(root);
    while let Some(y) = q.pop_front() {
        let wy = seen[&y];
        for (i, g) in bwd.iter().enumerate() {
            // x = g^{-1}(y), so applying generator `i+1` to x gives y.
            let x = g(y);
            if !seen.contains_key(&x) {
                assert!(wy < u128::MAX / (base * base), "word too long");
                let w = (i as u128 + 1) + base * wy;
                seen.insert(x, w);
                out.push((x, w));
                q.push_back(x);
            }
        }
    }
    out
}

impl Problem {
    pub fn tcode(&self, a: usize, b: usize, c: usize) -> usize {
        (a * self.k + b) * self.k + c
    }
    /// Build the problem for `sigma`. `order` chooses the numbering of the variables: it receives
    /// the list of orbit representatives (triple codes, increasing) and returns them in the order
    /// in which they should be numbered.
    pub fn new(sys: &Sys, sigma: &[usize], order: &dyn Fn(&Problem, Vec<usize>) -> Vec<usize>) -> Problem {
        let k = sys.k;
        let pinv = inverse(sigma);
        let mut p = Problem {
            s: sys.s,
            n: sys.n,
            k,
            conv: sys.conv.clone(),
            perm: sigma.to_vec(),
            pinv,
            nvars: 0,
            cls: vec![0; k * k * k],
            reps: vec![],
            path: vec![0; k * k * k],
            quads: vec![],
            wit: vec![0; k * k * k * k],
        };
        let cv = p.conv.clone();
        let pm = p.perm.clone();
        let pi = p.pinv.clone();
        let dec3 = move |x: usize| (x / k / k, x / k % k, x % k);
        let enc3 = move |a: usize, b: usize, c: usize| (a * k + b) * k + c;
        // generators on triples: 1 left, 2 right, 3 sigma, 4 sigma^{-1}; all listed as inverses
        let (cv1, cv2) = (cv.clone(), cv.clone());
        let (pm1, pi1) = (pm.clone(), pi.clone());
        let left = move |x: usize| { let (a, b, c) = dec3(x); enc3(cv1[a], c, b) };
        let right = move |x: usize| { let (a, b, c) = dec3(x); enc3(c, cv2[b], a) };
        let sig = move |x: usize| { let (a, b, c) = dec3(x); enc3(pm1[a], pm1[b], pm1[c]) };
        let sigi = move |x: usize| { let (a, b, c) = dec3(x); enc3(pi1[a], pi1[b], pi1[c]) };
        // inverse of generator d: left, right are involutions; sigma^{-1}; (sigma^{-1})^{-1}
        let bwd3: Vec<&dyn Fn(usize) -> usize> = vec![&left, &right, &sigi, &sig];
        // identity triples
        for a in 0..k {
            for b in 0..k {
                for c in 0..k {
                    let x = enc3(a, b, c);
                    if a == 0 {
                        p.cls[x] = (b == c) as usize;
                    } else if b == 0 {
                        p.cls[x] = (a == c) as usize;
                    } else if c == 0 {
                        p.cls[x] = (b == cv[a]) as usize;
                    }
                }
            }
        }
        // orbits of diversity triples
        let mut orbit_of = vec![usize::MAX; k * k * k];
        let mut roots = vec![];
        for a in 1..k {
            for b in 1..k {
                for c in 1..k {
                    let x = enc3(a, b, c);
                    if orbit_of[x] != usize::MAX {
                        continue;
                    }
                    for (y, w) in orbit_words(x, &bwd3, 8) {
                        orbit_of[y] = x;
                        p.path[y] = w;
                    }
                    roots.push(x);
                }
            }
        }
        let ordered = order(&p, roots.clone());
        assert_eq!(ordered.len(), roots.len());
        p.nvars = ordered.len();
        let mut var_of_root = std::collections::HashMap::new();
        for (j, &r) in ordered.iter().enumerate() {
            var_of_root.insert(r, j);
        }
        p.reps = ordered;
        for a in 1..k {
            for b in 1..k {
                for c in 1..k {
                    let x = enc3(a, b, c);
                    p.cls[x] = var_of_root[&orbit_of[x]] + 2;
                }
            }
        }
        // quadruples
        let dec4 = move |x: usize| (x / k / k / k, x / k / k % k, x / k % k, x % k);
        let enc4 = move |r: usize, u: usize, t: usize, q: usize| ((r * k + u) * k + t) * k + q;
        let (cva, cvb) = (cv.clone(), cv.clone());
        let pi2 = pi.clone();
        // inverse of rot: (r,u,t,p) -> (cv p, r, u, cv t); flip is an involution; sigma^{-1}
        let roti = move |x: usize| { let (r, u, t, q) = dec4(x); enc4(cva[q], r, u, cva[t]) };
        let flip = move |x: usize| { let (r, u, t, q) = dec4(x); enc4(cvb[t], cvb[u], cvb[r], cvb[q]) };
        let sig4i = move |x: usize| { let (r, u, t, q) = dec4(x); enc4(pi2[r], pi2[u], pi2[t], pi2[q]) };
        let bwd4: Vec<&dyn Fn(usize) -> usize> = vec![&roti, &flip, &sig4i];
        let mut done = vec![false; k * k * k * k];
        for r in 1..k {
            for u in 1..k {
                for t in 1..k {
                    for q in 1..k {
                        let x = enc4(r, u, t, q);
                        if done[x] {
                            continue;
                        }
                        for (y, w) in orbit_words(x, &bwd4, 4) {
                            done[y] = true;
                            p.wit[y] = w;
                        }
                        p.quads.push(x);
                    }
                }
            }
        }
        p
    }

    /// Variables occurring in the two sides of a quadruple's condition, as (left pairs, right
    /// pairs) of class codes.
    pub fn quad_terms(&self, x: usize) -> (Vec<(usize, usize)>, Vec<(usize, usize)>) {
        let k = self.k;
        let (r, u, t, p) = (x / k / k / k, x / k / k % k, x / k % k, x % k);
        let cv = &self.conv;
        let mut l = vec![];
        let mut rr = vec![];
        for q in 0..k {
            l.push((self.cls[self.tcode(cv[r], p, q)], self.cls[self.tcode(u, t, q)]));
            rr.push((self.cls[self.tcode(r, u, q)], self.cls[self.tcode(p, cv[t], q)]));
        }
        (l, rr)
    }
}

impl Problem {
    /// Masks of the high variables (relative to `b`) occurring in the two sides of the condition
    /// of the quadruple with code `x`.
    pub fn quad_masks(&self, x: usize, b: usize) -> (u64, u64) {
        let (l, r) = self.quad_terms(x);
        let mask = |terms: &Vec<(usize, usize)>| -> u64 {
            let mut m = 0u64;
            for &(i, j) in terms {
                for c in [i, j] {
                    if c >= b + 2 {
                        m |= 1 << (c - 2 - b);
                    }
                }
            }
            m
        };
        (mask(&l), mask(&r))
    }

    /// Order the quadruples so that those depending only on slowly changing high variables (high
    /// bits of `alpha`) come first, and return them in blocks with their masks.
    pub fn order_quads(&mut self, b: usize, block: usize) -> Vec<Vec<(usize, u64, u64)>> {
        let mut items: Vec<(usize, u64, u64)> = self.quads.iter().map(|&x| { let (m1, m2) = self.quad_masks(x, b); (x, m1, m2) }).collect();
        // key: lowest relevant high variable, descending; quadruples without high variables first
        items.sort_by_key(|&(x, m1, m2)| {
            let m = m1 | m2;
            let low = if m == 0 { 64 } else { m.trailing_zeros() as usize };
            (std::cmp::Reverse(low), std::cmp::Reverse(m), x)
        });
        self.quads = items.iter().map(|e| e.0).collect();
        items.chunks(block).map(|c| c.to_vec()).collect()
    }
}
