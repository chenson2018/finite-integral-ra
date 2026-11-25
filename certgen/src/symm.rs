//! Symmetries of a counting problem and the reduction of the high assignments to orbit minima.

use crate::problem::Problem;
use crate::sys::{compose, inverse, Sys};
use crate::tree::Tree;

/// A symmetry of the problem: an atom permutation and the induced permutation of variables.
#[derive(Clone)]
pub struct Sym {
    pub h: Vec<usize>,
    pub hi: Vec<usize>,
    pub vp: Vec<usize>,
    pub vq: Vec<usize>,
}

/// Permutation of the variables induced by the atom permutation `h` (which must normalise the
/// classes of `p`).
pub fn var_perm(p: &Problem, h: &[usize]) -> Vec<usize> {
    let k = p.k;
    (0..p.nvars)
        .map(|j| {
            let x = p.reps[j];
            let (a, b, c) = (x / k / k, x / k % k, x % k);
            p.cls[p.tcode(h[a], h[b], h[c])] - 2
        })
        .collect()
}

/// The elements of `g` commuting with `sigma`.
pub fn centralizer(g: &[Vec<usize>], sigma: &[usize]) -> Vec<Vec<usize>> {
    g.iter().filter(|h| compose(h, sigma) == compose(sigma, h)).cloned().collect()
}

/// Orbits of the variables under the group `hs`.
pub fn var_orbits(p: &Problem, hs: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let perms: Vec<Vec<usize>> = hs.iter().map(|h| var_perm(p, h)).collect();
    let mut seen = vec![false; p.nvars];
    let mut orbits = vec![];
    for j in 0..p.nvars {
        if seen[j] {
            continue;
        }
        let mut o: Vec<usize> = perms.iter().map(|pm| pm[j]).collect();
        o.sort();
        o.dedup();
        for &x in &o {
            seen[x] = true;
        }
        orbits.push(o);
    }
    orbits
}

/// The group of permutations of the high variables induced by the symmetries, with a symmetry
/// realising each of them, and its multiplication and inversion tables.
pub struct BitGroup {
    pub t: usize,
    /// (p, q): bit `i` moves to `p[i]`; `q` is the inverse.
    pub perms: Vec<(Vec<usize>, Vec<usize>)>,
    pub syms: Vec<Sym>,
    pub comp: Vec<Vec<usize>>,
    pub inv: Vec<usize>,
}

impl BitGroup {
    pub fn new(p: &Problem, b: usize, hs: &[Vec<usize>]) -> BitGroup {
        let t = p.nvars - b;
        let mut items: Vec<(Vec<usize>, Sym)> = vec![];
        for h in hs {
            let vp = var_perm(p, h);
            let vq = inverse(&vp);
            for j in 0..p.nvars {
                assert_eq!(j < b, vp[j] < b, "symmetry does not preserve the low variables");
            }
            let top: Vec<usize> = (0..t).map(|i| vp[b + i] - b).collect();
            items.push((top, Sym { h: h.clone(), hi: inverse(h), vp, vq }));
        }
        // identity first, then lexicographic; duplicates removed
        items.sort_by(|x, y| x.0.cmp(&y.0));
        items.dedup_by(|x, y| x.0 == y.0);
        let perms: Vec<(Vec<usize>, Vec<usize>)> = items.iter().map(|(p, _)| (p.clone(), inverse(p))).collect();
        assert!(perms[0].0.iter().enumerate().all(|(i, &x)| i == x));
        let index = |q: &Vec<usize>| perms.binary_search_by(|x| x.0.cmp(q)).expect("not closed");
        let comp = perms.iter().map(|(pi, _)| perms.iter().map(|(pj, _)| index(&compose(pi, pj))).collect()).collect();
        let inv = perms.iter().map(|(_, q)| index(q)).collect();
        BitGroup { t, perms, syms: items.into_iter().map(|x| x.1).collect(), comp, inv }
    }

    #[inline]
    pub fn act(&self, i: usize, alpha: u64) -> u64 {
        let p = &self.perms[i].0;
        let mut r = 0u64;
        let mut a = alpha;
        let mut j = 0;
        while a != 0 {
            if a & 1 == 1 {
                r |= 1 << p[j];
            }
            a >>= 1;
            j += 1;
        }
        r
    }
}

/// An orbit minimum of the high assignments.
#[derive(Clone, Debug)]
pub struct Rep {
    pub alpha: u64,
    /// Orbit size.
    pub m: u64,
    /// Code of a quadruple whose condition is violated by the high variables alone, if any.
    pub dead: Option<usize>,
}

/// All orbit minima in `[lo, hi)`.
pub fn reps_in(p: &Problem, b: usize, grp: &BitGroup, tree: &Tree, lo: u64, hi: u64) -> Vec<Rep> {
    let n = grp.perms.len();
    let mut out = vec![];
    let mut assign = vec![2u8; p.nvars];
    'outer: for alpha in lo..hi {
        let mut stab = 0u64;
        for i in 0..n {
            let a2 = grp.act(i, alpha);
            if a2 < alpha {
                continue 'outer;
            }
            if a2 == alpha {
                stab += 1;
            }
        }
        for i in 0..grp.t {
            assign[b + i] = ((alpha >> i) & 1) as u8;
        }
        let dead = tree.dead(&assign).map(|qi| p.quads[qi]);
        out.push(Rep { alpha, m: n as u64 / stab, dead });
    }
    out
}

/// All orbit minima, computed in parallel.
pub fn all_reps(p: &Problem, b: usize, grp: &BitGroup) -> Vec<Rep> {
    let total: u64 = 1 << grp.t;
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(10) as u64;
    let pieces = (nthreads * 8).min(total);
    let step = total / pieces;
    let tree = Tree::new(p, b);
    let mut results: Vec<Vec<Rep>> = vec![vec![]; pieces as usize];
    let next = std::sync::atomic::AtomicUsize::new(0);
    let slots: Vec<std::sync::Mutex<Vec<Rep>>> = (0..pieces).map(|_| std::sync::Mutex::new(vec![])).collect();
    std::thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= pieces as usize {
                    break;
                }
                let lo = i as u64 * step;
                let hi = if i as u64 + 1 == pieces { total } else { lo + step };
                *slots[i].lock().unwrap() = reps_in(p, b, grp, &tree, lo, hi);
            });
        }
    });
    for (i, s) in slots.into_iter().enumerate() {
        results[i] = s.into_inner().unwrap();
    }
    results.concat()
}

/// Estimated kernel time (seconds) of the symmetry-reduced certificate of a class.
pub fn estimate(p: &Problem, b: usize, grp: &BitGroup, reps: &[Rep]) -> f64 {
    // Calibrated on measured kernel times: about 0.35 ms of small reduction steps per quadruple,
    // about five big-number operations per quadruple at 127 µs each for tables of 2^20 bits
    // (linear in the table size), and 30 ms of fixed cost per leaf.
    let live = reps.iter().filter(|r| r.dead.is_none()).count() as f64;
    let dead = reps.len() as f64 - live;
    let leaf = 0.03 + p.quads.len() as f64 * (0.00035 + 5.0 * 127e-6 * (2f64).powi(b as i32 - 20));
    let rep = 0.0003 + grp.perms.len() as f64 * grp.t as f64 * 3e-6;
    live * leaf + reps.len() as f64 * rep + dead * 0.0008
}

/// Choose the low variables as a union of orbits of variables under the symmetries `hs`, of
/// total size at most `bmax`, minimising the estimated checking time. Returns the numbering of
/// the variables (low ones first) and `b`.
pub fn choose_low(sys: &Sys, sigma: &[usize], hs: &[Vec<usize>], bmax: usize) -> (Vec<usize>, usize) {
    let base = Problem::new(sys, sigma, &|_p, roots| roots);
    let orbits = var_orbits(&base, hs);
    let sizes: Vec<usize> = orbits.iter().map(|o| o.len()).collect();
    let no = orbits.len();
    let roots_of = |mask: u64| -> (Vec<usize>, usize) {
        let mut order: Vec<usize> = vec![];
        for (i, o) in orbits.iter().enumerate() {
            if mask >> i & 1 == 1 {
                order.extend(o);
            }
        }
        let b = order.len();
        for (i, o) in orbits.iter().enumerate() {
            if mask >> i & 1 == 0 {
                order.extend(o);
            }
        }
        (order.into_iter().map(|j| base.reps[j]).collect(), b)
    };
    if base.nvars <= bmax {
        return roots_of((1u64 << no) - 1);
    }
    assert!(no <= 30, "too many variable orbits");
    // candidate subsets: total size in [bmax - 6, bmax], at most 26 high variables
    let mut cands: Vec<u64> = vec![];
    for mask in 0u64..(1 << no) {
        let sz: usize = (0..no).filter(|i| mask >> i & 1 == 1).map(|i| sizes[i]).sum();
        if sz <= bmax && sz + 6 >= bmax && base.nvars - sz <= 26 {
            cands.push(mask);
        }
    }
    if cands.is_empty() {
        // fall back to the largest low set that fits
        let mut best = (0usize, 0u64);
        for mask in 0u64..(1 << no) {
            let sz: usize = (0..no).filter(|i| mask >> i & 1 == 1).map(|i| sizes[i]).sum();
            if sz <= bmax && sz > best.0 {
                best = (sz, mask);
            }
        }
        return roots_of(best.1);
    }
    // sample if there are too many candidates
    let stride = cands.len().div_ceil(40);
    let mut best: Option<(f64, u64)> = None;
    for &mask in cands.iter().step_by(stride) {
        let (roots, b) = roots_of(mask);
        let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
        let p = Problem::new(sys, sigma, &order);
        let grp = BitGroup::new(&p, b, hs);
        let reps = all_reps(&p, b, &grp);
        let est = estimate(&p, b, &grp, &reps);
        if best.is_none() || est < best.unwrap().0 {
            best = Some((est, mask));
        }
    }
    roots_of(best.unwrap().1)
}
