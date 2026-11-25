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
    /// Generators `g` (as indices) with their rows of the multiplication table, such that every
    /// index `i != 0` is `row[j]` for some generator row and some `j < i`.
    pub fn gens(&self) -> Vec<(usize, Vec<usize>)> {
        let n = self.perms.len();
        let mut covered = vec![false; n];
        covered[0] = true;
        let mut out = vec![];
        for i in 1..n {
            if covered[i] {
                continue;
            }
            // take i itself as a generator: i = i * identity with 0 < i
            let row = self.comp[i].clone();
            for (j, &c) in row.iter().enumerate() {
                if j < c {
                    covered[c] = true;
                }
            }
            out.push((i, row));
        }
        assert!(covered.iter().all(|&x| x));
        out
    }

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
pub fn all_reps(p: &Problem, b: usize, m: usize, grp: &BitGroup) -> Vec<Rep> {
    let total: u64 = 1 << grp.t;
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(10) as u64;
    let pieces = (nthreads * 8).min(total);
    let step = total / pieces;
    let tree = Tree::new_elim(p, b, m);
    let b = b + m;
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

/// Estimated kernel time (seconds, on one thread) of one evaluated leaf and of one orbit
/// minimum, with tables of `2^b` bits and `m` eliminated variables.
pub fn leaf_cost(_p: &Problem, b: usize, m: usize) -> (f64, f64) {
    // Calibrated on measured kernel times:
    // about 2 ms of small reduction steps per leaf, and 54 µs per big-number operation on tables
    // of 2^20 bits, linear in the table size; larger tables do not fit into the processor caches
    // together with their operands and cost more per bit, in particular when several files are
    // checked in parallel. About 0.6 ms per orbit minimum.
    let penalty = match b { 0..=20 => 1.0, 21 => 1.5, _ => 2.5 };
    let per_op = 54e-6 * (2f64).powi(b as i32 - 20) * penalty;
    (0.002 + crate::lean::leaf_ops(m) as f64 * per_op, 0.0006)
}

/// The variables to eliminate: a union of orbits of variables under the symmetries `hs` no two
/// of which occur in the condition of the same quadruple.
pub fn choose_elim(base: &Problem, orbits: &[Vec<usize>]) -> Vec<usize> {
    let v = base.nvars;
    let mut adj = vec![0u64; v];
    for &x in &base.quads {
        let d = base.quad_deps(x);
        for a in 0..v {
            if d >> a & 1 == 1 {
                adj[a] |= d & !(1 << a);
            }
        }
    }
    let mut chosen: Vec<usize> = vec![];
    let mut cm = 0u64;
    for (i, o) in orbits.iter().enumerate() {
        let om: u64 = o.iter().fold(0, |m, &a| m | 1 << a);
        if o.iter().all(|&a| adj[a] & (om | cm) == 0) {
            chosen.push(i);
            cm |= om;
        }
    }
    chosen
}

/// Choose the eliminated variables and the low variables, each a union of orbits of variables
/// under the symmetries `hs`, with at most `bmax` low variables, minimising the estimated
/// checking time. Returns the numbering of the variables (low ones first, then the eliminated
/// ones), the number `b` of low variables and the number `m` of eliminated variables.
pub fn choose_low(sys: &Sys, sigma: &[usize], hs: &[Vec<usize>], bmax: usize) -> (Vec<usize>, usize, usize) {
    let base = Problem::new(sys, sigma, &|_p, roots| roots);
    let orbits = var_orbits(&base, hs);
    let elim = choose_elim(&base, &orbits);
    let zs: Vec<usize> = elim.iter().flat_map(|&i| orbits[i].clone()).collect();
    let m = zs.len();
    let orbits: Vec<Vec<usize>> = orbits.into_iter().enumerate().filter(|(i, _)| !elim.contains(i)).map(|x| x.1).collect();
    let sizes: Vec<usize> = orbits.iter().map(|o| o.len()).collect();
    let no = orbits.len();
    // number of quadruples in which each variable occurs
    let mut occ = vec![0usize; base.nvars];
    for &x in &base.quads {
        let d = base.quad_deps(x);
        for (v, o) in occ.iter_mut().enumerate() {
            if d >> v & 1 == 1 {
                *o += 1;
            }
        }
    }
    let roots_of = |mask: u64| -> (Vec<usize>, usize, usize) {
        let mut order: Vec<usize> = vec![];
        for (i, o) in orbits.iter().enumerate() {
            if mask >> i & 1 == 1 {
                order.extend(o);
            }
        }
        let b = order.len();
        order.extend(&zs);
        // high variables: those occurring in few quadruples get the low bits of `alpha`, which
        // change fastest between consecutive leaves, so that most residuals are shared
        let mut high: Vec<usize> = vec![];
        for (i, o) in orbits.iter().enumerate() {
            if mask >> i & 1 == 0 {
                high.extend(o);
            }
        }
        high.sort_by_key(|&j| (occ[j], j));
        order.extend(high);
        (order.into_iter().map(|j| base.reps[j]).collect(), b, m)
    };
    if base.nvars - m <= bmax {
        return roots_of((1u64 << no) - 1);
    }
    assert!(no <= 30, "too many variable orbits");
    // candidate subsets: total size in [bmax - 6, bmax], at most 34 high variables
    let mut cands: Vec<u64> = vec![];
    for mask in 0u64..(1 << no) {
        let sz: usize = (0..no).filter(|i| mask >> i & 1 == 1).map(|i| sizes[i]).sum();
        if sz <= bmax && sz + 6 >= bmax && base.nvars - m - sz <= 34 {
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
    let stride = cands.len().div_ceil(160);
    let mut best: Option<(f64, u64)> = None;
    for &mask in cands.iter().step_by(stride) {
        let (roots, b, m) = roots_of(mask);
        let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
        let p = Problem::new(sys, sigma, &order);
        let grp = BitGroup::new(&p, b + m, hs);
        let (canon, live) = sample_reps(&p, b, m, &grp);
        let (per_leaf, per_rep) = leaf_cost(&p, b, m);
        let est = live * per_leaf + canon * per_rep;
        if best.is_none() || est < best.unwrap().0 {
            best = Some((est, mask));
        }
    }
    roots_of(best.unwrap().1)
}

/// The numbers of orbit minima and of live orbit minima: exact for at most `2^22` high
/// assignments, otherwise estimated from a pseudo-random sample.
pub fn sample_reps(p: &Problem, b: usize, m: usize, grp: &BitGroup) -> (f64, f64) {
    if grp.t <= 22 {
        let reps = all_reps(p, b, m, grp);
        return (reps.len() as f64, reps.iter().filter(|r| r.dead.is_none()).count() as f64);
    }
    let tree = Tree::new_elim(p, b, m);
    let samples = 1u64 << 18;
    let mut x: u64 = 0x9E3779B97F4A7C15;
    let (mut canon, mut live) = (0u64, 0u64);
    let mut assign = vec![2u8; p.nvars];
    for _ in 0..samples {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let alpha = (x >> 20) & ((1u64 << grp.t) - 1);
        if (0..grp.perms.len()).any(|i| grp.act(i, alpha) < alpha) {
            continue;
        }
        canon += 1;
        for i in 0..grp.t {
            assign[b + m + i] = ((alpha >> i) & 1) as u8;
        }
        if tree.dead(&assign).is_none() {
            live += 1;
        }
    }
    let scale = (1u64 << grp.t) as f64 / samples as f64;
    (canon as f64 * scale, live as f64 * scale)
}
