// Prototype 2: memoized model counting with residual-formula caching and component decomposition.
use std::collections::HashMap;

struct Sys { k: usize, conv: Vec<usize> }
impl Sys {
    fn new(s: usize, n: usize) -> Sys {
        let k = 1 + s + 2 * n;
        let mut conv: Vec<usize> = (0..k).collect();
        for i in 0..n { conv[1 + s + 2 * i] = 1 + s + 2 * i + 1; conv[1 + s + 2 * i + 1] = 1 + s + 2 * i; }
        Sys { k, conv }
    }
    fn code(&self, a: usize, b: usize, c: usize) -> usize { (a * self.k + b) * self.k + c }
}
fn find(p: &mut Vec<usize>, x: usize) -> usize { let mut r = x; while p[r] != r { r = p[r]; } let mut y = x; while p[y] != r { let n = p[y]; p[y] = r; y = n; } r }

#[derive(Clone, Copy, PartialEq, Eq)]
enum T { False, True, Var(usize) }

type Mask = u64;
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct Con { prem: Mask, concl: Vec<Mask> }

fn build(sys: &Sys, sigma: &[usize]) -> (usize, Vec<Con>) {
    let k = sys.k; let n3 = k * k * k;
    let mut uf: Vec<usize> = (0..n3).collect();
    let union = |uf: &mut Vec<usize>, a: usize, b: usize| { let ra = find(uf, a); let rb = find(uf, b); if ra != rb { let (lo, hi) = if ra < rb { (ra, rb) } else { (rb, ra) }; uf[hi] = lo; } };
    for a in 1..k { for b in 1..k { for c in 1..k {
        let x = sys.code(a, b, c);
        union(&mut uf, x, sys.code(sys.conv[a], c, b));
        union(&mut uf, x, sys.code(c, sys.conv[b], a));
        union(&mut uf, x, sys.code(sigma[a], sigma[b], sigma[c]));
    }}}
    let mut varid: HashMap<usize, usize> = HashMap::new();
    let mut tv = vec![T::False; n3];
    for a in 0..k { for b in 0..k { for c in 0..k {
        let x = sys.code(a, b, c);
        tv[x] = if a == 0 { if b == c { T::True } else { T::False } }
        else if b == 0 { if a == c { T::True } else { T::False } }
        else if c == 0 { if b == sys.conv[a] { T::True } else { T::False } }
        else { let r = find(&mut uf, x); let l = varid.len(); T::Var(*varid.entry(r).or_insert(l)) };
    }}}
    let nvars = varid.len();
    let mut cons: Vec<Con> = vec![];
    for r in 0..k { for s in 0..k { for t in 0..k { for p in 0..k {
        let mut concl: Vec<Mask> = vec![]; let mut concl_true = false;
        for q2 in 0..k {
            let x = tv[sys.code(q2, t, p)]; let y = tv[sys.code(r, s, q2)];
            if x == T::False || y == T::False { continue; }
            let mut m: Mask = 0;
            if let T::Var(v) = x { m |= 1 << v; } if let T::Var(v) = y { m |= 1 << v; }
            if m == 0 { concl_true = true; }
            concl.push(m);
        }
        if concl_true { continue; }
        for q in 0..k {
            let x = tv[sys.code(r, q, p)]; let y = tv[sys.code(s, t, q)];
            if x == T::False || y == T::False { continue; }
            let mut prem: Mask = 0;
            if let T::Var(v) = x { prem |= 1 << v; } if let T::Var(v) = y { prem |= 1 << v; }
            let mut c2: Vec<Mask> = concl.iter().map(|c| c & !prem).collect();
            if c2.iter().any(|&c| c == 0) { continue; }
            norm_concl(&mut c2);
            cons.push(Con { prem, concl: c2 });
        }
    }}}}
    cons.sort(); cons.dedup();
    (nvars, cons)
}

fn norm_concl(c: &mut Vec<Mask>) {
    c.sort(); c.dedup();
    let cc = c.clone();
    c.retain(|&x| !cc.iter().any(|&d| d != x && (d & x) == d));
}

// Simplify a formula under assignment (tr = true vars, fa = false vars), with unit propagation.
// Returns None on conflict; else (residual constraints, forced-true mask, forced-false mask).
fn simplify(cons: &[Con], mut tr: Mask, mut fa: Mask) -> Option<(Vec<Con>, Mask, Mask)> {
    let mut cur: Vec<Con> = cons.to_vec();
    loop {
        let mut next: Vec<Con> = Vec::with_capacity(cur.len());
        let mut changed = false;
        for c in &cur {
            if c.prem & fa != 0 { continue; }
            let prem = c.prem & !tr;
            let mut concl: Vec<Mask> = Vec::with_capacity(c.concl.len());
            let mut sat = false;
            for &m in &c.concl {
                if m & fa != 0 { continue; }
                let m2 = m & !tr & !prem; // within the constraint premise vars may be assumed true
                if m2 == 0 { sat = true; break; }
                concl.push(m2);
            }
            if sat { continue; }
            if concl.is_empty() {
                if prem == 0 { return None; }
                if prem.count_ones() == 1 { fa |= prem; changed = true; continue; }
            } else if prem == 0 && concl.len() == 1 {
                tr |= concl[0]; changed = true; continue;
            }
            norm_concl(&mut concl);
            if prem == 0 && concl.len() == 1 { tr |= concl[0]; changed = true; continue; }
            next.push(Con { prem, concl });
        }
        if tr & fa != 0 { return None; }
        cur = next;
        if !changed { break; }
    }
    cur.sort(); cur.dedup();
    // subsumption among pure things is skipped
    Some((cur, tr, fa))
}

fn vars_of(cons: &[Con]) -> Mask { let mut m = 0; for c in cons { m |= c.prem; for &x in &c.concl { m |= x; } } m }

struct Counter {
    cache: HashMap<Vec<Con>, u128>,
    nodes: u64, hits: u64, comps: u64,
    hist: Vec<u64>, // histogram of #vars at cache-miss nodes
    use_comp: bool,
    heur: u32,
}

impl Counter {
    // count models of cons over exactly the variables occurring in cons
    fn count(&mut self, cons: Vec<Con>) -> u128 {
        if cons.is_empty() { return 1; }
        if let Some(&v) = self.cache.get(&cons) { self.hits += 1; return v; }
        self.nodes += 1;
        let vm = vars_of(&cons);
        let nv = vm.count_ones() as usize;
        self.hist[nv] += 1;
        // components
        if self.use_comp {
            let mut comp_masks: Vec<Mask> = vec![];
            for c in &cons {
                let mut m = c.prem; for &x in &c.concl { m |= x; }
                let mut i = 0;
                while i < comp_masks.len() { if comp_masks[i] & m != 0 { m |= comp_masks[i]; comp_masks.swap_remove(i); } else { i += 1; } }
                comp_masks.push(m);
            }
            if comp_masks.len() > 1 {
                self.comps += 1;
                let mut res: u128 = 1;
                for cm in comp_masks {
                    let sub: Vec<Con> = cons.iter().filter(|c| c.prem & cm != 0 || c.concl.iter().any(|&x| x & cm != 0)).cloned().collect();
                    res *= self.count(sub);
                    if res == 0 { break; }
                }
                self.cache.insert(cons, res);
                return res;
            }
        }
        // choose variable
        let mut score = [0u32; 64];
        for c in &cons {
            let w = match self.heur { 0 => 1, _ => 64 / (c.concl.len() as u32 + c.prem.count_ones()) };
            let mut m = c.prem; while m != 0 { let v = m.trailing_zeros(); score[v as usize] += 3 * w; m &= m - 1; }
            for &x in &c.concl { let mut m = x; while m != 0 { let v = m.trailing_zeros(); score[v as usize] += w; m &= m - 1; } }
        }
        let mut best = 0; let mut bs = 0;
        for v in 0..64 { if score[v] > bs { bs = score[v]; best = v; } }
        let bit: Mask = 1 << best;
        let mut total: u128 = 0;
        for val in 0..2 {
            let r = if val == 0 { simplify(&cons, 0, bit) } else { simplify(&cons, bit, 0) };
            if let Some((res, tr, fa)) = r {
                let rv = vars_of(&res);
                let assigned = tr | fa;
                let free = (vm & !assigned & !rv).count_ones();
                total += self.count(res) << free;
            }
        }
        self.cache.insert(cons, total);
        total
    }
}

fn group(sys: &Sys) -> Vec<Vec<usize>> {
    let k = sys.k; let mut res = vec![]; let mut cur = vec![usize::MAX; k]; cur[0] = 0; let mut used = vec![false; k]; used[0] = true;
    fn rec(sys: &Sys, i: usize, cur: &mut Vec<usize>, used: &mut Vec<bool>, res: &mut Vec<Vec<usize>>) {
        let k = sys.k;
        if i == k { res.push(cur.clone()); return; }
        if cur[i] != usize::MAX { rec(sys, i + 1, cur, used, res); return; }
        for j in 1..k {
            if used[j] { continue; }
            let isym = sys.conv[i] == i; let jsym = sys.conv[j] == j;
            if isym != jsym { continue; }
            let ci = sys.conv[i]; let cj = sys.conv[j];
            cur[i] = j; cur[ci] = cj; used[j] = true; used[cj] = true;
            rec(sys, i + 1, cur, used, res);
            used[j] = false; used[cj] = false; cur[i] = usize::MAX; cur[ci] = usize::MAX;
        }
    }
    rec(sys, 1, &mut cur, &mut used, &mut res); res
}
fn compose(a: &[usize], b: &[usize]) -> Vec<usize> { b.iter().map(|&x| a[x]).collect() }
fn inverse(a: &[usize]) -> Vec<usize> { let mut r = vec![0; a.len()]; for (i, &x) in a.iter().enumerate() { r[x] = i; } r }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let s: usize = args[1].parse().unwrap(); let n: usize = args[2].parse().unwrap();
    let use_comp = args.get(3).map(|x| x == "1").unwrap_or(true);
    let heur: u32 = args.get(4).map(|x| x.parse().unwrap()).unwrap_or(0);
    let only_id = args.get(5).map(|x| x == "1").unwrap_or(false);
    let sys = Sys::new(s, n);
    let g = group(&sys);
    println!("k={} |G|={}", sys.k, g.len());
    let mut class_of: HashMap<Vec<usize>, usize> = HashMap::new();
    let mut reps: Vec<(Vec<usize>, usize)> = vec![];
    for x in &g {
        if class_of.contains_key(x) { continue; }
        let id = reps.len(); let mut size = 0;
        for t in &g { let c = compose(&compose(t, x), &inverse(t)); if class_of.insert(c, id).is_none() { size += 1; } }
        reps.push((x.clone(), size));
    }
    let mut total: u128 = 0;
    for (rep, size) in &reps {
        let (nvars, cons) = build(&sys, rep);
        let t0 = std::time::Instant::now();
        let mut c = Counter { cache: HashMap::new(), nodes: 0, hits: 0, comps: 0, hist: vec![0; 65], use_comp, heur };
        let ncons = cons.len();
        let (res, tr, fa) = simplify(&cons, 0, 0).unwrap();
        let rv = vars_of(&res);
        let free = nvars as u32 - (tr | fa | rv).count_ones();
        let cnt = c.count(res) << free;
        println!("rep {:?} size {} vars {} cons {} count {} nodes {} hits {} comps {} time {:?}", rep, size, nvars, ncons, cnt, c.nodes, c.hits, c.comps, t0.elapsed());
        let mut cum = 0; let mut hs = String::new();
        for i in (0..65).rev() { if c.hist[i] > 0 { cum += c.hist[i]; hs += &format!("{}:{} ", i, cum); } }
        println!("  cumulative nodes with >= v vars: {}", hs);
        total += cnt * (*size as u128);
        if only_id { return; }
    }
    println!("sum {} orbits {} rem {}", total, total / g.len() as u128, total % g.len() as u128);
}
