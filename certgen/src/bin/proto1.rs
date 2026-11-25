// Prototype: Burnside count of integral relation algebras with s symmetric and n pairs of
// nonsymmetric diversity atoms.
use std::collections::HashMap;

#[derive(Clone)]
struct Sys {
    k: usize,
    conv: Vec<usize>,
}

impl Sys {
    fn new(s: usize, n: usize) -> Sys {
        let k = 1 + s + 2 * n;
        let mut conv: Vec<usize> = (0..k).collect();
        for i in 0..n {
            conv[1 + s + 2 * i] = 1 + s + 2 * i + 1;
            conv[1 + s + 2 * i + 1] = 1 + s + 2 * i;
        }
        Sys { k, conv }
    }
    fn code(&self, a: usize, b: usize, c: usize) -> usize {
        (a * self.k + b) * self.k + c
    }
}

fn find(p: &mut Vec<usize>, x: usize) -> usize {
    let mut r = x;
    while p[r] != r {
        r = p[r];
    }
    let mut y = x;
    while p[y] != r {
        let n = p[y];
        p[y] = r;
        y = n;
    }
    r
}

// all perms of atoms commuting with conv, fixing 0, preserving symmetric-ness
fn group(sys: &Sys) -> Vec<Vec<usize>> {
    let k = sys.k;
    let mut res = vec![];
    let mut cur = vec![usize::MAX; k];
    cur[0] = 0;
    let mut used = vec![false; k];
    used[0] = true;
    fn rec(sys: &Sys, i: usize, cur: &mut Vec<usize>, used: &mut Vec<bool>, res: &mut Vec<Vec<usize>>) {
        let k = sys.k;
        if i == k {
            res.push(cur.clone());
            return;
        }
        if cur[i] != usize::MAX {
            rec(sys, i + 1, cur, used, res);
            return;
        }
        for j in 1..k {
            if used[j] {
                continue;
            }
            let isym = sys.conv[i] == i;
            let jsym = sys.conv[j] == j;
            if isym != jsym {
                continue;
            }
            if isym {
                cur[i] = j;
                used[j] = true;
                rec(sys, i + 1, cur, used, res);
                used[j] = false;
                cur[i] = usize::MAX;
            } else {
                let ci = sys.conv[i];
                let cj = sys.conv[j];
                cur[i] = j;
                cur[ci] = cj;
                used[j] = true;
                used[cj] = true;
                rec(sys, i + 1, cur, used, res);
                used[j] = false;
                used[cj] = false;
                cur[i] = usize::MAX;
                cur[ci] = usize::MAX;
            }
        }
    }
    rec(sys, 1, &mut cur, &mut used, &mut res);
    res
}

fn compose(a: &[usize], b: &[usize]) -> Vec<usize> {
    // (a*b)(x) = a(b(x))
    b.iter().map(|&x| a[x]).collect()
}
fn inverse(a: &[usize]) -> Vec<usize> {
    let mut r = vec![0; a.len()];
    for (i, &x) in a.iter().enumerate() {
        r[x] = i;
    }
    r
}

// A literal reference: constant or variable
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum T {
    False,
    True,
    Var(usize),
}

#[derive(Clone, Debug)]
struct Constraint {
    prem: Vec<usize>,            // variables that must all be true for premise (1 or 2)
    concl: Vec<Vec<usize>>,      // disjunction of conjunctions (each 1 or 2 vars)
}

struct Formula {
    nvars: usize,
    cons: Vec<Constraint>,
}

fn build(sys: &Sys, sigma: &[usize]) -> Formula {
    let k = sys.k;
    let n3 = k * k * k;
    let mut uf: Vec<usize> = (0..n3).collect();
    let mut union = |uf: &mut Vec<usize>, a: usize, b: usize| {
        let ra = find(uf, a);
        let rb = find(uf, b);
        if ra != rb {
            let (lo, hi) = if ra < rb { (ra, rb) } else { (rb, ra) };
            uf[hi] = lo;
        }
    };
    for a in 1..k {
        for b in 1..k {
            for c in 1..k {
                let x = sys.code(a, b, c);
                // left: (r,u,t) -> (conv r, t, u)
                union(&mut uf, x, sys.code(sys.conv[a], c, b));
                // right: (r,u,t) -> (t, conv u, r)
                union(&mut uf, x, sys.code(c, sys.conv[b], a));
                union(&mut uf, x, sys.code(sigma[a], sigma[b], sigma[c]));
            }
        }
    }
    let mut varid: HashMap<usize, usize> = HashMap::new();
    let mut tv = vec![T::False; n3];
    for a in 0..k {
        for b in 0..k {
            for c in 0..k {
                let x = sys.code(a, b, c);
                tv[x] = if a == 0 {
                    if b == c { T::True } else { T::False }
                } else if b == 0 {
                    if a == c { T::True } else { T::False }
                } else if c == 0 {
                    if b == sys.conv[a] { T::True } else { T::False }
                } else {
                    let r = find(&mut uf, x);
                    let l = varid.len();
                    T::Var(*varid.entry(r).or_insert(l))
                };
            }
        }
    }
    let nvars = varid.len();
    let mut cons: Vec<Constraint> = vec![];
    let mut seen: HashMap<(Vec<usize>, Vec<Vec<usize>>), ()> = HashMap::new();
    // assoc: (r,q,p) & (s,t,q) -> exists q', (q',t,p) & (r,s,q')
    for r in 0..k {
        for s in 0..k {
            for t in 0..k {
                for p in 0..k {
                    // conclusion
                    let mut concl: Vec<Vec<usize>> = vec![];
                    let mut concl_true = false;
                    for q2 in 0..k {
                        let x = tv[sys.code(q2, t, p)];
                        let y = tv[sys.code(r, s, q2)];
                        if x == T::False || y == T::False {
                            continue;
                        }
                        let mut c = vec![];
                        if let T::Var(v) = x { c.push(v); }
                        if let T::Var(v) = y { c.push(v); }
                        c.sort();
                        c.dedup();
                        if c.is_empty() {
                            concl_true = true;
                        }
                        concl.push(c);
                    }
                    if concl_true {
                        continue;
                    }
                    concl.sort();
                    concl.dedup();
                    // remove subsumed conjunctions (supersets of another)
                    let cc = concl.clone();
                    concl.retain(|c| !cc.iter().any(|d| d != c && d.iter().all(|x| c.contains(x))));
                    for q in 0..k {
                        let x = tv[sys.code(r, q, p)];
                        let y = tv[sys.code(s, t, q)];
                        if x == T::False || y == T::False {
                            continue;
                        }
                        let mut prem = vec![];
                        if let T::Var(v) = x { prem.push(v); }
                        if let T::Var(v) = y { prem.push(v); }
                        prem.sort();
                        prem.dedup();
                        // trivially satisfied if some conclusion conj is subset of premise
                        if concl.iter().any(|c| c.iter().all(|v| prem.contains(v))) {
                            continue;
                        }
                        // simplify conclusion conjunctions by removing premise vars
                        let mut c2: Vec<Vec<usize>> = concl
                            .iter()
                            .map(|c| c.iter().cloned().filter(|v| !prem.contains(v)).collect())
                            .collect();
                        c2.sort();
                        c2.dedup();
                        let cc = c2.clone();
                        c2.retain(|c: &Vec<usize>| !cc.iter().any(|d| d != c && d.iter().all(|x| c.contains(x))));
                        let key = (prem.clone(), c2.clone());
                        if seen.insert(key, ()).is_none() {
                            cons.push(Constraint { prem, concl: c2 });
                        }
                    }
                }
            }
        }
    }
    Formula { nvars, cons }
}

// simple DPLL model counter with stats
struct Counter<'a> {
    f: &'a Formula,
    assign: Vec<i8>, // -1 unassigned, 0, 1
    occ: Vec<Vec<usize>>,
    nodes: u64,
    leaves: u64,
}

impl<'a> Counter<'a> {
    fn new(f: &'a Formula) -> Self {
        let mut occ = vec![vec![]; f.nvars];
        for (i, c) in f.cons.iter().enumerate() {
            for &v in &c.prem {
                occ[v].push(i);
            }
            for cj in &c.concl {
                for &v in cj {
                    occ[v].push(i);
                }
            }
        }
        for o in occ.iter_mut() {
            o.sort();
            o.dedup();
        }
        Counter { f, assign: vec![-1; f.nvars], occ, nodes: 0, leaves: 0 }
    }
    // status: 0 = satisfied, 1 = violated, 2 = undetermined
    fn status(&self, c: &Constraint) -> u8 {
        let mut prem_true = true;
        for &v in &c.prem {
            match self.assign[v] {
                0 => return 0,
                -1 => prem_true = false,
                _ => {}
            }
        }
        let mut any_open = false;
        for cj in &c.concl {
            let mut all_true = true;
            let mut dead = false;
            for &v in cj {
                match self.assign[v] {
                    0 => { dead = true; break; }
                    -1 => all_true = false,
                    _ => {}
                }
            }
            if dead { continue; }
            if all_true { return 0; }
            any_open = true;
        }
        if !any_open && prem_true { return 1; }
        2
    }
    fn count(&mut self, active: &[usize], free: u32) -> u128 {
        self.nodes += 1;
        // filter active constraints
        let mut act: Vec<usize> = Vec::with_capacity(active.len());
        for &ci in active {
            match self.status(&self.f.cons[ci]) {
                0 => {}
                1 => return 0,
                _ => act.push(ci),
            }
        }
        if act.is_empty() {
            self.leaves += 1;
            return 1u128 << free;
        }
        // choose var: most occurrences among active constraints
        let mut score = vec![0u32; self.f.nvars];
        for &ci in &act {
            let c = &self.f.cons[ci];
            for &v in &c.prem { if self.assign[v] < 0 { score[v] += 3; } }
            for cj in &c.concl { for &v in cj { if self.assign[v] < 0 { score[v] += 1; } } }
        }
        let mut best = usize::MAX;
        let mut bs = 0;
        for v in 0..self.f.nvars {
            if score[v] > bs { bs = score[v]; best = v; }
        }
        let v = best;
        let mut total = 0u128;
        for val in [0i8, 1] {
            self.assign[v] = val;
            total += self.count(&act, free - 1);
        }
        self.assign[v] = -1;
        total
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let s: usize = args[1].parse().unwrap();
    let n: usize = args[2].parse().unwrap();
    let sys = Sys::new(s, n);
    let g = group(&sys);
    println!("k={} |G|={}", sys.k, g.len());
    // conjugacy classes
    let mut class_of: HashMap<Vec<usize>, usize> = HashMap::new();
    let mut reps: Vec<(Vec<usize>, usize)> = vec![];
    for x in &g {
        if class_of.contains_key(x) { continue; }
        let id = reps.len();
        let mut size = 0;
        for t in &g {
            let c = compose(&compose(t, x), &inverse(t));
            if class_of.insert(c, id).is_none() { size += 1; }
        }
        reps.push((x.clone(), size));
    }
    println!("classes: {}", reps.len());
    let mut total: u128 = 0;
    for (rep, size) in &reps {
        let f = build(&sys, rep);
        let mut c = Counter::new(&f);
        let all: Vec<usize> = (0..f.cons.len()).collect();
        let t0 = std::time::Instant::now();
        let cnt = c.count(&all, f.nvars as u32);
        println!("rep {:?} size {} vars {} cons {} count {} nodes {} leaves {} time {:?}", rep, size, f.nvars, f.cons.len(), cnt, c.nodes, c.leaves, t0.elapsed());
        total += cnt * (*size as u128);
    }
    println!("sum {} orbits {} rem {}", total, total / g.len() as u128, total % g.len() as u128);
}
