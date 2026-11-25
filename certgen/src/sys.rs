//! Atoms, converse, and the symmetry group.

use std::collections::HashMap;

#[derive(Clone)]
pub struct Sys {
    pub s: usize,
    pub n: usize,
    pub k: usize,
    pub conv: Vec<usize>,
}

impl Sys {
    /// Atom codes: 0 is the identity, 1..=s the symmetric atoms, then the pairs.
    pub fn new(s: usize, n: usize) -> Sys {
        let k = 1 + s + 2 * n;
        let mut conv: Vec<usize> = (0..k).collect();
        for i in 0..n {
            conv[1 + s + 2 * i] = 1 + s + 2 * i + 1;
            conv[1 + s + 2 * i + 1] = 1 + s + 2 * i;
        }
        Sys { s, n, k, conv }
    }

    /// All permutations of the atoms fixing the identity and commuting with converse.
    pub fn group(&self) -> Vec<Vec<usize>> {
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
                if used[j] || (sys.conv[i] == i) != (sys.conv[j] == j) {
                    continue;
                }
                let (ci, cj) = (sys.conv[i], sys.conv[j]);
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
        let mut res = vec![];
        let mut cur = vec![usize::MAX; self.k];
        cur[0] = 0;
        let mut used = vec![false; self.k];
        used[0] = true;
        rec(self, 1, &mut cur, &mut used, &mut res);
        res
    }
}

/// `(a ∘ b)(x) = a[b[x]]`.
pub fn compose(a: &[usize], b: &[usize]) -> Vec<usize> {
    b.iter().map(|&x| a[x]).collect()
}

pub fn inverse(a: &[usize]) -> Vec<usize> {
    let mut r = vec![0; a.len()];
    for (i, &x) in a.iter().enumerate() {
        r[x] = i;
    }
    r
}

/// Conjugacy classes: representatives, and for every group element `l` (sorted) its class index
/// and a conjugator `t` with `l ∘ t = t ∘ rep`.
pub struct Classes {
    pub reps: Vec<Vec<usize>>,
    pub elems: Vec<(Vec<usize>, usize, Vec<usize>)>,
}

pub fn classes(g: &[Vec<usize>]) -> Classes {
    let mut seen: HashMap<Vec<usize>, (usize, Vec<usize>)> = HashMap::new();
    let mut reps = vec![];
    let mut sorted = g.to_vec();
    sorted.sort();
    for x in &sorted {
        if seen.contains_key(x) {
            continue;
        }
        let id = reps.len();
        for t in &sorted {
            let c = compose(&compose(t, x), &inverse(t));
            seen.entry(c).or_insert((id, t.clone()));
        }
        reps.push(x.clone());
    }
    let elems = sorted.iter().map(|l| { let (i, t) = &seen[l]; (l.clone(), *i, t.clone()) }).collect();
    Classes { reps, elems }
}
