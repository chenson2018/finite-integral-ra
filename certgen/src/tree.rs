//! Search tree over the high variables with three-valued pruning.

use crate::problem::Problem;

/// Three-valued (Kleene) value of a class code under a partial assignment.
/// 0 = false, 1 = true, 2 = unknown.
#[inline]
fn kval(code: usize, assign: &[u8]) -> u8 {
    match code {
        0 => 0,
        1 => 1,
        c => assign[c - 2],
    }
}

fn kdot(terms: &[(usize, usize)], assign: &[u8]) -> u8 {
    let mut acc = 0u8;
    for &(i, j) in terms {
        let (x, y) = (kval(i, assign), kval(j, assign));
        let a = if x == 0 || y == 0 { 0 } else if x == 1 { y } else if y == 1 { x } else { 2 };
        if a == 1 {
            return 1;
        }
        if a == 2 {
            acc = 2;
        }
    }
    acc
}

pub struct Tree<'a> {
    pub p: &'a Problem,
    pub b: usize,
    pub terms: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>,
}

/// A maximal block of the search: all `alpha` in `[lo, lo + 2^j)`.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Block {
    /// Every leaf of the block is zero because quadruple number `quad` is violated.
    Dead { lo: u64, j: usize, quad: usize },
    /// A single leaf to be evaluated by truth table.
    Leaf { lo: u64 },
}

impl<'a> Tree<'a> {
    pub fn new(p: &'a Problem, b: usize) -> Self {
        let terms = p.quads.iter().map(|&x| p.quad_terms(x)).collect();
        Tree { p, b, terms }
    }

    /// Index of a quadruple definitely violated under the partial assignment, if any.
    pub fn dead(&self, assign: &[u8]) -> Option<usize> {
        for (qi, (l, r)) in self.terms.iter().enumerate() {
            let (a, b) = (kdot(l, assign), kdot(r, assign));
            if (a == 1 && b == 0) || (a == 0 && b == 1) {
                return Some(qi);
            }
        }
        None
    }

    /// Enumerate the blocks, splitting the high variables from the highest index down.
    pub fn blocks(&self) -> Vec<Block> {
        let v = self.p.nvars;
        let mut assign = vec![2u8; v];
        let mut out = vec![];
        self.rec(v, 0, &mut assign, &mut out);
        out
    }

    fn rec(&self, depth_var: usize, lo: u64, assign: &mut Vec<u8>, out: &mut Vec<Block>) {
        // variables >= depth_var are assigned; depth_var - b free high variables remain
        let j = depth_var - self.b;
        if let Some(q) = self.dead(assign) {
            out.push(Block::Dead { lo, j, quad: q });
            return;
        }
        if j == 0 {
            out.push(Block::Leaf { lo });
            return;
        }
        let var = depth_var - 1;
        for val in 0..2u64 {
            assign[var] = val as u8;
            self.rec(var, lo | (val << (j - 1)), assign, out);
        }
        assign[var] = 2;
    }
}

/// Canonical residual formula of a full assignment of the high variables (variables `>= b`):
/// for every quadruple, the residual left and right disjunctions over the low variables, with
/// constants folded. Two assignments with equal residuals have equal leaves.
pub fn residual(tree: &Tree, alpha: u64) -> Option<Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>> {
    let b = tree.b;
    let val = |code: usize| -> u8 {
        match code {
            0 => 0,
            1 => 1,
            c => { let j = c - 2; if j < b { 2 } else { ((alpha >> (j - b)) & 1) as u8 } }
        }
    };
    // residual of a dot: None = true, Some(terms) with each term a sorted pair of low codes
    // (a single remaining variable is encoded as (c, c))
    let rdot = |terms: &[(usize, usize)]| -> Option<Vec<(usize, usize)>> {
        let mut out = vec![];
        for &(i, j) in terms {
            let (x, y) = (val(i), val(j));
            if x == 0 || y == 0 { continue; }
            if x == 1 && y == 1 { return None; }
            let t = if x == 1 { (j, j) } else if y == 1 { (i, i) } else { (i.min(j), i.max(j)) };
            out.push(t);
        }
        out.sort();
        out.dedup();
        // absorption: a single variable absorbs pairs containing it
        let singles: Vec<usize> = out.iter().filter(|t| t.0 == t.1).map(|t| t.0).collect();
        out.retain(|t| t.0 == t.1 || !(singles.contains(&t.0) || singles.contains(&t.1)));
        Some(out)
    };
    let mut res = vec![];
    for (l, r) in &tree.terms {
        let (a, c) = (rdot(l), rdot(r));
        match (&a, &c) {
            (None, None) => continue,
            (None, Some(v)) | (Some(v), None) if v.is_empty() => return None, // dead
            _ => {}
        }
        if a == c { continue; }
        let (a, c) = (a.unwrap_or(vec![(1, 1)]), c.unwrap_or(vec![(1, 1)]));
        let (a, c) = if a <= c { (a, c) } else { (c, a) };
        res.push((a, c));
    }
    res.sort();
    res.dedup();
    Some(res)
}
