//! Three-valued pruning of the assignments of the high variables.

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

/// The conditions which can show that a leaf vanishes without evaluating it.
pub struct Tree {
    terms: Vec<(Vec<(usize, usize)>, Vec<(usize, usize)>)>,
}

impl Tree {
    /// The conditions for the high variables `b + m, …` when the variables `b, …, b + m - 1` are
    /// eliminated: only the conditions not depending on the latter can kill a leaf.
    pub fn new_elim(p: &Problem, b: usize, m: usize) -> Self {
        let tags = p.quad_tags(b, m);
        let terms = p.quads.iter().zip(&tags).map(|(&x, t)| if *t == Some(0) { p.quad_terms(x) } else { (vec![], vec![]) }).collect();
        Tree { terms }
    }

    /// Index of a quadruple whose two sides are opposite constants under the partial assignment
    /// (2 = unknown), if any.
    pub fn dead(&self, assign: &[u8]) -> Option<usize> {
        for (qi, (l, r)) in self.terms.iter().enumerate() {
            let (a, b) = (kdot(l, assign), kdot(r, assign));
            if (a == 1 && b == 0) || (a == 0 && b == 1) {
                return Some(qi);
            }
        }
        None
    }
}
