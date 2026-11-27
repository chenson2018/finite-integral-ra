//! Identify forced or equal cycle variables in a cofactor. The certificate names
//! a quadruple excluding both unequal valuations, independently of this search.
use crate::leaf::Evaluator;
use crate::problem::Problem;
use std::collections::HashMap;

type Side = Vec<(usize, usize)>;
type Equation = (Side, Side);

pub struct Contraction {
    pub steps: Vec<(usize, usize, usize)>,
    pub ids: Vec<usize>,
    pub codes: Vec<usize>,
    pub widths: Vec<usize>,
    pub conflict: Option<usize>,
}

pub struct Contractor<'a> {
    p: &'a Problem,
    quads: Vec<(usize, Equation)>,
    tables: HashMap<usize, Evaluator<'a>>,
}

fn residual(terms: &Side, map: &[usize]) -> Side {
    let mut result = Vec::with_capacity(terms.len());
    for &(i, j) in terms {
        let (a, b) = (map[i], map[j]);
        if a == 0 || b == 0 {
            continue;
        }
        if a == 1 && b == 1 {
            return vec![(1, 1)];
        }
        result.push(if a == b { (1, a) } else { (a.min(b), a.max(b)) });
    }
    result.sort_unstable();
    result.dedup();
    let singles = result
        .iter()
        .take_while(|p| p.0 == 1)
        .fold(0u64, |m, p| m | (1 << (p.1 - 2)));
    result.retain(|&(a, b)| a == 1 || ((1 << (a - 2)) | (1 << (b - 2))) & singles == 0);
    result
}

fn variables(l: &Side, r: &Side) -> u64 {
    l.iter()
        .chain(r)
        .flat_map(|&(a, b)| [a, b])
        .filter(|&v| v >= 2)
        .fold(0, |mask, v| mask | (1 << (v - 2)))
}

fn forced(left: &Side, right: &Side) -> Option<(usize, usize)> {
    if left.is_empty() {
        return right
            .first()
            .and_then(|&(a, b)| (a == 1 && b >= 2).then_some((b, 0)));
    }
    if left == &[(1, 1)] {
        let &(a, b) = right.first()?;
        return [a, b]
            .into_iter()
            .find(|&v| v >= 2 && right.iter().all(|&(i, j)| i == v || j == v))
            .map(|v| (v, 1));
    }
    None
}

impl<'a> Contractor<'a> {
    pub fn new(p: &'a Problem) -> Self {
        let quads = p
            .quads
            .iter()
            .filter(|&&q| !p.quad_trivial(q))
            .map(|&q| (q, p.quad_terms(q)))
            .collect();
        Self {
            p,
            quads,
            tables: HashMap::new(),
        }
    }

    pub fn plan(&self, k: usize, h: u64, max_bits: usize) -> Option<Contraction> {
        let mut map: Vec<_> = (0..self.p.nvars + 2)
            .map(|c| {
                if c < k + 2 {
                    c
                } else {
                    ((h >> (c - k - 2)) & 1) as usize
                }
            })
            .collect();
        let mut steps = Vec::new();
        loop {
            let mut step = None;
            for (q, (a, b)) in &self.quads {
                let l = residual(a, &map);
                let r = residual(b, &map);
                if l == r {
                    continue;
                }
                if (l.is_empty() && r == [(1, 1)]) || (r.is_empty() && l == [(1, 1)]) {
                    return Some(Contraction {
                        steps,
                        ids: vec![],
                        codes: vec![],
                        widths: vec![],
                        conflict: Some(*q),
                    });
                }
                let eq = if let ([(1, i)], [(1, j)]) = (&l[..], &r[..]) {
                    Some(((*i).max(*j), (*i).min(*j)))
                } else {
                    forced(&l, &r).or_else(|| forced(&r, &l))
                };
                if let Some((x, y)) = eq {
                    step = Some((x, y, *q));
                    break;
                }
            }
            let Some((x, y, q)) = step else {
                break;
            };
            steps.push((x, y, q));
            for v in &mut map[2..k + 2] {
                if *v == x {
                    *v = y;
                }
            }
        }
        // Each residual equation couples its surviving variables. Distinct
        // connected components can be counted independently, and unused cycles
        // contribute a power of two without needing any table.
        let free = (0..k)
            .filter(|&j| map[j + 2] == j + 2)
            .fold(0u64, |mask, j| mask | (1 << j));
        let mut groups: Vec<u64> = Vec::new();
        for (_, (a, b)) in &self.quads {
            let l = residual(a, &map);
            let r = residual(b, &map);
            if l == r {
                continue;
            }
            let mut mask = variables(&l, &r);
            groups.retain(|&g| {
                if g & mask == 0 {
                    true
                } else {
                    mask |= g;
                    false
                }
            });
            if mask.count_ones() as usize > max_bits {
                return None;
            }
            if mask != 0 {
                groups.push(mask);
            }
        }
        groups.sort_by_key(|g| g.trailing_zeros());
        let unused = free & !groups.iter().fold(0, |a, b| a | b);
        if groups.is_empty() {
            groups.push(0);
        }
        if unused != 0 {
            groups.push(unused);
        }
        let widths = groups.iter().map(|g| g.count_ones() as usize).collect();
        let ids: Vec<_> = groups
            .iter()
            .flat_map(|&g| (0..k).filter(move |j| g >> j & 1 != 0))
            .collect();
        let mut compact = vec![0; k + 2];
        compact[1] = 1;
        for (i, &j) in ids.iter().enumerate() {
            compact[j + 2] = i + 2;
        }
        let codes = map[2..k + 2].iter().map(|&v| compact[v]).collect();
        Some(Contraction {
            steps,
            ids,
            codes,
            widths,
            conflict: None,
        })
    }

    pub fn count(&mut self, c: &Contraction, k: usize, h: u64) -> u64 {
        if c.conflict.is_some() {
            return 0;
        }
        let mut map = vec![0, 1];
        map.extend(&c.codes);
        map.extend((k..self.p.nvars).map(|i| ((h >> (i - k)) & 1) as usize));
        let eqs: Vec<_> = self
            .quads
            .iter()
            .filter_map(|(_, (a, b))| {
                let l = residual(a, &map);
                let r = residual(b, &map);
                (l != r).then_some((l, r))
            })
            .collect();
        let mut by_component = vec![Vec::new(); c.widths.len()];
        let mut ends = Vec::new();
        let mut end = 0;
        for width in &c.widths {
            end += width;
            ends.push(end);
        }
        for (mut l, mut r) in eqs {
            let mask = variables(&l, &r);
            let g = if mask == 0 {
                0
            } else {
                ends.partition_point(|&v| v <= mask.trailing_zeros() as usize)
            };
            let start = ends[g] - c.widths[g];
            for (a, b) in l.iter_mut().chain(&mut r) {
                for v in [a, b] {
                    if *v >= 2 {
                        assert!((start..ends[g]).contains(&(*v - 2)));
                        *v -= start;
                    }
                }
            }
            by_component[g].push((l, r));
        }
        by_component
            .into_iter()
            .zip(&c.widths)
            .map(|(eqs, &width)| {
                if eqs.is_empty() {
                    return 1 << width;
                }
                let ev = self
                    .tables
                    .entry(width)
                    .or_insert_with(|| Evaluator::new(self.p, width));
                ev.leaf_terms(0, &eqs)
            })
            .product()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sys::Sys;

    #[test]
    fn component_products_agree_with_the_unsplit_formula() {
        let sys = Sys::new(4, 0);
        let identity: Vec<_> = (0..sys.k).collect();
        let p = Problem::new(&sys, &identity, &|_, roots| roots);
        let k = 8;
        let direct = Evaluator::new(&p, k);
        let mut solver = Contractor::new(&p);
        let mut factored = false;
        let mut identified = false;
        let mut conflict = false;
        for i in 0..256 {
            let h = (i * 7919) & ((1 << (p.nvars - k)) - 1);
            let c = solver.plan(k, h, k).unwrap();
            assert_eq!(solver.count(&c, k, h), direct.leaf(h), "outer bits {h}");
            factored |= c.widths.len() > 1;
            identified |= !c.steps.is_empty();
            conflict |= c.conflict.is_some();
        }
        assert!(factored && identified && conflict);
    }
}
