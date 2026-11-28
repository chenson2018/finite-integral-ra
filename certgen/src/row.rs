//! Project each oriented associativity equation onto the ten middle decisions.
//! The two possible values of a remaining cycle give two row domains. A row
//! excluded from both has zero completions, even with different witnesses.
use crate::problem::Problem;

pub const BITS: usize = 10;
const WORDS: usize = (1 << BITS) / 64;
pub type Mask = [u64; WORDS];
type Terms = Vec<(u64, usize, u64)>; // low, middle and outer cycle masks

pub struct Probe {
    pub code: usize,
    pub zero: Vec<usize>,
    pub one: Vec<usize>,
}

pub struct Domain {
    pub live: Mask,
    pub witnesses: Vec<usize>,
    pub probes: Vec<Probe>,
}

pub struct Projection {
    quads: Vec<(usize, Terms, Terms)>,
    guards: Vec<Mask>,
    low: usize,
}

fn terms(pairs: Vec<(usize, usize)>, k: usize) -> Terms {
    let mut terms = Vec::new();
    for (a, b) in pairs {
        if a == 0 || b == 0 {
            continue;
        }
        let bits = [a, b]
            .into_iter()
            .filter(|&c| c >= 2)
            .fold(0, |m, c| m | 1u64 << (c - 2));
        if bits == 0 {
            return vec![(0, 0, 0)];
        }
        let low = bits & ((1 << k) - 1);
        let mid = ((bits >> k) as usize) & ((1 << BITS) - 1);
        terms.push((low, mid, bits >> (k + BITS)));
    }
    terms
}

impl Projection {
    pub fn new(p: &Problem, low: usize) -> Self {
        let quads = p
            .quads
            .iter()
            .filter(|&&x| !p.quad_trivial(x))
            .map(|&x| {
                let (l, r) = p.quad_terms(x);
                (x, terms(l, low), terms(r, low))
            })
            .collect();
        let guards = (0..1 << BITS)
            .map(|g| {
                std::array::from_fn(|w| {
                    (0..64)
                        .filter(|i| (w * 64 + i) & g == g)
                        .fold(0, |m, i| m | 1 << i)
                })
            })
            .collect();
        Self { quads, guards, low }
    }

    fn bounds(&self, ts: &[(u64, usize)], zero: u64, one: u64) -> (Mask, Mask) {
        let mut lo = [0; WORDS];
        let mut hi = [0; WORDS];
        for &(variables, g) in ts {
            if variables & zero != 0 {
                continue;
            }
            let guard = &self.guards[g];
            for (x, &v) in hi.iter_mut().zip(guard) {
                *x |= v;
            }
            if variables & !one == 0 {
                for (x, &v) in lo.iter_mut().zip(guard) {
                    *x |= v;
                }
            }
        }
        (lo, hi)
    }

    pub fn domain(&self, h: u64) -> Domain {
        let mut qs = Vec::new();
        let mut live = [u64::MAX; WORDS];
        let mut witnesses = Vec::new();
        for (x, left, right) in &self.quads {
            let specialize = |ts: &Terms| -> Vec<_> {
                ts.iter()
                    .filter(|t| t.2 & !h == 0)
                    .map(|t| (t.0, t.1))
                    .collect()
            };
            let l = specialize(left);
            let r = specialize(right);
            if l == r {
                continue;
            }
            let (ll, lu) = self.bounds(&l, 0, 0);
            let (rl, ru) = self.bounds(&r, 0, 0);
            let mut useful = false;
            for w in 0..WORDS {
                let bad = (ll[w] & !ru[w]) | (rl[w] & !lu[w]);
                useful |= live[w] & bad != 0;
                live[w] &= !bad;
            }
            if useful {
                witnesses.push(*x);
            }
            if live == [0; WORDS] {
                break;
            }
            let deps = l.iter().chain(&r).fold(0, |a, t| a | t.0);
            qs.push((*x, l, r, deps, ll, lu, rl, ru));
        }
        let mut probes = Vec::new();
        for j in 0..self.low {
            if live == [0; WORDS] {
                break;
            }
            let bit = 1 << j;
            let mut excluded = [[0; WORDS]; 2];
            let mut reasons = [Vec::new(), Vec::new()];
            for (x, l, r, deps, ll, lu, rl, ru) in &qs {
                if deps & bit == 0 {
                    continue;
                }
                let (_, lu0) = self.bounds(l, bit, 0);
                let (_, ru0) = self.bounds(r, bit, 0);
                let (ll1, _) = self.bounds(l, 0, bit);
                let (rl1, _) = self.bounds(r, 0, bit);
                for value in 0..2 {
                    let mut gained = [0; WORDS];
                    for w in 0..WORDS {
                        let bad = if value == 0 {
                            (ll[w] & !ru0[w]) | (rl[w] & !lu0[w])
                        } else {
                            (ll1[w] & !ru[w]) | (rl1[w] & !lu[w])
                        };
                        gained[w] = bad & live[w] & !excluded[value][w];
                        excluded[value][w] |= gained[w];
                    }
                    if gained != [0; WORDS] {
                        reasons[value].push((*x, gained));
                    }
                }
            }
            let conflict: Mask = std::array::from_fn(|w| excluded[0][w] & excluded[1][w]);
            if conflict == [0; WORDS] {
                continue;
            }
            let [zero, one] = reasons.map(|rs| {
                rs.into_iter()
                    .filter_map(|(q, m)| (0..WORDS).any(|w| m[w] & conflict[w] != 0).then_some(q))
                    .collect()
            });
            probes.push(Probe {
                code: j + 2,
                zero,
                one,
            });
            for w in 0..WORDS {
                live[w] &= !conflict[w];
            }
        }
        Domain {
            live,
            witnesses,
            probes,
        }
    }
}

/// A checked renaming of two product-row cofactors. The fixed outer cycles
/// may admit more renamings than those respecting our particular row split.
pub struct Action {
    pub sym: crate::symm::Sym,
    pub high: Vec<usize>,
    pub keep: Mask,
    pub twice: Mask,
    image: Vec<usize>,
}

fn permute(mut x: u64, p: &[usize]) -> u64 {
    let mut image = 0;
    while x != 0 {
        image |= 1 << p[x.trailing_zeros() as usize];
        x &= x - 1;
    }
    image
}

// Keep the lower row of a pair with weight two, and a fixed row with
// weight one. If either end belongs to a contracted 64-row block,
// both ends have unit weight so the block can be summed independently.
fn row_weights(image: &[usize], blocks: u16) -> (Mask, Mask) {
    let (mut keep, mut twice) = ([0; WORDS], [0; WORDS]);
    for (i, &j) in image.iter().enumerate() {
        let contracted = blocks & ((1 << (i / 64)) | (1 << (j / 64))) != 0;
        if contracted || i <= j {
            keep[i / 64] |= 1 << (i % 64);
        }
        if !contracted && i < j {
            twice[i / 64] |= 1 << (i % 64);
        }
    }
    (keep, twice)
}

impl Action {
    pub fn all(p: &Problem, k: usize, atoms: &[Vec<usize>]) -> Vec<Self> {
        let mut out = Vec::new();
        for h in atoms {
            let vp = crate::symm::var_perm(p, h);
            let block = |j: usize| {
                if j < k {
                    0
                } else if j < k + BITS {
                    1
                } else {
                    2
                }
            };
            if (0..p.nvars).any(|j| block(j) != block(vp[j])) {
                continue;
            }
            let high: Vec<_> = vp[k..].iter().map(|i| i - k).collect();
            if (0..BITS).all(|j| high[j] == j) || (0..BITS).any(|j| high[high[j]] != j) {
                continue;
            }
            let image: Vec<_> = (0..1 << BITS).map(|i| permute(i, &high) as usize).collect();
            let (keep, twice) = row_weights(&image, 0);
            let sym = crate::symm::Sym {
                h: h.clone(),
                hi: crate::sys::inverse(h),
                vq: crate::sys::inverse(&vp),
                vp,
            };
            out.push(Self {
                sym,
                image,
                high,
                keep,
                twice,
            });
        }
        out
    }

    pub fn weights(&self, blocks: u16) -> (Mask, Mask) {
        if blocks == 0 {
            (self.keep, self.twice)
        } else {
            row_weights(&self.image, blocks)
        }
    }

    pub fn best(actions: &[Self], h: u64, live: &Mask, blocks: u16) -> (Option<usize>, usize) {
        let mut best = (None, 0);
        for (i, a) in actions.iter().enumerate() {
            if permute(h << BITS, &a.high) != h << BITS {
                continue;
            }
            let (keep, _) = a.weights(blocks);
            let gain = live
                .iter()
                .zip(keep)
                .map(|(&w, k)| (w & !k).count_ones() as usize)
                .sum();
            if gain > best.1 {
                best = (Some(i), gain);
            }
        }
        best
    }
}

pub fn mask_literal(mask: &Mask) -> String {
    let hex: String = mask.iter().rev().map(|w| format!("{w:016x}")).collect();
    let digits = hex.trim_start_matches('0');
    if digits.is_empty() {
        "0".into()
    } else {
        format!("0x{digits}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contraction_preserves_pairs_outside_its_block() {
        // Swap bits 0 and 6. Rows 1 and 64 straddle the contracted block;
        // rows 129 and 192 form an unaffected pair farther up the domain.
        let mut high: Vec<_> = (0..BITS).collect();
        high.swap(0, 6);
        let image: Vec<_> = (0..1 << BITS).map(|i| permute(i, &high) as usize).collect();
        let (keep, twice) = row_weights(&image, 1);
        let weight =
            |i: usize| ((keep[i / 64] >> (i % 64)) & 1) + ((twice[i / 64] >> (i % 64)) & 1);
        assert_eq!((weight(1), weight(64)), (1, 1));
        assert_eq!((weight(129), weight(192)), (2, 0));
        for (i, &j) in image.iter().enumerate() {
            assert_eq!(weight(i) + weight(j), 2);
        }
    }
}
