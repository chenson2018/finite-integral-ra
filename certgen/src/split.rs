//! Count the identity class by the cycles on three converse-orbits and the remaining product rows.

use super::*;
use crate::contract::{Contraction, Contractor};
use crate::leaf::{Evaluator, MemoEval};
use crate::row::{mask_literal, Action, Domain, Mask, Probe, Projection};
use std::collections::BTreeMap;

// In both seven-atom milestones the middle block has ten bits. The low table
// and the number of independent symmetric loops are kept separate.
const B: usize = 20;
const D: usize = crate::row::BITS;
const WIDTH: usize = 1 << D;

fn order(p: &Problem, mut roots: Vec<usize>) -> Vec<usize> {
    roots.sort_by_key(|&x| {
        let (a, b, c) = (x / p.k / p.k, x / p.k % p.k, x % p.k);
        let mut support = [a, b, c].map(|i| i.min(p.conv[i]));
        support.sort_unstable();
        let [u, v, w] = support;
        if u != v && v != w {
            3 // three different converse-orbits
        } else if a == b && b == c && a <= p.s {
            1 // independent loops
        } else {
            let middle = if p.n == 0 {
                v >= 5
            } else {
                // The two diagonal rows of atoms 3 and 4, including their
                // oriented endpoint cycles involving the converse pair.
                (v == 3 || v == 4) || ((a == 3 || a == 4) && b == 5 && c == 6)
            };
            if middle {
                2
            } else {
                0
            }
        }
    });
    roots
}

struct Fiber {
    minimum: u64,
    weight: u64,
    image: u64,
    orientation: usize,
    witnesses: Vec<usize>,
    probes: Vec<Probe>,
    action: Option<usize>,
    mixed: Option<(Mask, Mask)>,
    live: usize,
    mask: Mask,
    chunks: Vec<(usize, u64)>,
    contracted: BTreeMap<usize, Contraction>,
}

impl Fiber {
    fn new(r: &Rep, image: u64, orientation: usize) -> Self {
        Self {
            minimum: r.alpha,
            weight: r.m,
            image,
            orientation,
            witnesses: vec![],
            probes: vec![],
            action: None,
            mixed: None,
            live: 0,
            mask: [0; WIDTH / 64],
            chunks: vec![],
            contracted: BTreeMap::new(),
        }
    }

    fn count(&self) -> u64 {
        self.chunks.iter().map(|c| c.1).sum()
    }
}

struct RowSearch<'a> {
    k: usize,
    projection: Projection,
    actions: Vec<Action>,
    group: &'a BitGroup,
    orientations: Vec<usize>,
}

// Approximate the cost in ordinary row leaves. Checking substitutions and a
// component partition has a fixed cost even when there are very few models.
fn contraction_cost(c: &Contraction) -> usize {
    let substitutions = c.steps.len().div_ceil(4);
    if c.conflict.is_some() {
        1 + substitutions
    } else if c.widths.len() > 1 {
        64 + substitutions
    } else {
        16 + substitutions + (1usize << c.ids.len()).div_ceil(1 << 16)
    }
}

impl RowSearch<'_> {
    fn fiber(&self, r: &Rep, ev: &mut MemoEval, solver: &mut Contractor) -> Fiber {
        let k = self.k;
        let mut f = Fiber::new(r, r.alpha, 0);
        if let Some(q) = r.dead {
            f.witnesses.push(q);
            f.chunks.push((WIDTH, 0));
            return f;
        }
        let whole = match solver.plan(k + D, r.alpha, B) {
            Some(c) if c.conflict.is_some() => {
                f.contracted.insert(0, c);
                f.chunks.push((WIDTH, 0));
                return f;
            }
            other => other,
        };

        let domain = self.projection.domain(r.alpha);
        let (mut cost, mut f) = self.plan(f, domain, solver);
        // The orbit minimum is convenient for coverage. Another choice of the two
        // product rows can have a much smaller domain on this same labelled problem.
        let mut alternative = None;
        let mut best = whole
            .as_ref()
            .map_or(cost, |c| cost.min(contraction_cost(c)));
        let mut tried = vec![r.alpha];
        for &j in &self.orientations {
            if best == 0 {
                break;
            }
            let image = self.group.act(j, r.alpha);
            if tried.contains(&image) {
                continue;
            }
            tried.push(image);
            let domain = self.projection.domain(image);
            let (_, gain) = Action::best(&self.actions, image, &domain.live, 0);
            let size = domain
                .live
                .iter()
                .map(|w| w.count_ones() as usize)
                .sum::<usize>()
                - gain;
            if size < best {
                best = size;
                alternative = Some((image, j, domain));
            }
        }
        if let Some((image, j, domain)) = alternative {
            let (other_cost, other) = self.plan(Fiber::new(r, image, j), domain, solver);
            if other_cost < cost {
                cost = other_cost;
                f = other;
            }
        }
        if let Some(c) = whole {
            if contraction_cost(&c) <= cost {
                let value = solver.count(&c, k + D, r.alpha);
                let mut direct = Fiber::new(r, r.alpha, 0);
                direct.contracted.insert(0, c);
                direct.chunks.push((WIDTH, value));
                return direct;
            }
        }
        let h = f.image;
        let span = u64::BITS as usize;
        let prefix_bits = D - span.ilog2() as usize;
        let weights = f.mixed.or_else(|| {
            f.action
                .map(|j| (self.actions[j].keep, self.actions[j].twice))
        });

        let (mut start, mut value, mut in_chunk) = (0, 0, 0);
        let mut i = 0;
        while i < WIDTH {
            if let Some(c) = f.contracted.get(&i) {
                if start < i {
                    f.chunks.push((i - start, value));
                }
                let key = ((h << D) + i as u64) / span as u64;
                f.chunks
                    .push((span, solver.count(c, k + D - prefix_bits, key)));
                i += span;
                (start, value, in_chunk) = (i, 0, 0);
                continue;
            }
            if f.mask[i / 64] >> (i % 64) & 1 != 0 {
                let w = match &weights {
                    Some((keep, _)) if keep[i / 64] >> (i % 64) & 1 == 0 => 0,
                    Some((_, twice)) => 1 + (twice[i / 64] >> (i % 64) & 1),
                    None => 1,
                };
                if w > 0 {
                    if in_chunk == 96 {
                        f.chunks.push((i - start, value));
                        (start, value, in_chunk) = (i, 0, 0);
                    }
                    value += w * ev.leaf_elim((h << D) + i as u64);
                    in_chunk += 1;
                    f.live += 1;
                }
            }
            i += 1;
        }
        if start < WIDTH {
            f.chunks.push((WIDTH - start, value));
        }
        debug_assert_eq!(
            cost,
            f.live + f.contracted.values().map(contraction_cost).sum::<usize>()
        );
        f
    }

    fn plan(&self, mut f: Fiber, domain: Domain, solver: &Contractor) -> (usize, Fiber) {
        let k = self.k;
        let actions = &self.actions;
        let h = f.image;
        f.mask = domain.live;
        f.witnesses = domain.witnesses;
        f.probes = domain.probes;
        let (symmetry, symmetry_savings) = Action::best(actions, h, &domain.live, 0);
        let mut blocks = 0;
        let span = u64::BITS as usize;
        let prefix_bits = D - span.ilog2() as usize;
        let mut saved = 0;
        for (prefix, &word) in domain.live.iter().enumerate() {
            let candidates = word.count_ones() as usize;
            if candidates < 4 {
                continue;
            }
            let key = (h << prefix_bits) + prefix as u64;
            if let Some(c) = solver.plan(k + D - prefix_bits, key, B - 2) {
                let cost = contraction_cost(&c);
                if candidates <= cost {
                    continue;
                }
                f.contracted.insert(prefix * span, c);
                saved += candidates - cost;
                blocks |= 1 << prefix;
            }
        }
        let (mixed, extra) = if blocks == 0 || symmetry.is_none() {
            (None, 0)
        } else {
            Action::best(actions, h, &domain.live, blocks)
        };
        if saved + extra > symmetry_savings {
            f.action = mixed;
            f.mixed = mixed.map(|j| actions[j].weights(blocks));
        } else {
            f.contracted.clear();
            f.action = symmetry;
        }
        let live = domain
            .live
            .iter()
            .map(|w| w.count_ones() as usize)
            .sum::<usize>();
        (live - symmetry_savings.max(saved + extra), f)
    }
}

fn emit_contraction(out: &mut String, name: &str, k: usize, h: u64, val: u64, c: &Contraction) {
    let steps: Vec<_> = c
        .steps
        .iter()
        .map(|(x, y, q)| format!("({x}, {y}, {q})"))
        .collect();
    writeln!(out, "theorem {name} : P.leaf {k} {h} = {val} := by").unwrap();
    if let Some(q) = c.conflict {
        writeln!(out, "  exact leaf_contract_zero (ss := {}) (q := {q}) check rows (by decide) (by decide +kernel) (by decide +kernel)\n",list(&steps)).unwrap();
    } else if c.widths.len() > 1 {
        writeln!(out, "  exact leaf_contract_factors (k := {k}) (b := {}) (H := {h}) (ss := {}) (ids := {}) (cs := {}) (bs := {}) (W := {val}) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)\n",
            c.ids.len(),list(&steps),list(&c.ids),list(&c.codes),list(&c.widths)).unwrap();
    } else {
        writeln!(out, "  apply (leaf_contract (k := {k}) (b := {}) (H := {h}) (ss := {}) (ids := {}) (cs := {}) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans\n  decide +kernel\n",
            c.ids.len(),list(&steps),list(&c.ids),list(&c.codes)).unwrap();
    }
}

// Both the weighted and unweighted assemblers use this ordinary block sum.
fn contracted_chunk(out: &mut String, f: &Fiber, k: usize, lo: usize, j: usize) -> Option<String> {
    let c = f.contracted.get(&lo)?;
    let (len, val) = f.chunks[j];
    let h = f.image;
    let d = len.ilog2() as usize;
    let key = ((h << D) + lo as u64) / len as u64;
    emit_contraction(out, &format!("contract{h}_{j}"), k + d, key, val, c);
    Some(format!("(leaf_eq_inner (k := {k}) (d := {d}) (H := {key}) rows (by decide) (by decide)).symm.trans contract{h}_{j}"))
}

fn emit_fiber(out: &mut String, f: &Fiber, m: usize) {
    let k = B + m;
    let outer = k + D;
    let h = f.image;
    let mask = mask_literal(&f.mask);
    if f.chunks.len() == 1 {
        if let Some(c) = f.contracted.get(&0) {
            emit_contraction(out, &format!("h{h}"), outer, h, f.count(), c);
            return;
        }
    }
    let witnesses = list(&f.witnesses);
    if f.probes.is_empty() {
        writeln!(out, "theorem cover{h} : P.CoversSplit {k} {D} {h} {} :=\n  coversSplit check rows (by decide) (by decide) (xs := {witnesses}) (by decide +kernel)\n", mask).unwrap();
    } else {
        let probes: Vec<_> = f
            .probes
            .iter()
            .map(|p| format!("({}, {}, {})", p.code, list(&p.zero), list(&p.one)))
            .collect();
        writeln!(out, "theorem cover{h} : P.CoversSplit {k} {D} {h} {} :=\n  coversProjected check rows (by decide) (by decide) (xs := {witnesses}) (ps := {}) (by decide +kernel)\n", mask, list(&probes)).unwrap();
    }
    // A sparse domain is the first axis of the remaining Cartesian product.
    // Give Lean the indices directly and check that their bit mask is exact.
    if f.contracted.is_empty() && f.mask.iter().map(|w| w.count_ones()).sum::<u32>() <= 32 {
        let indices: Vec<_> = (0..WIDTH)
            .filter(|&i| f.mask[i / 64] >> (i % 64) & 1 != 0)
            .collect();
        writeln!(
            out,
            "theorem h{h} : P.leaf {outer} {h} = {} := by",
            f.count()
        )
        .unwrap();
        let weight = if let Some(a) = f.action {
            writeln!(out, "  apply leaf_weighted (k := {k}) (d := {D}) (H := {h}) (keep := keep{a}) (twice := twice{a}) rows (by decide) (by decide) bal{a} (invRow{a} (H := {h}) (by decide) (by decide +kernel))").unwrap();
            format!("rowWeight keep{a} twice{a}")
        } else {
            writeln!(out, "  apply leaf_of_rowSum (k := {k}) (d := {D}) (H := {h}) rows (by decide) (by decide)").unwrap();
            "fun _ => 1".to_string()
        };
        writeln!(out, "  apply rowSum_sparse (b := {B}) (m := {m}) (d := {D}) (H := {h}) (weight := {weight}) (xs := {}) check rows elimOK (by decide) (by decide) cover{h} (by decide) (by decide) (by decide +kernel)\n  decide +kernel\n", list(&indices)).unwrap();
        return;
    }
    if let Some(a) = f.action {
        let base = h << D;
        let (keep, twice, balance) = if let Some((keep, twice)) = &f.mixed {
            writeln!(
                out,
                "def k{h} : ℕ := {}\ndef t{h} : ℕ := {}\n",
                mask_literal(keep),
                mask_literal(twice)
            )
            .unwrap();
            (
                format!("k{h}"),
                format!("t{h}"),
                "balancedRows_of_check (by decide +kernel)".to_string(),
            )
        } else {
            (format!("keep{a}"), format!("twice{a}"), format!("bal{a}"))
        };
        writeln!(out, "noncomputable def f{h} (i : ℕ) := rowWeight {keep} {twice} i * P.leaf {k} ({base} + i)\n").unwrap();
        let mut lo = 0;
        for (j, &(len, val)) in f.chunks.iter().enumerate() {
            if let Some(sum) = contracted_chunk(out, f, k, lo, j) {
                writeln!(out, "theorem c{h}_{j} : rowSum f{h} {lo} {len} = {val} :=\n  (rowSum_unit_block (P := P) (keep := {keep}) (twice := {twice}) (by decide +kernel)).trans ({sum})\n").unwrap();
            } else {
                writeln!(out, "theorem c{h}_{j} : rowSum f{h} {lo} {len} = {val} := by\n  apply weightedChunk_eq (b := {B}) (m := {m}) (d := {D}) (H := {h}) (keep := {keep}) (twice := {twice}) check rows elimOK (by decide) (by decide) cover{h} (by decide)\n  decide +kernel\n").unwrap();
            }
            lo += len;
        }
        let last = f.chunks.len() - 1;
        let mut pf = format!("c{h}_{last}");
        let (mut span, mut total) = f.chunks[last];
        for j in (0..last).rev() {
            let (n, v) = f.chunks[j];
            let lo = WIDTH - span - n;
            pf = format!("rowSum_append (F := f{h}) (lo := {lo}) (n := {n}) (m := {span}) (A := {v}) (B := {total}) c{h}_{j} ({pf})");
            span += n;
            total += v;
        }
        writeln!(
            out,
            "theorem sum{h} : rowSum f{h} 0 {WIDTH} = {total} :=\n  {pf}\n"
        )
        .unwrap();
        writeln!(out, "theorem h{h} : P.leaf {outer} {h} = {total} :=\n  leaf_weighted (k := {k}) (d := {D}) (H := {h}) (keep := {keep}) (twice := {twice}) rows (by decide) (by decide) ({balance}) (invRow{a} (H := {h}) (by decide) (by decide +kernel)) sum{h}\n").unwrap();
        return;
    }
    let mut lo = 0;
    for (j, &(len, val)) in f.chunks.iter().enumerate() {
        if let Some(sum) = contracted_chunk(out, f, k, lo, j) {
            let base = (h << D) + lo as u64;
            writeln!(
                out,
                "theorem c{h}_{j} : P.sumLeaves {k} {base} {len} = {val} :=\n  {sum}\n"
            )
            .unwrap();
            lo += len;
            continue;
        }
        writeln!(out, "theorem c{h}_{j} : P.sumLeaves {k} {} {len} = {val} := by\n  apply sumLeaves_splitChunk (b := {B}) (m := {m}) (d := {D}) (H := {h}) (lo := {lo}) (len := {len}) (W := {val}) check rows elimOK (by decide) (by decide) cover{h} (by decide)\n  decide +kernel\n",
                 (h << D) + lo as u64).unwrap();
        lo += len;
    }
    let chunks: Vec<_> = f
        .chunks
        .iter()
        .map(|(len, val)| format!("({len}, {val})"))
        .collect();
    let mut proof = ".nil".to_string();
    for j in (0..chunks.len()).rev() {
        proof = format!(".cons c{h}_{j} ({proof})");
    }
    writeln!(out, "theorem h{h} : P.leaf {outer} {h} = {} :=\n  (leaf_eq_inner (k := {k}) (d := {D}) rows (by decide) (by decide)).trans\n    (sumLeaves_of_chunks (cs := {}) ({proof}) (by decide) (by decide))\n", f.count(), list(&chunks)).unwrap();
}

pub(super) fn emit(ctx: &Ctx, sys: &Sys, rep: &[usize], hs: &[Vec<usize>]) -> u128 {
    let p = Problem::new(sys, rep, &order);
    let m = p.s;
    let outer = B + m + D;
    let t = p.nvars - outer;
    let tags = p.quad_tags(B, m);
    let (qt, ow) = trees(&p, B, m, &tags);
    let grp = BitGroup::new(&p, B + m + D, hs);
    let reps = all_reps(&p, B + m + D, 0, &grp);
    // The interval test treats the loops as unknown. Even an equation mentioning a
    // loop can have opposite constant sides, so include every nontrivial quadruple.
    let projection = Projection::new(&p, B + m);
    let actions = Action::all(&p, B + m, hs);
    // Renamings inducing the same set of ten original row bits describe the
    // same projection up to relabelling. Try one per distinct set.
    let mut seen = std::collections::BTreeSet::new();
    let orientations = grp
        .syms
        .iter()
        .enumerate()
        .filter_map(|(j, sym)| {
            let mask = sym.vq[B + m..outer].iter().fold(0u64, |a, v| a | (1 << v));
            seen.insert(mask).then_some(j)
        })
        .collect();
    let search = RowSearch {
        k: B + m,
        projection,
        actions,
        group: &grp,
        orientations,
    };
    let ev = Evaluator::new(&p, B);
    let workers = std::thread::available_parallelism()
        .map(|x| x.get())
        .unwrap_or(4)
        .min(10);
    let fibers = std::thread::scope(|sc| {
        let handles: Vec<_> = reps
            .chunks(reps.len().div_ceil(workers))
            .map(|rs| {
                let (search, ev, tags) = (&search, &ev, &tags);
                sc.spawn(move || {
                    let mut memo = MemoEval::new(ev, m, tags, 600 << 20);
                    let mut solver = Contractor::new(ev.p);
                    rs.iter()
                        .map(|r| search.fiber(r, &mut memo, &mut solver))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });

    let module = format!("{}.C0", ctx.module);
    let ns = format!("{}.C0", ctx.namespace);
    let defs = format!("{module}.Defs");
    let doc = "Generated identity-class certificate for the product-row count.";
    let mut out = file_prelude(&["Solution.Cert.Factors".into()], doc);
    writeln!(out, "namespace {ns}\n\nopen RACert RACert.Problem\n").unwrap();
    out.push_str(&problem_def(&p));
    group_and_trees(&mut out, &grp, B, m, &qt, &ow);
    writeln!(
        out,
        "theorem symsOK : P.checkSyms {outer} syms perms = true := by decide +kernel\n"
    )
    .unwrap();
    writeln!(
        out,
        "theorem grpOK : checkBitGroup {t} perms gens inv = true := by decide +kernel\n"
    )
    .unwrap();
    writeln!(
        out,
        "def orbitCols : List ℕ := {}\n",
        list(&orbit_columns(&grp))
    )
    .unwrap();
    writeln!(
        out,
        "theorem colsOK : cols {t} perms.length perms = orbitCols := by decide +kernel\n\nend {ns}"
    )
    .unwrap();
    write_file(&ctx.path_of(&defs), &out);

    let action_module = format!("{module}.Actions");
    let mut out = file_prelude(std::slice::from_ref(&defs), doc);
    writeln!(out, "namespace {ns}\n\nopen RACert RACert.Problem\n").unwrap();
    let k = B + m;
    let top = t + D;
    for &j in &search.orientations {
        if j == 0 || !fibers.iter().any(|f| f.orientation == j) {
            continue;
        }
        let sym = &grp.syms[j];
        let (pm, inv) = &grp.perms[j];
        writeln!(out, "def os{j} : Sym := {{ h := {}, hi := {}, vp := {}, vq := {} }}\ndef op{j} : List ℕ × List ℕ := ({}, {})", list(&sym.h), list(&sym.hi), list(&sym.vp), list(&sym.vq), list(pm), list(inv)).unwrap();
        writeln!(out, "theorem orient{j} {{h v n : ℕ}} (hh : h < 2 ^ {t}) (hi : actBits {t} op{j}.1 h = v) (hv : P.leaf {outer} v = n) : P.leaf {outer} h = n := by\n  subst v\n  exact (leaf_actBits (S := os{j}) (e := op{j}) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv\n").unwrap();
    }
    for (i, a) in search.actions.iter().enumerate() {
        if !fibers.iter().any(|f| f.action == Some(i)) {
            continue;
        }
        let sym = &a.sym;
        writeln!(
            out,
            "def sym{i} : Sym := {{ h := {}, hi := {}, vp := {}, vq := {} }}",
            list(&sym.h),
            list(&sym.hi),
            list(&sym.vp),
            list(&sym.vq)
        )
        .unwrap();
        writeln!(
            out,
            "def perm{i} : List ℕ × List ℕ := ({}, {})",
            list(&a.high),
            list(&crate::sys::inverse(&a.high))
        )
        .unwrap();
        writeln!(
            out,
            "def keep{i} : ℕ := {}\ndef twice{i} : ℕ := {}",
            mask_literal(&a.keep),
            mask_literal(&a.twice)
        )
        .unwrap();
        writeln!(out, "theorem bal{i} : BalancedRows {D} keep{i} twice{i} (actBits {top} perm{i}.1) :=\n  balancedRows_of_check (by decide +kernel)").unwrap();
        writeln!(out, "theorem invRow{i} {{H : ℕ}} (hh : H < 2 ^ {t}) (hs : actBits {top} perm{i}.1 ({WIDTH} * H) = {WIDTH} * H) : ∀ j < {WIDTH}, P.leaf {k} ({WIDTH} * H + actBits {top} perm{i}.1 j) = P.leaf {k} ({WIDTH} * H + j) :=\n  fun j hj => row_invariant (d := {D}) (S := sym{i}) (e := perm{i}) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal{i} j hj).1\n").unwrap();
    }
    writeln!(out, "end {ns}").unwrap();
    write_file(&ctx.path_of(&action_module), &out);
    let mut parts = Vec::new();
    let mut first = 0;
    while first < fibers.len() {
        let mut end = first;
        let mut live = 0;
        while end < fibers.len() && end - first < 32 && live < 1400 {
            live += fibers[end].live;
            end += 1;
        }
        let file = &fibers[first..end];
        let j = parts.len();
        let child = format!("{module}.S{j}");
        let mut out = file_prelude(std::slice::from_ref(&action_module), doc);
        writeln!(out, "namespace {ns}.S{j}\n\nopen RACert RACert.Problem\n").unwrap();
        for f in file {
            emit_fiber(&mut out, f, m);
            if f.orientation != 0 {
                writeln!(out, "theorem h{} : P.leaf {outer} {} = {} :=\n  orient{} (v := {}) (by decide) (by decide +kernel) h{}\n", f.minimum, f.minimum, f.count(), f.orientation, f.image, f.image).unwrap();
            }
        }
        let seg: Vec<_> = file
            .iter()
            .map(|f| format!("({}, {})", f.minimum, f.weight))
            .collect();
        let lo = file[0].minimum;
        let hi = fibers.get(end).map_or(1 << grp.t, |f| f.minimum);
        let mass = file.iter().map(|f| f.weight as u128).sum();
        let sum = file
            .iter()
            .map(|f| f.weight as u128 * f.count() as u128)
            .sum();
        writeln!(out, "def seg : List (ℕ × ℕ) := {}\n", list(&seg)).unwrap();
        writeln!(out, "theorem segOK : checkSeg {t} perms {lo} {hi} seg = true :=\n  checkSeg_of_cols colsOK (by decide +kernel)\n").unwrap();
        let mut proof = format!("show SegSum (P.leaf {outer}) [] 0 from rfl");
        for f in file.iter().rev() {
            proof = format!("SegSum.cons (w := {}) h{} ({proof})", f.weight, f.minimum);
        }
        writeln!(out, "theorem total : OrbitSeg {t} perms (P.leaf {outer}) {lo} {hi} {mass} {sum} :=\n  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := {sum})\n    ({proof}) (by decide)\n\nend {ns}.S{j}").unwrap();
        write_file(&ctx.path_of(&child), &out);
        parts.push((
            Part {
                lo,
                hi,
                m: mass,
                w: sum,
                name: format!("S{j}.total"),
            },
            child,
        ));
        first = end;
    }
    let total = parts.iter().map(|(p, _)| p.w).sum();
    let live: usize = fibers.iter().map(|f| f.live).sum();
    let mut tables = 0;
    let mut conflicts = 0;
    let mut factored = 0;
    for c in fibers.iter().flat_map(|f| f.contracted.values()) {
        if c.conflict.is_some() {
            conflicts += 1;
        } else if c.widths.len() > 1 {
            factored += 1;
        } else {
            tables += 1;
        }
    }
    println!(
        "  identity: {} hypergraph orbits, {live} inner leaves, {tables} contracted tables, {factored} factored cofactors, {conflicts} contraction conflicts, count {total}",
        fibers.len()
    );
    finish_class(
        ctx,
        &p,
        &ns,
        &defs,
        &module,
        &outer.to_string(),
        grp.t,
        parts,
        total,
        doc,
    );
    total
}
