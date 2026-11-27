//! Count the identity class by the cycles on three converse-orbits and the remaining product rows.

use super::*;
use crate::contract::{Contraction, Contractor};
use crate::leaf::{Evaluator, MemoEval};
use crate::row::{mask_literal, Action, Probe, Projection};
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
    h: u64,
    weight: u64,
    witnesses: Vec<usize>,
    probes: Vec<Probe>,
    action: Option<usize>,
    live: usize,
    mask: String,
    chunks: Vec<(usize, u64)>,
    contracted: BTreeMap<usize, Contraction>,
}

impl Fiber {
    fn count(&self) -> u64 {
        self.chunks.iter().map(|c| c.1).sum()
    }
}

fn fiber(
    r: &Rep,
    k: usize,
    projection: &Projection,
    actions: &[Action],
    ev: &mut MemoEval,
    solver: &mut Contractor,
) -> Fiber {
    let mut f = Fiber {
        h: r.alpha,
        weight: r.m,
        witnesses: vec![],
        probes: vec![],
        action: None,
        live: 0,
        mask: "0".into(),
        chunks: vec![],
        contracted: BTreeMap::new(),
    };
    if let Some(q) = r.dead {
        f.witnesses.push(q);
        f.chunks.push((WIDTH, 0));
        return f;
    }
    if let Some(c) = solver.plan(k + D, r.alpha, B) {
        let val = solver.count(&c, k + D, r.alpha);
        f.contracted.insert(0, c);
        f.chunks.push((WIDTH, val));
        return f;
    }

    let domain = projection.domain(r.alpha);
    f.mask = mask_literal(&domain.live);
    f.witnesses = domain.witnesses;
    f.probes = domain.probes;
    f.action = Action::best(actions, r.alpha, &domain.live);

    // A prefix fixes four further cycles. One contracted cofactor replaces
    // up to 64 standard tables. Only switch plans if it saves more evaluations
    // than quotienting the fibre by its best row involution.
    let span = u64::BITS as usize;
    let prefix_bits = D - span.ilog2() as usize;
    let mut saved = 0;
    for (prefix, &word) in domain.live.iter().enumerate() {
        let candidates = word.count_ones() as usize;
        if candidates < 4 {
            continue;
        }
        let key = (r.alpha << prefix_bits) + prefix as u64;
        if let Some(c) = solver.plan(k + D - prefix_bits, key, B - 2) {
            f.contracted.insert(prefix * span, c);
            saved += candidates - 1;
        }
    }
    let symmetry_savings = f.action.map_or(0, |j| {
        domain
            .live
            .iter()
            .zip(actions[j].keep)
            .map(|(&w, keep)| (w & !keep).count_ones() as usize)
            .sum()
    });
    if saved > symmetry_savings {
        f.action = None;
    } else {
        f.contracted.clear();
    }

    let (mut start, mut value, mut in_chunk) = (0, 0, 0);
    let mut i = 0;
    while i < WIDTH {
        if let Some(c) = f.contracted.get(&i) {
            if start < i {
                f.chunks.push((i - start, value));
            }
            let key = ((r.alpha << D) + i as u64) / span as u64;
            f.chunks
                .push((span, solver.count(c, k + D - prefix_bits, key)));
            i += span;
            (start, value, in_chunk) = (i, 0, 0);
            continue;
        }
        if domain.live[i / 64] >> (i % 64) & 1 != 0 {
            let w = match f.action.map(|j| &actions[j]) {
                Some(a) if a.keep[i / 64] >> (i % 64) & 1 == 0 => 0,
                Some(a) => 1 + (a.twice[i / 64] >> (i % 64) & 1),
                None => 1,
            };
            if w > 0 {
                if in_chunk == 96 {
                    f.chunks.push((i - start, value));
                    (start, value, in_chunk) = (i, 0, 0);
                }
                value += w * ev.leaf_elim((r.alpha << D) + i as u64);
                in_chunk += 1;
                f.live += 1;
            }
        }
        i += 1;
    }
    if start < WIDTH {
        f.chunks.push((WIDTH - start, value));
    }
    f
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

fn emit_fiber(out: &mut String, f: &Fiber, m: usize) {
    let k = B + m;
    let outer = k + D;
    let h = f.h;
    if f.chunks.len() == 1 {
        if let Some(c) = f.contracted.get(&0) {
            emit_contraction(out, &format!("h{h}"), outer, h, f.count(), c);
            return;
        }
    }
    let witnesses = list(&f.witnesses);
    if f.probes.is_empty() {
        writeln!(out, "theorem cover{h} : P.CoversSplit {k} {D} {h} {} :=\n  coversSplit check rows (by decide) (by decide) (xs := {witnesses}) (by decide +kernel)\n", f.mask).unwrap();
    } else {
        let probes: Vec<_> = f
            .probes
            .iter()
            .map(|p| format!("({}, {}, {})", p.code, list(&p.zero), list(&p.one)))
            .collect();
        writeln!(out, "theorem cover{h} : P.CoversSplit {k} {D} {h} {} :=\n  coversProjected check rows (by decide) (by decide) (xs := {witnesses}) (ps := {}) (by decide +kernel)\n", f.mask, list(&probes)).unwrap();
    }
    if let Some(a) = f.action {
        let base = h << D;
        writeln!(out, "noncomputable def f{h} (i : ℕ) := rowWeight keep{a} twice{a} i * P.leaf {k} ({base} + i)\n").unwrap();
        let mut lo = 0;
        for (j, &(len, val)) in f.chunks.iter().enumerate() {
            writeln!(out, "theorem c{h}_{j} : rowSum f{h} {lo} {len} = {val} := by\n  apply weightedChunk_eq (b := {B}) (m := {m}) (d := {D}) (H := {h}) (keep := keep{a}) (twice := twice{a}) check rows elimOK (by decide) (by decide) cover{h} (by decide)\n  decide +kernel\n").unwrap();
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
        writeln!(out, "theorem h{h} : P.leaf {outer} {h} = {total} :=\n  leaf_weighted (k := {k}) (d := {D}) (H := {h}) (keep := keep{a}) (twice := twice{a}) rows (by decide) (by decide) bal{a} (invRow{a} (H := {h}) (by decide) (by decide +kernel)) sum{h}\n").unwrap();
        return;
    }
    let mut lo = 0;
    for (j, &(len, val)) in f.chunks.iter().enumerate() {
        if let Some(c) = f.contracted.get(&lo) {
            let d = len.ilog2() as usize;
            let base = (h << D) + lo as u64;
            let key = base / (len as u64);
            emit_contraction(out, &format!("contract{h}_{j}"), k + d, key, val, c);
            writeln!(out, "theorem c{h}_{j} : P.sumLeaves {k} {base} {len} = {val} :=\n  (leaf_eq_inner (k := {k}) (d := {d}) (H := {key}) rows (by decide) (by decide)).symm.trans contract{h}_{j}\n").unwrap();
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
    let ev = Evaluator::new(&p, B);
    let workers = std::thread::available_parallelism()
        .map(|x| x.get())
        .unwrap_or(4)
        .min(10);
    let fibers = std::thread::scope(|sc| {
        let handles: Vec<_> = reps
            .chunks(reps.len().div_ceil(workers))
            .map(|rs| {
                let (projection, actions, ev, tags) = (&projection, &actions, &ev, &tags);
                sc.spawn(move || {
                    let mut memo = MemoEval::new(ev, m, tags, 600 << 20);
                    let mut solver = Contractor::new(ev.p);
                    rs.iter()
                        .map(|r| fiber(r, B + m, projection, actions, &mut memo, &mut solver))
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
    for (i, a) in actions.iter().enumerate() {
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
        }
        let seg: Vec<_> = file
            .iter()
            .map(|f| format!("({}, {})", f.h, f.weight))
            .collect();
        let lo = file[0].h;
        let hi = fibers.get(end).map_or(1 << grp.t, |f| f.h);
        let mass = file.iter().map(|f| f.weight as u128).sum();
        let sum = file
            .iter()
            .map(|f| f.weight as u128 * f.count() as u128)
            .sum();
        writeln!(out, "def seg : List (ℕ × ℕ) := {}\n", list(&seg)).unwrap();
        writeln!(out, "theorem segOK : checkSeg {t} perms {lo} {hi} seg = true :=\n  checkSeg_of_cols colsOK (by decide +kernel)\n").unwrap();
        let mut proof = format!("show SegSum (P.leaf {outer}) [] 0 from rfl");
        for f in file.iter().rev() {
            proof = format!("SegSum.cons (w := {}) h{} ({proof})", f.weight, f.h);
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
