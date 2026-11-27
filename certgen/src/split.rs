//! The identity class on six symmetric diversity atoms, split first by its 3-uniform hypergraph.

use super::*;
use crate::leaf::{Evaluator, MemoEval};
use crate::tree::Tree;
use std::collections::BTreeSet;

// The twenty distinct triples form an invariant outer block under S₆. Inside each
// representative, split off the two rows aab for a = 5,6. These labels are in the
// canonical hypergraph's numbering, so the inner block need not be invariant.
const B: usize = 20;
const M: usize = 6;
const D: usize = 10;
const WIDTH: usize = 1 << D;

fn order(p: &Problem, mut roots: Vec<usize>) -> Vec<usize> {
    roots.sort_by_key(|&x| {
        let (a, b, c) = (x / p.k / p.k, x / p.k % p.k, x % p.k);
        // Each representative is the sorted triple.
        if a == c {
            1 // eliminated loops
        } else if a != b && b != c {
            3 // hypergraph
        } else {
            let repeated = if a == b { a } else { b };
            if repeated >= 5 {
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
    live: usize,
    mask: String,
    chunks: Vec<(usize, u64)>,
}

impl Fiber {
    fn count(&self) -> u64 {
        self.chunks.iter().map(|c| c.1).sum()
    }
}

fn fiber(p: &Problem, r: &Rep, tree: &Tree, ev: &mut MemoEval) -> Fiber {
    if let Some(x) = r.dead {
        return Fiber {
            h: r.alpha,
            weight: r.m,
            witnesses: vec![x],
            live: 0,
            mask: "0".into(),
            chunks: vec![(WIDTH, 0)],
        };
    }
    let mut assign = vec![2; p.nvars];
    for (j, bit) in assign[B + M + D..].iter_mut().enumerate() {
        *bit = ((r.alpha >> j) & 1) as u8;
    }
    let mut witnesses = BTreeSet::new();
    let mut digits = [0u8; WIDTH / 4];
    let mut chunks = Vec::new();
    let (mut start, mut value, mut live, mut in_chunk) = (0, 0, 0, 0);
    for i in 0..WIDTH {
        for (j, bit) in assign[B + M..B + M + D].iter_mut().enumerate() {
            *bit = ((i >> j) & 1) as u8;
        }
        if let Some(q) = tree.dead(&assign) {
            witnesses.insert(p.quads[q]);
        } else {
            if in_chunk == 96 {
                chunks.push((i - start, value));
                (start, value, in_chunk) = (i, 0, 0);
            }
            digits[i / 4] |= 1 << (i % 4);
            value += ev.leaf_elim((r.alpha << D) + i as u64);
            in_chunk += 1;
            live += 1;
        }
    }
    chunks.push((WIDTH - start, value));
    let hex: String = digits
        .iter()
        .rev()
        .map(|&d| char::from_digit(d.into(), 16).unwrap())
        .collect();
    let mask = if live == 0 {
        "0".into()
    } else {
        format!("0x{}", hex.trim_start_matches('0'))
    };
    Fiber {
        h: r.alpha,
        weight: r.m,
        witnesses: witnesses.into_iter().collect(),
        live,
        mask,
        chunks,
    }
}

fn emit_fiber(out: &mut String, f: &Fiber) {
    let h = f.h;
    writeln!(out, "theorem cover{h} : P.CoversSplit 26 10 {h} {} :=\n  coversSplit check rows (by decide) (by decide) (xs := {}) (by decide +kernel)\n",
             f.mask, list(&f.witnesses)).unwrap();
    let mut lo = 0;
    for (j, &(len, val)) in f.chunks.iter().enumerate() {
        writeln!(out, "theorem c{h}_{j} : P.sumLeaves 26 {} {len} = {val} := by\n  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := {h}) (lo := {lo}) (len := {len}) (W := {val}) check rows elimOK (by decide) (by decide) cover{h} (by decide)\n  decide +kernel\n",
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
    writeln!(out, "theorem h{h} : P.leaf 36 {h} = {} :=\n  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans\n    (sumLeaves_of_chunks (cs := {}) ({proof}) (by decide) (by decide))\n", f.count(), list(&chunks)).unwrap();
}

pub(super) fn emit(ctx: &Ctx, sys: &Sys, rep: &[usize], hs: &[Vec<usize>]) -> u128 {
    let p = Problem::new(sys, rep, &order);
    let tags = p.quad_tags(B, M);
    let (qt, ow) = trees(&p, B, M, &tags);
    let grp = BitGroup::new(&p, B + M + D, hs);
    let reps = all_reps(&p, B + M + D, 0, &grp);
    // The interval test treats the loops as unknown. Even an equation mentioning a
    // loop can have opposite constant sides, so include every nontrivial quadruple.
    let tree = Tree::new_elim(&p, B + M, 0);
    let ev = Evaluator::new(&p, B);
    let workers = std::thread::available_parallelism()
        .map(|x| x.get())
        .unwrap_or(4)
        .min(10);
    let fibers = std::thread::scope(|sc| {
        let handles: Vec<_> = reps
            .chunks(reps.len().div_ceil(workers))
            .map(|rs| {
                let (p, tree, ev, tags) = (&p, &tree, &ev, &tags);
                sc.spawn(move || {
                    let mut memo = MemoEval::new(ev, M, tags, 600 << 20);
                    rs.iter()
                        .map(|r| fiber(p, r, tree, &mut memo))
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
    let doc = "Generated certificate for the identity on six symmetric diversity atoms.";
    let mut out = file_prelude(&["Solution.Cert.Split".into()], doc);
    writeln!(out, "namespace {ns}\n\nopen RACert RACert.Problem\n").unwrap();
    out.push_str(&problem_def(&p));
    group_and_trees(&mut out, &grp, B, M, &qt, &ow);
    writeln!(
        out,
        "theorem symsOK : P.checkSyms 36 syms perms = true := by decide +kernel\n"
    )
    .unwrap();
    writeln!(
        out,
        "theorem grpOK : checkBitGroup 20 perms gens inv = true := by decide +kernel\n"
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
        "theorem colsOK : cols 20 perms.length perms = orbitCols := by decide +kernel\n\nend {ns}"
    )
    .unwrap();
    write_file(&ctx.path_of(&defs), &out);

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
        let mut out = file_prelude(std::slice::from_ref(&defs), doc);
        writeln!(out, "namespace {ns}.S{j}\n\nopen RACert RACert.Problem\n").unwrap();
        for f in file {
            emit_fiber(&mut out, f);
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
        writeln!(out, "theorem segOK : checkSeg 20 perms {lo} {hi} seg = true :=\n  checkSeg_of_cols colsOK (by decide +kernel)\n").unwrap();
        let mut proof = "show SegSum (P.leaf 36) [] 0 from rfl".to_string();
        for f in file.iter().rev() {
            proof = format!("SegSum.cons (w := {}) h{} ({proof})", f.weight, f.h);
        }
        writeln!(out, "theorem total : OrbitSeg 20 perms (P.leaf 36) {lo} {hi} {mass} {sum} :=\n  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := {sum})\n    ({proof}) (by decide)\n\nend {ns}.S{j}").unwrap();
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
    println!(
        "  identity: {} hypergraph orbits, {live} inner leaves, count {total}",
        fibers.len()
    );
    finish_class(ctx, &p, &ns, &defs, &module, "36", grp.t, parts, total, doc);
    total
}
