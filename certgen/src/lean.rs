//! Emission of the Lean certificate files.

use crate::leaf::all_leaves;
use crate::problem::Problem;
use crate::sys::{classes, Sys};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

const HEADER: &str = "/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/
";

/// Maximal number of chunk theorems (or sub-files) combined in one file.
const FANOUT: usize = 64;

fn list<T: std::fmt::Display>(v: &[T]) -> String {
    let mut s = String::from("[");
    for (i, x) in v.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        write!(s, "{}", x).unwrap();
    }
    s.push(']');
    s
}

fn nested3<T: std::fmt::Display>(v: &[T], k: usize) -> String {
    let rows: Vec<String> = (0..k)
        .map(|a| {
            let r: Vec<String> = (0..k).map(|b| list(&v[(a * k + b) * k..(a * k + b) * k + k])).collect();
            format!("[{}]", r.join(", "))
        })
        .collect();
    format!("[{}]", rows.join(",\n    "))
}

fn nested4<T: std::fmt::Display>(v: &[T], k: usize) -> String {
    let rows: Vec<String> = (0..k).map(|r| nested3(&v[r * k * k * k..(r + 1) * k * k * k], k)).collect();
    format!("[{}]", rows.join(",\n    "))
}

fn write_file(path: &Path, content: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, content).unwrap();
}

struct Ctx {
    root: PathBuf,
    /// e.g. `Solution.Atoms3.S2N0`
    module: String,
    /// e.g. `RACert.S2N0`
    namespace: String,
}

impl Ctx {
    fn path_of(&self, module: &str) -> PathBuf {
        let mut p = self.root.clone();
        for part in module.split('.') {
            p.push(part);
        }
        p.set_extension("lean");
        p
    }
}

fn file_prelude(imports: &[String], doc: &str) -> String {
    let mut s = String::new();
    s.push_str(HEADER);
    s.push_str("\nmodule\n\n");
    for i in imports {
        writeln!(s, "public import {}", i).unwrap();
    }
    writeln!(s, "\n/-! {} -/\n", doc).unwrap();
    // `Elab.async false`: with asynchronous elaboration the memory used by the kernel for one
    // theorem is only released at the end of the file, and leaves use a lot of it.
    s.push_str("set_option linter.style.longLine false\nset_option maxRecDepth 100000\nset_option Elab.async false\n\n");
    s.push_str("@[expose] public section\n\n");
    s
}

fn problem_def(p: &Problem) -> String {
    let k = p.k;
    let mut s = String::new();
    s.push_str("/-- The counting problem of this class. -/\ndef P : Problem where\n");
    writeln!(s, "  s := {}", p.s).unwrap();
    writeln!(s, "  n := {}", p.n).unwrap();
    writeln!(s, "  perm := {}", list(&p.perm)).unwrap();
    writeln!(s, "  pinv := {}", list(&p.pinv)).unwrap();
    writeln!(s, "  V := {}", p.nvars).unwrap();
    writeln!(s, "  cls := {}", nested3(&p.cls, k)).unwrap();
    writeln!(s, "  reps := {}", list(&p.reps)).unwrap();
    writeln!(s, "  path := {}", nested3(&p.path, k)).unwrap();
    writeln!(s, "  quads := {}", list(&p.quads)).unwrap();
    writeln!(s, "  wit := {}", nested4(&p.wit, k)).unwrap();
    s.push_str("\ntheorem check : P.check = true := by decide +kernel\n\n");
    s.push_str("theorem rows : P.checkRows = true := by decide +kernel\n\n");
    s
}

/// A chunk of consecutive leaves: start, count, value.
#[derive(Clone)]
struct Chunk {
    lo: u64,
    cnt: u64,
    val: u128,
}

/// Emit the theorems for `chunks` (recursively splitting into sub-files when there are too
/// many), ending with `theorem <name> : P.sumLeaves b lo cnt = val` in the current file content
/// `out`. `module` is the module of the current file; sub-files are placed below it. Returns the
/// list of extra imports needed by the current file.
fn emit_chunks(ctx: &Ctx, cls_ns: &str, defs_module: &str, module: &str, b: usize, chunks: &[Chunk], out: &mut String, name: &str) -> Vec<String> {
    let lo = chunks[0].lo;
    let cnt: u64 = chunks.iter().map(|c| c.cnt).sum();
    let val: u128 = chunks.iter().map(|c| c.val).sum();
    let mut imports = vec![];
    let mut items: Vec<(String, Chunk)> = vec![];
    if chunks.len() <= FANOUT {
        for c in chunks {
            let nm = format!("c{}", c.lo);
            writeln!(out, "theorem {} : P.sumLeaves {} {} {} = {} := by decide +kernel\n", nm, b, c.lo, c.cnt, c.val).unwrap();
            items.push((nm, c.clone()));
        }
    } else {
        let per = chunks.len().div_ceil(FANOUT);
        for (j, sub) in chunks.chunks(per).enumerate() {
            let sub_module = format!("{}.K{}", module, j);
            let sub_ns = format!("K{}", sub[0].lo);
            let mut content = file_prelude(&[defs_module.to_string()], "Generated certificate chunk; see `certgen`.");
            // placeholder: imports of the sub-file's own children are added below
            let mut body = String::new();
            writeln!(body, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
            writeln!(body, "namespace {}\n", sub_ns).unwrap();
            let sub_imports = emit_chunks(ctx, cls_ns, defs_module, &sub_module, b, sub, &mut body, "total");
            writeln!(body, "end {}\n\nend {}", sub_ns, cls_ns).unwrap();
            if !sub_imports.is_empty() {
                let mut imps = vec![defs_module.to_string()];
                imps.extend(sub_imports);
                content = file_prelude(&imps, "Generated certificate chunk; see `certgen`.");
            }
            content.push_str(&body);
            write_file(&ctx.path_of(&sub_module), &content);
            imports.push(sub_module);
            let c = Chunk { lo: sub[0].lo, cnt: sub.iter().map(|c| c.cnt).sum(), val: sub.iter().map(|c| c.val).sum() };
            items.push((format!("{}.total", sub_ns), c));
        }
    }
    let cs: Vec<String> = items.iter().map(|(_, c)| format!("({}, {})", c.cnt, c.val)).collect();
    let mut proof = String::from(".nil");
    for (nm, _) in items.iter().rev() {
        proof = format!(".cons {} ({})", nm, proof);
    }
    writeln!(
        out,
        "theorem {} : P.sumLeaves {} {} {} = {} :=\n  sumLeaves_of_chunks (cs := [{}])\n    ({})\n    (by decide +kernel) (by decide +kernel)\n",
        name,
        b,
        lo,
        cnt,
        val,
        cs.join(", "),
        proof
    )
    .unwrap();
    imports
}

/// Default variable order: by representative code.
fn default_order(_p: &Problem, roots: Vec<usize>) -> Vec<usize> {
    roots
}

/// Emit the certificate of one class without symmetry reduction: all leaves are evaluated.
fn emit_class_plain(ctx: &Ctx, sys: &Sys, i: usize, rep: &[usize], bmax: usize) -> u128 {
    let (s, n) = (sys.s, sys.n);
    let p = Problem::new(sys, rep, &default_order);
    let b = p.nvars.min(bmax);
    let t0 = std::time::Instant::now();
    let leaves = all_leaves(&p, b);
    let total: u128 = leaves.iter().map(|&x| x as u128).sum();
    println!("  class {} rep {:?}: vars {} quads {} b {} leaves {} count {} ({:?})", i, rep, p.nvars, p.quads.len(), b, leaves.len(), total, t0.elapsed());
    let chunks: Vec<Chunk> = leaves.iter().enumerate().map(|(a, &v)| Chunk { lo: a as u64, cnt: 1, val: v as u128 }).collect();
    let cls_module = format!("{}.C{}", ctx.module, i);
    let cls_ns = format!("{}.C{}", ctx.namespace, i);
    let single = chunks.len() <= FANOUT;
    let defs_module = if single { cls_module.clone() } else { format!("{}.Defs", cls_module) };
    let mut defs = String::new();
    writeln!(defs, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
    defs.push_str(&problem_def(&p));
    let mut body = String::new();
    let imports = emit_chunks(ctx, &cls_ns, &defs_module, &cls_module, b, &chunks, &mut body, "total");
    writeln!(
        body,
        "/-- The number of lawful cycle sets invariant under the symmetry of this class. -/\ntheorem count : fixCountL {} {} {} = {} :=\n  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total\n",
        s,
        n,
        list(rep),
        total
    )
    .unwrap();
    let doc = format!("Generated certificate (see `certgen`): symmetry class {} of type ({}, {}).", i, s, n);
    if single {
        let mut content = file_prelude(&["Solution.Cert.Eval".to_string()], &doc);
        content.push_str(&defs);
        content.push_str(&body);
        writeln!(content, "end {}", cls_ns).unwrap();
        write_file(&ctx.path_of(&cls_module), &content);
    } else {
        let mut dcontent = file_prelude(&["Solution.Cert.Eval".to_string()], &doc);
        dcontent.push_str(&defs);
        writeln!(dcontent, "end {}", cls_ns).unwrap();
        write_file(&ctx.path_of(&defs_module), &dcontent);
        let mut imps = vec![defs_module.clone()];
        imps.extend(imports);
        let mut content = file_prelude(&imps, &doc);
        writeln!(content, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
        content.push_str(&body);
        writeln!(content, "end {}", cls_ns).unwrap();
        write_file(&ctx.path_of(&cls_module), &content);
    }
    total
}

pub fn generate(s: usize, n: usize, root: &Path, bmax: usize) {
    let sys = Sys::new(s, n);
    let k = sys.k;
    let ctx = Ctx {
        root: root.to_path_buf(),
        module: format!("Solution.Atoms{}.S{}N{}", k, s, n),
        namespace: format!("RACert.S{}N{}", s, n),
    };
    // start from a clean directory so that stale files of earlier runs do not linger
    let dir = ctx.path_of(&ctx.module).with_extension("");
    let _ = fs::remove_dir_all(&dir);
    let g = sys.group();
    let cl = classes(&g);
    println!("({},{}): k={} |G|={} classes={}", s, n, k, g.len(), cl.reps.len());
    let mut counts: Vec<u128> = vec![];
    for (i, rep) in cl.reps.iter().enumerate() {
        let nvars = Problem::new(&sys, rep, &default_order).nvars;
        let total = if nvars <= bmax {
            emit_class_plain(&ctx, &sys, i, rep, bmax)
        } else {
            let hs = centralizer(&g, rep);
            emit_class_sym(&ctx, &sys, i, rep, &hs, bmax)
        };
        counts.push(total);
    }
    // Burnside
    let weighted: u128 = cl.elems.iter().map(|(_, i, _)| counts[*i]).sum();
    let order = g.len() as u128;
    assert_eq!(weighted % order, 0, "Burnside sum not divisible by the group order");
    let orbits = weighted / order;
    println!("  Burnside sum {} = {} * {}", weighted, orbits, order);
    let mut imps = vec!["Solution.Cert.Group".to_string()];
    for i in 0..cl.reps.len() {
        imps.push(format!("{}.C{}", ctx.module, i));
    }
    let mut content = file_prelude(&imps, &format!("Generated certificate (see `certgen`): Burnside count for type ({}, {}).", s, n));
    writeln!(content, "namespace {}\n\nopen RACert\n", ctx.namespace).unwrap();
    let reps: Vec<String> = cl.reps.iter().map(|r| list(r)).collect();
    writeln!(content, "/-- Representatives of the conjugacy classes of the symmetry group. -/\ndef reps : List (List ℕ) :=\n  [{}]\n", reps.join(", ")).unwrap();
    let elems: Vec<String> = cl.elems.iter().map(|(l, i, t)| format!("({}, {}, {})", list(l), i, list(t))).collect();
    writeln!(content, "/-- All elements of the symmetry group, with their class and a conjugator. -/\ndef elems : List (List ℕ × ℕ × List ℕ) :=\n  [{}]\n", elems.join(",\n   ")).unwrap();
    writeln!(content, "theorem groupCert : checkGroup {} {} reps elems = true := by decide +kernel\n", s, n).unwrap();
    let mut fa = String::from(".nil");
    for i in (0..cl.reps.len()).rev() {
        fa = format!(".cons C{}.count ({})", i, fa);
    }
    writeln!(
        content,
        "/-- The number of isomorphism classes of integral relation algebras of type ({s}, {n}). -/\ntheorem count : (Cslib.RelationAlgebra.IntegralAlgebra.IsoClass.ofSymmNsymm {s} {n}).encard = ({orbits} : ℕ) :=\n  encard_ofSymmNsymm_of_groupCert' {s} {n} {orbits} reps elems {cs} groupCert\n    ({fa})\n    (by decide +kernel)\n",
        s = s,
        n = n,
        orbits = orbits,
        cs = list(&counts),
        fa = fa
    )
    .unwrap();
    writeln!(content, "end {}", ctx.namespace).unwrap();
    write_file(&ctx.path_of(&format!("{}.Group", ctx.module)), &content);
    println!("  => {} isomorphism classes", orbits);
}

use crate::leaf::QTree;
use crate::symm::{all_reps, centralizer, choose_low, BitGroup, Rep};

/// Maximal number of orbit minima in one part (a pair of checking theorems).
const PART_REPS: usize = 1500;

/// The tree of the quadruples not depending on the eliminated variables (those depending only
/// on slowly changing high variables first), and the trees of the quadruples depending on each
/// eliminated variable.
fn trees(p: &Problem, b: usize, m: usize, tags: &[Option<usize>]) -> (QTree, Vec<QTree>) {
    let index: std::collections::HashMap<usize, usize> = p.quads.iter().enumerate().map(|(i, &x)| (x, i)).collect();
    let mut next_id = 0usize;
    let mut tree = |tag: usize| -> QTree {
        let items: Vec<(usize, usize)> = p.tagged_quads(b, tags, tag).iter().map(|&(x, m1, m2)| {
            assert_eq!((m1, m2), { let (l, r) = p.quad_terms(x); (crate::leaf::classify(b, &l).0, crate::leaf::classify(b, &r).0) });
            (index[&x], x)
        }).collect();
        if items.is_empty() {
            // the quadruple of the identity atom: its condition always holds
            return QTree::leaf(p, b, usize::MAX, 0);
        }
        QTree::balanced(p, b, &items, &mut next_id)
    };
    let qt = tree(0);
    let ow = (0..m).map(|i| tree(i + 1)).collect();
    (qt, ow)
}

/// Maximal number of parts in one segment file.
const FILE_PARTS: usize = 24;

/// Maximal number of orbit minima in one segment file (they are checked by one theorem).
const FILE_REPS: usize = 6000;

/// Number of big-number operations of the weighted population count of `n` tables
/// (`RACert.wtotF`).
pub const WPOP: [usize; 9] = [0, 16, 23, 32, 37, 51, 56, 65, 70];

/// Number of big-number results the kernel retains for one evaluated leaf: about 50 for the
/// conditions, those of the weight tables of the `m` eliminated variables and of their
/// population count.
pub fn leaf_ops(m: usize) -> usize {
    50 + 3 * m * (m + 1) / 2 + 2 * m + WPOP[(m + 1).min(8)]
}

/// Maximal number of evaluated leaves in one theorem: the big-number results of one declaration
/// are all retained by the kernel and should stay around two gigabytes.
fn seg_live(b: usize, m: usize) -> usize {
    let per_leaf = leaf_ops(m) as f64 * (1u64 << b) as f64 / 8.0;
    ((2.0e9 / per_leaf) as usize).clamp(4, 256)
}

fn pairs(v: &[(Vec<usize>, Vec<usize>)]) -> String {
    let items: Vec<String> = v.iter().map(|(p, q)| format!("({}, {})", list(p), list(q))).collect();
    format!("[{}]", items.join(",\n   "))
}

/// A certified part of the orbit sum: `[lo, hi)` with total orbit size `m` and weighted sum `w`,
/// proved by `name` in module `module`.
#[derive(Clone)]
struct Part {
    lo: u64,
    hi: u64,
    m: u128,
    w: u128,
    name: String,
}

/// Emit segment files and (recursively) combining files. Returns the theorem proving the whole
/// range and the imports the caller needs.
fn emit_parts(ctx: &Ctx, cls_ns: &str, defs_module: &str, module: &str, b: &str, t: usize, parts: Vec<(Part, String)>, out: &mut String, name: &str) -> (Part, Vec<String>) {
    // parts: (part, module providing it)
    let _ = ctx;
    let mut items: Vec<(Part, String)> = parts;
    let mut level = 0;
    while items.len() > FANOUT {
        // group into intermediate files
        let per = FANOUT;
        let mut next: Vec<(Part, String)> = vec![];
        for (j, group) in items.chunks(per).enumerate() {
            let sub_module = format!("{}.G{}x{}", module, level, j);
            let sub_ns = format!("G{}x{}", level, j);
            let mut imps = vec![defs_module.to_string()];
            imps.extend(group.iter().map(|(_, m)| m.clone()));
            let mut content = file_prelude(&imps, "Generated certificate; see `certgen`.");
            writeln!(content, "namespace {}\n\nopen RACert RACert.Problem\n\nnamespace {}\n", cls_ns, sub_ns).unwrap();
            let part = combine(group, b, t, &mut content, "total");
            writeln!(content, "end {}\n\nend {}", sub_ns, cls_ns).unwrap();
            write_file(&ctx.path_of(&sub_module), &content);
            next.push((Part { name: format!("{}.total", sub_ns), ..part }, sub_module));
        }
        items = next;
        level += 1;
    }
    let part = combine(&items, b, t, out, name);
    (part, items.into_iter().map(|(_, m)| m).collect())
}

/// Write `theorem name : OrbitSeg t perms (P.leaf b) lo hi M W` combining consecutive parts.
fn combine(items: &[(Part, String)], b: &str, t: usize, out: &mut String, name: &str) -> Part {
    let lo = items[0].0.lo;
    let hi = items[items.len() - 1].0.hi;
    let m: u128 = items.iter().map(|x| x.0.m).sum();
    let w: u128 = items.iter().map(|x| x.0.w).sum();
    let mut proof = items[items.len() - 1].0.name.clone();
    for (p, _) in items[..items.len() - 1].iter().rev() {
        proof = format!("({}).append ({})", p.name, proof);
    }
    writeln!(
        out,
        "theorem {} : OrbitSeg {} perms (P.leaf {}) {} {} {} {} :=\n  OrbitSeg.cast ({})\n    (by decide +kernel) (by decide +kernel)\n",
        name, t, b, lo, hi, m, w, proof
    )
    .unwrap();
    Part { lo, hi, m, w, name: name.to_string() }
}

/// Emit the certificate of one class using the symmetry reduction. Returns the count.
fn emit_class_sym(ctx: &Ctx, sys: &Sys, i: usize, rep: &[usize], hs: &[Vec<usize>], bmax: usize) -> u128 {
    let (s, n) = (sys.s, sys.n);
    let (roots, b, m) = choose_low(sys, rep, hs, bmax);
    let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
    let p = Problem::new(sys, rep, &order);
    let tags = p.quad_tags(b, m);
    // blocks of the quadruples not depending on the eliminated variables, and for each
    // eliminated variable the quadruples depending on it
    let (qt, ow) = trees(&p, b, m, &tags);
    let mut flat: Vec<(usize, u64, u64)> = vec![];
    qt.entries(&mut flat);
    let grp = BitGroup::new(&p, b + m, hs);
    let t = grp.t;
    let t0 = std::time::Instant::now();
    let reps = all_reps(&p, b, m, &grp);
    let live: Vec<&Rep> = reps.iter().filter(|r| r.dead.is_none()).collect();
    // leaves of the live minima, in parallel
    let ev = crate::leaf::Evaluator::new(&p, b);
    let mut vals = vec![0u64; live.len()];
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(10);
    let chunk = live.len().div_ceil(nthreads).max(1);
    std::thread::scope(|sc| {
        for (ci, slice) in vals.chunks_mut(chunk).enumerate() {
            let (ev, live, tags) = (&ev, &live, &tags);
            sc.spawn(move || {
                let mut memo = crate::leaf::MemoEval::new(ev, if b >= 22 { 2000 << 20 } else { 600 << 20 });
                for (j, o) in slice.iter_mut().enumerate() {
                    *o = memo.leaf_elim(live[ci * chunk + j].alpha, m, tags);
                }
            });
        }
    });
    let mut val_of = std::collections::HashMap::new();
    for (r, v) in live.iter().zip(&vals) {
        val_of.insert(r.alpha, *v);
    }
    let total: u128 = reps.iter().map(|r| r.m as u128 * val_of.get(&r.alpha).cloned().unwrap_or(0) as u128).sum();
    println!(
        "  class {} rep {:?}: vars {} quads {} b {} eliminated {} t {} group {} minima {} live {} count {} ({:?})",
        i, rep, p.nvars, p.quads.len(), b, m, t, grp.perms.len(), reps.len(), live.len(), total, t0.elapsed()
    );
    let bs = format!("({} + {})", b, m);
    let cls_module = format!("{}.C{}", ctx.module, i);
    let cls_ns = format!("{}.C{}", ctx.namespace, i);
    let defs_module = format!("{}.Defs", cls_module);
    // definitions
    let doc = format!("Generated certificate (see `certgen`): symmetry class {} of type ({}, {}).", i, s, n);
    let mut d = file_prelude(&["Solution.Cert.SymOrbit".to_string(), "Solution.Cert.Elim".to_string()], &doc);
    writeln!(d, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
    d.push_str(&problem_def(&p));
    let syms: Vec<String> = grp.syms.iter().map(|x| format!("{{ h := {}, hi := {}, vp := {}, vq := {} }}", list(&x.h), list(&x.hi), list(&x.vp), list(&x.vq))).collect();
    writeln!(d, "/-- Symmetries of the problem, one for each element of `perms`. -/\ndef syms : List Sym :=\n  [{}]\n", syms.join(",\n   ")).unwrap();
    writeln!(d, "/-- The group of permutations of the high variables induced by the symmetries. -/\ndef perms : List (List ℕ × List ℕ) :=\n  {}\n", pairs(&grp.perms)).unwrap();
    let gens: Vec<String> = grp.gens().iter().map(|(g, r)| format!("({}, {})", g, list(r))).collect();
    writeln!(d, "/-- Generators of `perms` with their rows of the multiplication table. -/\ndef gens : List (ℕ × List ℕ) :=\n  [{}]\n", gens.join(",\n   ")).unwrap();
    writeln!(d, "/-- Inverses in `perms`. -/\ndef inv : List ℕ := {}\n", list(&grp.inv)).unwrap();
    writeln!(d, "/-- The quadruples not depending on the eliminated variables, as a tree with their classified\nsides and the masks of the high variables of the subtrees. -/\ndef qt : QTree :=\n  {}\n", qt.lean()).unwrap();
    let ow_s: Vec<String> = ow.iter().map(|t| t.lean()).collect();
    writeln!(d, "/-- For each eliminated variable, the quadruples depending on it. -/\ndef ow : List QTree :=\n  [{}]\n", ow_s.join(",\n   ")).unwrap();
    writeln!(d, "theorem elimOK : P.checkElim {} {} qt ow = true := by decide +kernel\n", b, m).unwrap();
    let flat_s: Vec<String> = flat.iter().map(|(x, m1, m2)| format!("({}, {}, {})", x, m1, m2)).collect();
    writeln!(d, "/-- The quadruples of `qt`; dead leaves refer to them by index. -/\ndef qmFlat : List (ℕ × ℕ × ℕ) :=\n  [{}]\n", flat_s.join(", ")).unwrap();
    writeln!(d, "theorem flatOK : P.checkFlat {} {} qmFlat = true := by decide +kernel\n", b, m).unwrap();
    writeln!(d, "theorem symsOK : P.checkSyms {} syms perms = true := by decide +kernel\n", bs).unwrap();
    writeln!(d, "theorem grpOK : checkBitGroup {} perms gens inv = true := by decide +kernel\n", t).unwrap();
    writeln!(d, "end {}", cls_ns).unwrap();
    write_file(&ctx.path_of(&defs_module), &d);
    // parts: runs of consecutive orbit minima with a bounded number of evaluated leaves, each
    // checked by two theorems; several parts per file
    let mut parts_reps: Vec<Vec<&Rep>> = vec![];
    let mut cur: Vec<&Rep> = vec![];
    let mut cur_live = 0;
    for r in &reps {
        if cur.len() >= PART_REPS || (cur_live >= seg_live(b, m) && r.dead.is_none()) {
            parts_reps.push(std::mem::take(&mut cur));
            cur_live = 0;
        }
        if r.dead.is_none() {
            cur_live += 1;
        }
        cur.push(r);
    }
    if !cur.is_empty() {
        parts_reps.push(cur);
    }
    let top: u64 = 1 << t;
    let quad_index: std::collections::HashMap<usize, usize> = flat.iter().enumerate().map(|(i, e)| (e.0, i)).collect();
    // files: consecutive parts, with one check of all their orbit minima (its set-up for a
    // large group is expensive, so it should not be repeated for every part)
    let mut files: Vec<Vec<Vec<&Rep>>> = vec![];
    let mut cur_file: Vec<Vec<&Rep>> = vec![];
    let mut cur_reps = 0;
    for part in parts_reps {
        if !cur_file.is_empty() && (cur_file.len() >= FILE_PARTS || cur_reps + part.len() > FILE_REPS) {
            files.push(std::mem::take(&mut cur_file));
            cur_reps = 0;
        }
        cur_reps += part.len();
        cur_file.push(part);
    }
    if !cur_file.is_empty() {
        files.push(cur_file);
    }
    let mut parts: Vec<(Part, String)> = vec![];
    for (j, file) in files.iter().enumerate() {
        let seg_module = format!("{}.S{}", cls_module, j);
        let seg_ns = format!("S{}", j);
        let mut c = file_prelude(&[defs_module.clone()], "Generated certificate segment; see `certgen`.");
        writeln!(c, "namespace {}\n\nopen RACert RACert.Problem\n\nnamespace {}\n", cls_ns, seg_ns).unwrap();
        let lo = if j == 0 { 0 } else { file[0][0].alpha };
        let hi = if j + 1 == files.len() { top } else { files[j + 1][0][0].alpha };
        let (mut om, mut w) = (0u128, 0u128);
        let mut sum_proof = String::new();
        let mut seg_expr = String::new();
        for (i, seg) in file.iter().enumerate().rev() {
            let proof = format!("sumEvE_sum check rows elimOK flatOK sumOK{}", i);
            sum_proof = if sum_proof.is_empty() { proof } else { format!("({}).append ({})", proof, sum_proof) };
            seg_expr = if seg_expr.is_empty() { format!("seg{}", i) } else { format!("seg{} ++ ({})", i, seg_expr) };
            let _ = seg;
        }
        for (i, seg) in file.iter().enumerate() {
            let wi: u128 = seg.iter().map(|r| r.m as u128 * val_of.get(&r.alpha).cloned().unwrap_or(0) as u128).sum();
            om += seg.iter().map(|r| r.m as u128).sum::<u128>();
            w += wi;
            let seg_s: Vec<String> = seg.iter().map(|r| format!("({}, {})", r.alpha, r.m)).collect();
            // evidence, without the trailing evaluated leaves
            let mut ev: Vec<usize> = seg.iter().map(|r| match r.dead { None => 0, Some(x) => quad_index[&x] + 1 }).collect();
            while ev.last() == Some(&0) {
                ev.pop();
            }
            writeln!(c, "/-- Orbit minima `(α, orbit size)`, part {}. -/\ndef seg{} : List (ℕ × ℕ) :=\n  [{}]\n", i, i, seg_s.join(", ")).unwrap();
            writeln!(c, "/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an\nevaluated leaf. -/\ndef ev{} : List ℕ := {}\n", i, list(&ev)).unwrap();
            writeln!(c, "theorem sumOK{} : P.sumEvE {} {} qt ow qmFlat seg{} ev{} 0 {} = true := by decide +kernel\n", i, b, m, i, i, wi).unwrap();
        }
        writeln!(c, "/-- All orbit minima of this file. -/\ndef seg : List (ℕ × ℕ) := {}\n", seg_expr).unwrap();
        writeln!(c, "theorem segOK : checkSeg {} perms {} {} seg = true := by decide +kernel\n", t, lo, hi).unwrap();
        writeln!(
            c,
            "theorem total : OrbitSeg {} perms (P.leaf {}) {} {} {} {} :=\n  OrbitSeg.of_checkSum segOK (by decide +kernel)\n    ({})\n    (by decide +kernel)\n",
            t, bs, lo, hi, om, w, sum_proof
        )
        .unwrap();
        writeln!(c, "end {}\n\nend {}", seg_ns, cls_ns).unwrap();
        write_file(&ctx.path_of(&seg_module), &c);
        parts.push((Part { lo, hi, m: om, w, name: format!("{}.total", seg_ns) }, seg_module));
    }
    let mut body = String::new();
    let (part, imports) = emit_parts(ctx, &cls_ns, &defs_module, &cls_module, &bs, t, parts, &mut body, "total");
    assert_eq!(part.m, top as u128, "orbit sizes do not add up");
    assert_eq!(part.w, total);
    writeln!(
        body,
        "/-- The number of lawful cycle sets invariant under the symmetry of this class. -/\ntheorem count : fixCountL {} {} {} = {} :=\n  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)\n    symsOK grpOK total\n",
        s, n, list(rep), total
    )
    .unwrap();
    let mut imps = vec![defs_module.clone()];
    imps.extend(imports);
    let mut content = file_prelude(&imps, &doc);
    writeln!(content, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
    content.push_str(&body);
    writeln!(content, "end {}", cls_ns).unwrap();
    write_file(&ctx.path_of(&cls_module), &content);
    total
}

/// Estimate the certificate size and checking time of the identity class for every choice of
/// `b` low variables (a union of orbits of variables) with `bmin <= b <= bmax`.
pub fn plan(s: usize, n: usize, bmin: usize, bmax: usize) {
    use crate::symm::*;
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    let rep = &cl.reps[0];
    let base = Problem::new(&sys, rep, &default_order);
    let orbits = var_orbits(&base, &g);
    let elim = choose_elim(&base, &orbits);
    let zs: Vec<usize> = elim.iter().flat_map(|&i| orbits[i].clone()).collect();
    let m = zs.len();
    let orbits: Vec<Vec<usize>> = orbits.into_iter().enumerate().filter(|(i, _)| !elim.contains(i)).map(|x| x.1).collect();
    let sizes: Vec<usize> = orbits.iter().map(|o| o.len()).collect();
    println!("({},{}) vars {} |G| {} eliminated {} remaining variable orbit sizes {:?}", s, n, base.nvars, g.len(), m, sizes);
    let no = orbits.len();
    let mut rows: Vec<(f64, String)> = vec![];
    let mut seen_sizes = std::collections::HashMap::new();
    for mask in 0u64..(1 << no) {
        let sz: usize = (0..no).filter(|i| mask >> i & 1 == 1).map(|i| sizes[i]).sum();
        if sz < bmin || sz > bmax || base.nvars - m - sz > 40 {
            continue;
        }
        // at most a few candidates per size
        let cnt = seen_sizes.entry(sz).or_insert(0usize);
        if *cnt >= 6 {
            continue;
        }
        *cnt += 1;
        let mut order: Vec<usize> = vec![];
        for (i, o) in orbits.iter().enumerate() { if mask >> i & 1 == 1 { order.extend(o); } }
        order.extend(&zs);
        for (i, o) in orbits.iter().enumerate() { if mask >> i & 1 == 0 { order.extend(o); } }
        let roots: Vec<usize> = order.into_iter().map(|j| base.reps[j]).collect();
        let ord = move |_p: &Problem, _r: Vec<usize>| roots.clone();
        let p = Problem::new(&sys, rep, &ord);
        let b = sz;
        let grp = BitGroup::new(&p, b + m, &g);
        let (reps_e, live_e) = sample_reps(&p, b, m, &grp);
        let (leaf, per_rep) = leaf_cost(&p, b, m);
        let est = live_e * leaf + reps_e * per_rep;
        rows.push((est, format!("  b {:>2} t {:>2} group {:>3}: minima ~{:.3e} live ~{:.3e} leaf {:.0} ms => ~{:.1} CPU-hours (mask {:#x})", b, grp.t, grp.perms.len(), reps_e, live_e, leaf * 1000.0, est / 3600.0, mask)));
    }
    rows.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    for (_, r) in rows.iter().take(12) {
        println!("{}", r);
    }
}

/// Simulate the kernel's sharing of work for the identity class: sample runs of consecutive
/// orbit minima, group their live leaves into theorems, and count the distinct big-number
/// operations and the evaluated tree nodes per leaf.
pub fn ops(s: usize, n: usize, bmax: usize, per_thm: usize) {
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    let rep = &cl.reps[0];
    let (roots, b, m) = choose_low(&sys, rep, &g, bmax);
    let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
    let p = Problem::new(&sys, rep, &order);
    let tags = p.quad_tags(b, m);
    let (qt, ow) = trees(&p, b, m, &tags);
    let grp = BitGroup::new(&p, b + m, &g);
    let tree = crate::tree::Tree::new_elim(&p, b, m);
    let terms: Vec<_> = p.quads.iter().map(|&x| p.quad_terms(x)).collect();
    let per = if per_thm == 0 { seg_live(b, m) } else { per_thm };
    let total: u64 = 1 << grp.t;
    let pieces = 16u64;
    let mut sim = crate::leaf::Sim::new(&terms, b);
    let (mut leaves, mut minima) = (0usize, 0usize);
    for i in 0..pieces {
        // a run of minima starting inside the i-th piece, enough for a few theorems
        let lo = (total / pieces) * i + (total / pieces / 3);
        let mut live: Vec<u64> = vec![];
        let mut hi = lo;
        while live.len() < 4 * per && hi < total {
            let step = 1u64 << 12;
            let reps = crate::symm::reps_in(&p, b + m, &grp, &tree, hi, (hi + step).min(total));
            minima += reps.len();
            live.extend(reps.iter().filter(|r| r.dead.is_none()).map(|r| r.alpha));
            hi += step;
        }
        for thm in live.chunks(per) {
            sim.reset();
            for &a in thm {
                sim.leaf(&qt, &ow, a);
                leaves += 1;
            }
        }
    }
    let f = |x: usize| x as f64 / leaves.max(1) as f64;
    let tot: usize = sim.cat.iter().sum();
    println!(
        "({},{}) b {} eliminated {} t {}: {} leaves per theorem; per leaf {:.0} big operations (residuals {:.0}, xor {:.0}, tree {:.0}, weights {:.0}, population counts {:.0}) and {:.0} evaluated nodes (sampled {} leaves, {} minima)",
        s, n, b, m, grp.t, per, f(tot), f(sim.cat[0]), f(sim.cat[1]), f(sim.cat[2]), f(sim.cat[3]), f(sim.cat[4]), f(sim.visits), leaves, minima
    );
}
