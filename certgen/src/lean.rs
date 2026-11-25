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

/// Number of quadruples in whose condition each orbit (given by its root triple) occurs.
fn occurrences(sys: &Sys, sigma: &[usize], roots: &[usize]) -> Vec<usize> {
    let p = Problem::new(sys, sigma, &default_order);
    let mut occ = vec![0usize; roots.len()];
    for &x in &p.quads {
        let (l, r) = p.quad_terms(x);
        let mut seen = vec![false; roots.len()];
        for (i, j) in l.into_iter().chain(r) {
            for c in [i, j] {
                if c >= 2 {
                    seen[c - 2] = true;
                }
            }
        }
        for (v, s) in seen.iter().enumerate() {
            if *s {
                occ[v] += 1;
            }
        }
    }
    occ
}

/// Kind of a triple: number of distinct atoms, used to group variables.
fn kind(k: usize, conv: &[usize], x: usize) -> usize {
    let (a, b, c) = (x / k / k, x / k % k, x % k);
    let norm = |y: usize| y.min(conv[y]);
    let mut v = vec![norm(a), norm(b), norm(c)];
    v.sort();
    v.dedup();
    v.len()
}

pub fn stats(s: usize, n: usize, bmax: usize, ord: usize) {
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    let rep = &cl.reps[0];
    let base = Problem::new(&sys, rep, &default_order);
    let occ = occurrences(&sys, rep, &base.reps);
    let k = sys.k;
    let conv = sys.conv.clone();
    let order = move |_p: &Problem, roots: Vec<usize>| -> Vec<usize> {
        let mut idx: Vec<usize> = (0..roots.len()).collect();
        match ord {
            0 => {}
            1 => idx.sort_by_key(|&i| occ[i]),                       // most frequent last (= split first)
            2 => idx.sort_by_key(|&i| std::cmp::Reverse(occ[i])),    // most frequent first (= bottom)
            3 => idx.sort_by_key(|&i| kind(k, &conv, roots[i])),     // few distinct atoms at the bottom
            4 => idx.sort_by_key(|&i| std::cmp::Reverse(kind(k, &conv, roots[i]))), // many distinct atoms at the bottom
            _ => {}
        }
        idx.into_iter().map(|i| roots[i]).collect()
    };
    let p = Problem::new(&sys, rep, &order);
    let b = p.nvars.min(bmax);
    let t0 = std::time::Instant::now();
    let tree = crate::tree::Tree::new(&p, b);
    let blocks = tree.blocks();
    let leaves = blocks.iter().filter(|x| matches!(x, crate::tree::Block::Leaf { .. })).count();
    // distinct residual formulas among all assignments of the high variables
    {
        use std::collections::hash_map::DefaultHasher;
        use std::collections::HashSet;
        use std::hash::{Hash, Hasher};
        let t = p.nvars - b;
        let mut set: HashSet<u64> = HashSet::new();
        let mut live = 0u64;
        for alpha in 0..(1u64 << t) {
            if let Some(r) = crate::tree::residual(&tree, alpha) {
                live += 1;
                let mut h = DefaultHasher::new();
                r.hash(&mut h);
                set.insert(h.finish());
            }
        }
        println!("  high assignments {} live {} distinct residuals {}", 1u64 << t, live, set.len());
    }
    println!("({},{}) ord {} vars {} b {}: blocks {} leaves {} of {} ({:?})", s, n, ord, p.nvars, b, blocks.len(), leaves, 1u64 << (p.nvars - b), t0.elapsed());
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

/// Statistics for the symmetry-reduced search of the identity class: the low variables are a
/// union of orbits of variables under the symmetry group, of total size at most `bmax`.
pub fn symstats(s: usize, n: usize, bmax: usize) {
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    let rep = &cl.reps[0];
    let k = sys.k;
    let base = Problem::new(&sys, rep, &default_order);
    let v = base.nvars;
    // induced permutations of variables
    let var_perm = |p: &Problem, h: &[usize]| -> Vec<usize> {
        (0..p.nvars)
            .map(|j| {
                let x = p.reps[j];
                let (a, b, c) = (x / k / k, x / k % k, x % k);
                p.cls[p.tcode(h[a], h[b], h[c])] - 2
            })
            .collect()
    };
    // orbits of variables
    let mut orb = vec![usize::MAX; v];
    let mut orbits: Vec<Vec<usize>> = vec![];
    let perms: Vec<Vec<usize>> = g.iter().map(|h| var_perm(&base, h)).collect();
    for j in 0..v {
        if orb[j] != usize::MAX { continue; }
        let mut o: Vec<usize> = perms.iter().map(|p| p[j]).collect();
        o.sort();
        o.dedup();
        for &x in &o { orb[x] = orbits.len(); }
        orbits.push(o);
    }
    let occ = occurrences(&sys, rep, &base.reps);
    let mut info: Vec<(usize, usize, usize)> = orbits.iter().enumerate().map(|(i, o)| (i, o.len(), occ[o[0]])).collect();
    println!("({},{}) vars {} |G| {} variable orbits (size, occurrences): {:?}", s, n, v, g.len(), info.iter().map(|x| (x.1, x.2)).collect::<Vec<_>>());
    // choose low orbits: fewest occurrences first, greedily while fitting
    info.sort_by_key(|x| (x.2, x.1));
    let mut low: Vec<usize> = vec![];
    let mut b = 0;
    for &(i, sz, _) in &info {
        if b + sz <= bmax { low.push(i); b += sz; }
    }
    let low_set: std::collections::HashSet<usize> = low.iter().cloned().collect();
    let mut order_idx: Vec<usize> = vec![];
    for (i, o) in orbits.iter().enumerate() { if low_set.contains(&i) { order_idx.extend(o); } }
    for (i, o) in orbits.iter().enumerate() { if !low_set.contains(&i) { order_idx.extend(o); } }
    let roots: Vec<usize> = order_idx.iter().map(|&j| base.reps[j]).collect();
    let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
    let p = Problem::new(&sys, rep, &order);
    let t = v - b;
    let perms: Vec<Vec<usize>> = g.iter().map(|h| var_perm(&p, h)).collect();
    let tree = crate::tree::Tree::new(&p, b);
    let act = |pm: &Vec<usize>, alpha: u64| -> u64 {
        let mut r = 0u64;
        for i in 0..t { if (alpha >> i) & 1 == 1 { r |= 1 << (pm[b + i] - b); } }
        r
    };
    let (mut canon, mut live, mut total_w) = (0u64, 0u64, 0u64);
    for alpha in 0..(1u64 << t) {
        let mut is_min = true;
        let mut imgs: Vec<u64> = Vec::with_capacity(perms.len());
        for pm in &perms {
            let a2 = act(pm, alpha);
            if a2 < alpha { is_min = false; break; }
            imgs.push(a2);
        }
        if !is_min { continue; }
        canon += 1;
        imgs.sort();
        imgs.dedup();
        total_w += imgs.len() as u64;
        let mut assign = vec![2u8; v];
        for i in 0..t { assign[b + i] = ((alpha >> i) & 1) as u8; }
        if tree.dead(&assign).is_none() { live += 1; }
    }
    println!("  b {} t {}: high assignments {} canonical {} live canonical {} (weights sum {})", b, t, 1u64 << t, canon, live, total_w);
}

/// Summary of the symmetry-reduced search for every class.
pub fn symplan(s: usize, n: usize, bmax: usize) {
    use crate::symm::*;
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    for (i, rep) in cl.reps.iter().enumerate() {
        let hs = centralizer(&g, rep);
        let (roots, b) = choose_low(&sys, rep, &hs, bmax);
        let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
        let p = Problem::new(&sys, rep, &order);
        let grp = BitGroup::new(&p, b, &hs);
        let t0 = std::time::Instant::now();
        let reps = all_reps(&p, b, &grp);
        let live = reps.iter().filter(|r| r.dead.is_none()).count();
        {
            let ev = crate::leaf::Evaluator::new(&p, b);
            let mut tot = (0usize, 0usize, 0usize, 0usize, 0usize);
            let mut cnt = 0usize;
            for r in reps.iter().filter(|r| r.dead.is_none()).step_by((live / 2000).max(1)) {
                let c = crate::leaf::op_counts(&ev, r.alpha);
                tot = (tot.0 + c.0, tot.1 + c.1, tot.2 + c.2, tot.3 + c.3, tot.4 + c.4);
                cnt += 1;
            }
            if cnt > 0 {
                println!("    avg per live leaf: ands {} ors {} xors {} bad-ors {} equal-sides {}", tot.0 / cnt, tot.1 / cnt, tot.2 / cnt, tot.3 / cnt, tot.4 / cnt);
            }
            // sharing of canonical operations among groups of consecutive live minima
            let lives: Vec<u64> = reps.iter().filter(|r| r.dead.is_none()).map(|r| r.alpha).collect();
            for g in [1usize, 2, 4, 8, 16, 32, 64] {
                let mut total = 0usize;
                let mut leaves = 0usize;
                for grp in lives.chunks(g).step_by((lives.len() / g / 500).max(1)) {
                    let mut keys = std::collections::HashSet::new();
                    for &a in grp {
                        total += crate::leaf::op_keys(&ev, a, &mut keys);
                        leaves += 1;
                    }
                }
                if leaves > 0 {
                    println!("    group size {:>2}: {:.0} distinct canonical ops per leaf", g, total as f64 / leaves as f64);
                }
            }
        }
        let w: u64 = reps.iter().map(|r| r.m).sum();
        println!("  class {} vars {} |C| {} bit-group {} b {} t {}: reps {} live {} (weights ok: {}) est {:.0}s ({:?})", i, p.nvars, hs.len(), grp.perms.len(), b, grp.t, reps.len(), live, w == 1 << grp.t, estimate(&p, b, &grp, &reps), t0.elapsed());
    }
}

// ---------------------------------------------------------------------------------------------
// Symmetry-reduced certificates
// ---------------------------------------------------------------------------------------------

use crate::symm::{all_reps, centralizer, choose_low, BitGroup, Rep};

/// Maximal number of orbit minima in one segment file.
const SEG_REPS: usize = 1500;

/// Maximal number of leaf-checking theorems in one segment file.
const SEG_CHUNKS: usize = 12;

/// Maximal number of evaluated leaves in one segment: the big-number results of one declaration
/// are all retained by the kernel, about 55 per leaf, and should stay around one gigabyte.
fn seg_live(b: usize) -> usize {
    let per_leaf = 55.0 * (1u64 << b) as f64 / 8.0;
    ((1.2e9 / per_leaf) as usize).clamp(4, 256)
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
fn emit_parts(ctx: &Ctx, cls_ns: &str, defs_module: &str, module: &str, b: usize, t: usize, parts: Vec<(Part, String)>, out: &mut String, name: &str) -> (Part, Vec<String>) {
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
fn combine(items: &[(Part, String)], b: usize, t: usize, out: &mut String, name: &str) -> Part {
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
    let (roots, b) = choose_low(sys, rep, hs, bmax);
    let order = move |_p: &Problem, _r: Vec<usize>| roots.clone();
    let mut p = Problem::new(sys, rep, &order);
    let block: usize = std::env::var("CERTGEN_BLOCK").ok().and_then(|x| x.parse().ok()).unwrap_or(8);
    let qm = p.order_quads(b, block);
    let grp = BitGroup::new(&p, b, hs);
    let t = grp.t;
    let t0 = std::time::Instant::now();
    let reps = all_reps(&p, b, &grp);
    let live: Vec<&Rep> = reps.iter().filter(|r| r.dead.is_none()).collect();
    // leaves of the live minima, in parallel
    let ev = crate::leaf::Evaluator::new(&p, b);
    let mut vals = vec![0u64; live.len()];
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(10);
    let chunk = live.len().div_ceil(nthreads).max(1);
    std::thread::scope(|sc| {
        for (ci, slice) in vals.chunks_mut(chunk).enumerate() {
            let (ev, live) = (&ev, &live);
            sc.spawn(move || {
                let mut memo = crate::leaf::MemoEval::new(ev, if b >= 22 { 2000 << 20 } else { 600 << 20 });
                for (j, o) in slice.iter_mut().enumerate() {
                    *o = memo.leaf(live[ci * chunk + j].alpha);
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
        "  class {} rep {:?}: vars {} quads {} b {} t {} group {} minima {} live {} count {} ({:?})",
        i, rep, p.nvars, p.quads.len(), b, t, grp.perms.len(), reps.len(), live.len(), total, t0.elapsed()
    );
    {
        // sharing statistics: distinct big-number operations per leaf within a checking theorem
        let masks: Vec<(u64, u64)> = p.quads.iter().map(|&x| p.quad_masks(x, b)).collect();
        let index: std::collections::HashMap<usize, usize> = p.quads.iter().enumerate().map(|(i, &x)| (x, i)).collect();
        let blocks: Vec<Vec<usize>> = qm.iter().map(|blk| blk.iter().map(|e| index[&e.0]).collect()).collect();
        let g = seg_live(b);
        let (mut ops, mut n) = (0usize, 0usize);
        let mut cat = [0usize; 6];
        for grp in live.chunks(g).step_by((live.len() / g / 200).max(1)) {
            let mut keys = std::collections::HashSet::new();
            for r in grp {
                ops += crate::leaf::op_keys_memo(&ev, &masks, &blocks, r.alpha, &mut keys, &mut cat);
                n += 1;
            }
        }
        if n > 0 {
            let f = |x: usize| x as f64 / n as f64;
            println!(
                "    {} leaves per theorem, about {:.1} big operations per leaf besides the population count (and {:.1}, or {:.1}, xor {:.1}, block {:.1}, chain {:.1})",
                g, f(ops), f(cat[1]), f(cat[2]), f(cat[3]), f(cat[4]), f(cat[5])
            );
        }
    }
    let cls_module = format!("{}.C{}", ctx.module, i);
    let cls_ns = format!("{}.C{}", ctx.namespace, i);
    let defs_module = format!("{}.Defs", cls_module);
    // definitions
    let doc = format!("Generated certificate (see `certgen`): symmetry class {} of type ({}, {}).", i, s, n);
    let mut d = file_prelude(&["Solution.Cert.SymOrbit".to_string(), "Solution.Cert.Fast".to_string()], &doc);
    writeln!(d, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
    d.push_str(&problem_def(&p));
    let syms: Vec<String> = grp.syms.iter().map(|x| format!("{{ h := {}, hi := {}, vp := {}, vq := {} }}", list(&x.h), list(&x.hi), list(&x.vp), list(&x.vq))).collect();
    writeln!(d, "/-- Symmetries of the problem, one for each element of `perms`. -/\ndef syms : List Sym :=\n  [{}]\n", syms.join(",\n   ")).unwrap();
    writeln!(d, "/-- The group of permutations of the high variables induced by the symmetries. -/\ndef perms : List (List ℕ × List ℕ) :=\n  {}\n", pairs(&grp.perms)).unwrap();
    let gens: Vec<String> = grp.gens().iter().map(|(g, r)| format!("({}, {})", g, list(r))).collect();
    writeln!(d, "/-- Generators of `perms` with their rows of the multiplication table. -/\ndef gens : List (ℕ × List ℕ) :=\n  [{}]\n", gens.join(",\n   ")).unwrap();
    writeln!(d, "/-- Inverses in `perms`. -/\ndef inv : List ℕ := {}\n", list(&grp.inv)).unwrap();
    let qm_s: Vec<String> = qm.iter().map(|blk| format!("[{}]", blk.iter().map(|(x, m1, m2)| format!("({}, {}, {})", x, m1, m2)).collect::<Vec<_>>().join(", "))).collect();
    writeln!(d, "/-- The quadruples in blocks, with the masks of the high variables of their two sides. -/\ndef qm : List (List (ℕ × ℕ × ℕ)) :=\n  [{}]\n", qm_s.join(",\n   ")).unwrap();
    writeln!(d, "theorem qmOK : P.checkQM {} qm = true := by decide +kernel\n", b).unwrap();
    writeln!(d, "theorem symsOK : P.checkSyms {} syms perms = true := by decide +kernel\n", b).unwrap();
    writeln!(d, "theorem grpOK : checkBitGroup {} perms gens inv = true := by decide +kernel\n", t).unwrap();
    writeln!(d, "end {}", cls_ns).unwrap();
    write_file(&ctx.path_of(&defs_module), &d);
    // segments
    let mut segs: Vec<Vec<&Rep>> = vec![];
    let mut cur: Vec<&Rep> = vec![];
    let mut cur_live = 0;
    for r in &reps {
        if cur.len() >= SEG_REPS || (cur_live >= SEG_CHUNKS * seg_live(b) && r.dead.is_none()) {
            segs.push(std::mem::take(&mut cur));
            cur_live = 0;
        }
        if r.dead.is_none() {
            cur_live += 1;
        }
        cur.push(r);
    }
    if !cur.is_empty() {
        segs.push(cur);
    }
    let top: u64 = 1 << t;
    let mut parts: Vec<(Part, String)> = vec![];
    for (j, seg) in segs.iter().enumerate() {
        let lo = if j == 0 { 0 } else { seg[0].alpha };
        let hi = if j + 1 == segs.len() { top } else { segs[j + 1][0].alpha };
        let m: u128 = seg.iter().map(|r| r.m as u128).sum();
        let w: u128 = seg.iter().map(|r| r.m as u128 * val_of.get(&r.alpha).cloned().unwrap_or(0) as u128).sum();
        let seg_module = format!("{}.S{}", cls_module, j);
        let seg_ns = format!("S{}", j);
        let mut c = file_prelude(&[defs_module.clone()], "Generated certificate segment; see `certgen`.");
        writeln!(c, "namespace {}\n\nopen RACert RACert.Problem\n\nnamespace {}\n", cls_ns, seg_ns).unwrap();
        let seg_s: Vec<String> = seg.iter().map(|r| format!("({}, {})", r.alpha, r.m)).collect();
        let ev_s: Vec<String> = seg.iter().map(|r| match r.dead { None => "0".to_string(), Some(x) => format!("{}", x + 1) }).collect();
        let live_s: Vec<String> = seg.iter().filter(|r| r.dead.is_none()).map(|r| format!("({}, {})", r.alpha, val_of[&r.alpha])).collect();
        writeln!(c, "/-- Orbit minima `(α, orbit size)` in this segment. -/\ndef seg : List (ℕ × ℕ) :=\n  [{}]\n", seg_s.join(", ")).unwrap();
        writeln!(c, "/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/\ndef ev : List ℕ :=\n  [{}]\n", ev_s.join(", ")).unwrap();
        // the evaluated leaves, in chunks checked by one theorem each (the kernel shares the
        // tables within a theorem and releases them afterwards)
        let mut lp = String::from(".nil");
        let mut names: Vec<String> = vec![];
        let nchunks = live_s.chunks(seg_live(b)).count();
        for (ci, chunk) in live_s.chunks(seg_live(b)).enumerate().collect::<Vec<_>>().into_iter().rev() {
            lp = format!(".append (checkLeavesR_spec rows qmOK leavesOK{}) ({})", ci, lp);
            let _ = chunk;
        }
        for (ci, chunk) in live_s.chunks(seg_live(b)).enumerate() {
            writeln!(c, "/-- Evaluated leaves `(α, value)`, part {}. -/\ndef live{} : List (ℕ × ℕ) :=\n  [{}]\n", ci, ci, chunk.join(", ")).unwrap();
            writeln!(c, "theorem leavesOK{} : P.checkLeavesR {} qm live{} = true := by decide +kernel\n", ci, b, ci).unwrap();
            names.push(format!("live{}", ci));
        }
        let _ = nchunks;
        let mut live_expr = String::from("[]");
        for nm in names.iter().rev() {
            live_expr = format!("{} ++ ({})", nm, live_expr);
        }
        writeln!(c, "/-- All evaluated leaves of this segment. -/\ndef live : List (ℕ × ℕ) := {}\n", live_expr).unwrap();
        writeln!(c, "theorem segOK : checkSeg {} perms {} {} seg = true := by decide +kernel\n", t, lo, hi).unwrap();
        writeln!(c, "theorem evOK : P.checkEv {} seg ev live 0 {} = true := by decide +kernel\n", b, w).unwrap();
        writeln!(
            c,
            "theorem total : OrbitSeg {} perms (P.leaf {}) {} {} {} {} :=\n  OrbitSeg.of_check segOK (by decide +kernel)\n    (checkEv_sum check rows evOK ({}))\n",
            t, b, lo, hi, m, w, lp
        )
        .unwrap();
        writeln!(c, "end {}\n\nend {}", seg_ns, cls_ns).unwrap();
        write_file(&ctx.path_of(&seg_module), &c);
        parts.push((Part { lo, hi, m, w, name: format!("{}.total", seg_ns) }, seg_module));
    }
    let mut body = String::new();
    let (part, imports) = emit_parts(ctx, &cls_ns, &defs_module, &cls_module, b, t, parts, &mut body, "total");
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

/// Statistics on the quadruples of the identity class: how many have literally equal sides.
pub fn quadstats(s: usize, n: usize) {
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    let p = Problem::new(&sys, &cl.reps[0], &default_order);
    let mut triv_rows = 0;
    let mut triv_terms = 0;
    let mut pairs_all = std::collections::HashSet::new();
    let mut pairs_canon = std::collections::HashSet::new();
    let mut nterms = 0;
    for &x in &p.quads {
        let (l, r) = p.quad_terms(x);
        let norm = |v: &Vec<(usize, usize)>| {
            let mut w: Vec<(usize, usize)> = v.iter().filter(|t| t.0 != 0 && t.1 != 0).map(|&(a, b)| (a.min(b), a.max(b))).collect();
            w.sort();
            w.dedup();
            w
        };
        if norm(&l) == norm(&r) {
            triv_terms += 1;
        }
        let k = p.k;
        let (rr, u, t, pp) = (x / k / k / k, x / k / k % k, x / k % k, x % k);
        let row = |a: usize, b: usize| -> Vec<usize> { (0..k).map(|q| p.cls[p.tcode(a, b, q)]).collect() };
        let (a1, a2, b1, b2) = (row(p.conv[rr], pp), row(u, t), row(rr, u), row(pp, p.conv[t]));
        if (a1 == b1 && a2 == b2) || (a1 == b2 && a2 == b1) {
            triv_rows += 1;
        }
        for (a, b) in l.iter().chain(r.iter()) {
            if *a >= 2 && *b >= 2 {
                nterms += 1;
                pairs_all.insert((*a, *b));
                pairs_canon.insert((*a.min(b), *a.max(b)));
            }
        }
    }
    println!("({},{}): quads {} trivial(rows) {} trivial(terms) {}; variable-variable terms {} distinct ordered {} unordered {}", s, n, p.quads.len(), triv_rows, triv_terms, nterms, pairs_all.len(), pairs_canon.len());
}

/// Cheap plan for the identity class: for every admissible split into low and high variables,
/// estimate (by sampling) the numbers of orbit minima and of live leaves.
pub fn plan(s: usize, n: usize, bmin: usize, bmax: usize) {
    use crate::symm::*;
    let sys = Sys::new(s, n);
    let g = sys.group();
    let cl = classes(&g);
    let rep = &cl.reps[0];
    let base = Problem::new(&sys, rep, &default_order);
    let orbits = var_orbits(&base, &g);
    let sizes: Vec<usize> = orbits.iter().map(|o| o.len()).collect();
    println!("({},{}) vars {} |G| {} variable orbit sizes {:?}", s, n, base.nvars, g.len(), sizes);
    let no = orbits.len();
    let mut rows: Vec<(f64, String)> = vec![];
    let mut seen_sizes = std::collections::HashMap::new();
    for mask in 0u64..(1 << no) {
        let sz: usize = (0..no).filter(|i| mask >> i & 1 == 1).map(|i| sizes[i]).sum();
        if sz < bmin || sz > bmax {
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
        for (i, o) in orbits.iter().enumerate() { if mask >> i & 1 == 0 { order.extend(o); } }
        let roots: Vec<usize> = order.into_iter().map(|j| base.reps[j]).collect();
        let ord = move |_p: &Problem, _r: Vec<usize>| roots.clone();
        let p = Problem::new(&sys, rep, &ord);
        let b = sz;
        let grp = BitGroup::new(&p, b, &g);
        let tree = crate::tree::Tree::new(&p, b);
        let samples = 1u64 << 17;
        let mut x: u64 = 0x9E3779B97F4A7C15;
        let (mut canon, mut live) = (0u64, 0u64);
        let mut assign = vec![2u8; p.nvars];
        for _ in 0..samples {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let alpha = (x >> 20) & ((1u64 << grp.t) - 1);
            if (0..grp.perms.len()).any(|i| grp.act(i, alpha) < alpha) { continue; }
            canon += 1;
            for i in 0..grp.t { assign[b + i] = ((alpha >> i) & 1) as u8; }
            if tree.dead(&assign).is_none() { live += 1; }
        }
        let scale = (2f64).powi(grp.t as i32) / samples as f64;
        let (reps_e, live_e) = (canon as f64 * scale, live as f64 * scale);
        let leaf = 0.004 + p.quads.len() as f64 * 25e-6 + 50.0 * 127e-6 * (2f64).powi(b as i32 - 20);
        let est = live_e * leaf + reps_e * 0.0012;
        rows.push((est, format!("  b {:>2} t {:>2} group {:>3}: minima ~{:.3e} live ~{:.3e} leaf {:.0} ms => ~{:.1} CPU-hours (mask {:#x})", b, grp.t, grp.perms.len(), reps_e, live_e, leaf * 1000.0, est / 3600.0, mask)));
    }
    rows.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    for (_, r) in rows.iter().take(12) {
        println!("{}", r);
    }
}
