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
    s.push_str("set_option linter.style.longLine false\nset_option maxRecDepth 100000\n\n");
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

pub fn generate(s: usize, n: usize, root: &Path, bmax: usize) {
    let sys = Sys::new(s, n);
    let k = sys.k;
    let ctx = Ctx {
        root: root.to_path_buf(),
        module: format!("Solution.Atoms{}.S{}N{}", k, s, n),
        namespace: format!("RACert.S{}N{}", s, n),
    };
    let g = sys.group();
    let cl = classes(&g);
    println!("({},{}): k={} |G|={} classes={}", s, n, k, g.len(), cl.reps.len());
    let mut counts: Vec<u128> = vec![];
    for (i, rep) in cl.reps.iter().enumerate() {
        let p = Problem::new(&sys, rep, &default_order);
        let b = p.nvars.min(bmax);
        let t0 = std::time::Instant::now();
        let leaves = all_leaves(&p, b);
        let total: u128 = leaves.iter().map(|&x| x as u128).sum();
        println!("  class {} rep {:?}: vars {} quads {} b {} leaves {} count {} ({:?})", i, rep, p.nvars, p.quads.len(), b, leaves.len(), total, t0.elapsed());
        counts.push(total);
        let chunks: Vec<Chunk> = leaves.iter().enumerate().map(|(a, &v)| Chunk { lo: a as u64, cnt: 1, val: v as u128 }).collect();
        let cls_module = format!("{}.C{}", ctx.module, i);
        let cls_ns = format!("{}.C{}", ctx.namespace, i);
        let single = chunks.len() <= FANOUT;
        let defs_module = if single { cls_module.clone() } else { format!("{}.Defs", cls_module) };
        let mut defs = String::new();
        writeln!(defs, "namespace {}\n\nopen RACert RACert.Problem\n", cls_ns).unwrap();
        defs.push_str(&problem_def(&p));
        let mut body = String::new();
        let imports = emit_chunks(&ctx, &cls_ns, &defs_module, &cls_module, b, &chunks, &mut body, "total");
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
        let w: u64 = reps.iter().map(|r| r.m).sum();
        println!("  class {} vars {} |C| {} bit-group {} b {} t {}: reps {} live {} (weights ok: {}) est {:.0}s ({:?})", i, p.nvars, hs.len(), grp.perms.len(), b, grp.t, reps.len(), live, w == 1 << grp.t, estimate(&p, b, &grp, &reps), t0.elapsed());
    }
}
