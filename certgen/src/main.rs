//! Certificate generator for the counts of finite integral relation algebras.
//!
//! `certgen gen <s> <n> <repo-root> [bmax]` writes the Lean certificate files for the count of
//! isomorphism classes with `s` symmetric and `n` pairs of nonsymmetric diversity atoms.
//!
//! The count is obtained by Burnside's lemma: for one representative `sigma` of each conjugacy
//! class of the symmetry group of the atoms, we count the lawful cycle sets fixed by `sigma` as
//! models of a Boolean formula whose variables are the orbits of diversity triples under the
//! Peircean transformations and `sigma`. The model count is a sum of "leaves": for each
//! assignment `alpha` of the high variables, the number of assignments of the low `b` variables
//! satisfying the formula, which the Lean kernel recomputes with truth tables on big naturals.

mod leaf;
mod lean;
mod problem;
mod symm;
mod sys;
mod tree;

use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 4 && args[1] == "stats" {
        let s: usize = args[2].parse().unwrap();
        let n: usize = args[3].parse().unwrap();
        let bmax: usize = args.get(4).map(|x| x.parse().unwrap()).unwrap_or(20);
        let ord: usize = args.get(5).map(|x| x.parse().unwrap()).unwrap_or(0);
        lean::stats(s, n, bmax, ord);
        return;
    }
    if args.len() >= 4 && args[1] == "symplan" {
        let s: usize = args[2].parse().unwrap();
        let n: usize = args[3].parse().unwrap();
        let bmax: usize = args.get(4).map(|x| x.parse().unwrap()).unwrap_or(20);
        lean::symplan(s, n, bmax);
        return;
    }
    if args.len() >= 4 && args[1] == "symstats" {
        let s: usize = args[2].parse().unwrap();
        let n: usize = args[3].parse().unwrap();
        let bmax: usize = args.get(4).map(|x| x.parse().unwrap()).unwrap_or(20);
        lean::symstats(s, n, bmax);
        return;
    }
    if args.len() < 5 || args[1] != "gen" {
        eprintln!("usage: certgen gen <s> <n> <repo-root> [bmax]");
        std::process::exit(2);
    }
    let s: usize = args[2].parse().unwrap();
    let n: usize = args[3].parse().unwrap();
    let root = PathBuf::from(&args[4]);
    let bmax: usize = args.get(5).map(|x| x.parse().unwrap()).unwrap_or(20);
    lean::generate(s, n, &root, bmax);
}
