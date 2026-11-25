# certgen

Certificate generator for the counts of isomorphism classes of finite integral relation algebras
proved in `Solution/`.

```
cargo build --release
target/release/certgen gen <s> <n> <repo-root> [bmax]     # write Solution/Atoms<k>/S<s>N<n>/
target/release/certgen plan <s> <n> <bmin> <bmax>         # sampled estimate of certificate size and check time
```

`<s>` is the number of symmetric diversity atoms, `<n>` the number of pairs of nonsymmetric atoms,
`k = 1 + s + 2n`. `bmax` (default 20; the committed large certificates use 22) bounds the number `b` of variables
handled by one truth table, i.e. tables have `2^b` bits. The generator is deterministic; rerunning it reproduces the
committed files. After generating, `scripts/wire_headline.py <s> <n>` points the headline theorem
in `Solution/Atoms<k>/Symm<s>Nsymm<n>.lean` at the certificate.

## What is proved, and how

The Lean development (`Solution/Theory`, `Solution/Cert`) reduces
`(ofSymmNsymm s n).encard = N` to kernel computations in four steps.

1. **Classification** (`Solution/Theory`). Every finite integral relation algebra with `s`
   symmetric and `2n` nonsymmetric diversity atoms is the complex algebra of a *lawful cycle set*
   `T` on `IntegralAtom s n`, and two such algebras are isomorphic iff their cycle sets are
   related by an element of the group `Aut s n` of permutations of the atoms fixing the identity
   and commuting with converse. So the count is the number of orbits, and by Burnside's lemma
   `N * |Aut s n| = ∑ σ, #{T lawful | σ T = T}`.

2. **Group certificate** (`Solution/Cert/Group.lean`). The group is listed explicitly, each
   element with its conjugacy class and a conjugator; the checker `checkGroup` validates the
   list, so only one fixed-point count per conjugacy class is needed.

3. **Model counting** (`Solution/Cert/Problem.lean`). For a class representative `σ`, a
   `Problem` describes the lawful cycle sets fixed by `σ` as the models of a Boolean formula:
   the variables are the orbits of diversity triples under the Peircean transformations and
   `σ`, and the formula is the conjunction of the associativity conditions of one quadruple of
   atoms from each orbit under the dihedral symmetries of a quadruple and `σ`. The checker
   `Problem.check` validates the orbit data (`cls`, `reps`, `path`) and the reduction of
   quadruples (`quads`, `wit`); `Problem.fixCountL_eq` is the resulting bijection.

4. **Truth tables** (`Solution/Cert/Eval.lean`). The models are counted `2^b` at a time: the
   first `b` variables are represented by their truth-table columns, which are natural numbers
   with `2^b` bits, and the formula is evaluated with `Nat.land`, `Nat.lor`, `Nat.xor` — the
   operations the Lean kernel performs with GMP — followed by a verified SWAR population count
   (`Solution/Cert/Bits.lean`). A *leaf* `P.leaf b α` is the number of models whose remaining
   variables are given by the bits of `α`; constants are folded symbolically, so a leaf whose
   high variables already violate a condition costs almost nothing.

   For large problems (`Solution/Cert/Sym.lean`, `Orbit.lean`, `SymOrbit.lean`) the leaves are
   not all evaluated: the symmetries of the problem (the centraliser of `σ`) permute the high
   variables, leaves are constant on orbits, and only one leaf per orbit (its minimum, with the
   orbit size as weight) is needed. The certificate lists the orbit minima in segments; each
   segment is checked (`checkSeg`: minimality and orbit size of every listed assignment), and the
   total orbit size `2^t` proves that no orbit is missing. Minima whose high variables violate a
   condition are discharged in bulk (`checkEv`) rather than by a truth table.

5. **Sharing between leaves** (`Solution/Cert/Fast.lean`). The leaves of a segment are checked
   by a few theorems (`checkLeavesR`), each covering many leaves. The evaluator `leafR` is
   written so that the kernel sees *the same expression* whenever two leaves need the same
   table: each side of an associativity condition is a function of the quadruple and of the
   high variables it actually depends on (`dotRL P b x (α &&& mask)`), intermediate values are
   passed on in continuation-passing style in a canonical form, and violations are accumulated
   in blocks. The kernel caches the value of every expression within one declaration, so the
   leaves of a theorem share almost all of their big-number operations; what remains per leaf is
   essentially one population count (`Solution/Cert/Popcount.lean`: 14 big operations).

Every computational step is a `decide +kernel` proof of a closed Boolean or numeric equation, so
the only axioms are `propext`, `Quot.sound` and `Classical.choice`.

## Design notes for kernel reduction

* The kernel's cost for an operation on big literals is proportional to the size of the result
  (about 1 µs per KB: every intermediate value is retained until the end of the declaration), and
  about 1 µs per elementary reduction step otherwise. Truth tables of `2^18`–`2^20` bits give the
  best throughput; larger tables only use more memory.
* Hot loops are written directly with recursors (`List.rec`, `Nat.rec`, `Bool.rec`) and the raw
  `Nat.land`/`Nat.lor`/… functions; equation-compiler definitions and notation type classes cost
  several times more reduction steps.
* The kernel caches the weak head normal form of every expression it meets within a
  declaration. This is what limits the size of one theorem (memory), and it is also what makes
  the sharing of step 5 work: structurally equal expressions are evaluated once.
* Generated files set `Elab.async false` because asynchronous elaboration keeps the kernel's
  memory until the end of the file.
* Files are split so that `lake` checks them in parallel.
* Checking is dominated by memory traffic. Exporting
  `MALLOC_MMAP_THRESHOLD_=4294967296 MALLOC_TRIM_THRESHOLD_=4294967296 MALLOC_TOP_PAD_=1073741824`
  (as `scripts/safe-run.sh` does) lets GMP reuse heap memory instead of mapping every large
  block afresh and noticeably reduces the system time.
