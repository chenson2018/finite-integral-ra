# certgen

Certificate generator for the counts of isomorphism classes of finite integral relation algebras
proved in `Solution/`.

```
cargo build --release
target/release/certgen gen <s> <n> <repo-root> [bmax]     # write Solution/Atoms<k>/S<s>N<n>/
target/release/certgen plan <s> <n> <bmin> <bmax>         # sampled estimate of certificate size and check time
target/release/certgen ops <s> <n> <bmax> [leaves]        # simulated sharing of big-number operations
```

`<s>` is the number of symmetric diversity atoms, `<n>` the number of pairs of nonsymmetric atoms,
`k = 1 + s + 2n`. `bmax` (default 22, the value used for all committed certificates) bounds the number `b` of
variables handled by one truth table, i.e. tables have `2^b` bits. The generator is deterministic; rerunning it reproduces the
committed files exactly, which `scripts/check-regen.sh` verifies for all types. After generating, `scripts/wire_headline.py <s> <n>` points the headline theorem
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
   (`Solution/Cert/Bits.lean`, `Popcount.lean`). A *leaf* `P.leaf b α` is the number of models
   whose remaining variables are given by the bits of `α`. Small problems are settled by a
   single leaf.

5. **Symmetry** (`Solution/Cert/Sym.lean`, `Orbit.lean`, `SymOrbit.lean`). For large problems
   the leaves are not all evaluated: the symmetries of the problem (the centraliser of `σ`)
   permute the high variables, leaves are constant on orbits, and only one leaf per orbit (its
   minimum, with the orbit size as weight) is needed. The certificate lists the orbit minima in
   files; the minima of a file are checked by one theorem (`checkSeg`: minimality and orbit size
   of every listed assignment), and the total orbit size `2^t` proves that no orbit is missing.
   Minima whose high variables already violate a condition are discharged without a truth table
   (`deadR`).

6. **Eliminated variables** (`Solution/Cert/Elim.lean`). Some variables never occur together in
   the condition of a quadruple — in practice the variables `a ≤ a ; a` of the symmetric atoms
   `a`. Given the other variables their conditions are independent, so the number of their
   admissible values is a product and they need not be dimensions of the truth tables:
   `leafE P b m qt ow α` computes `P.leaf (b + m) α` with tables of `2^b` bits. The conditions
   not depending on the `m` eliminated variables (`qt`) give the table of admissible assignments;
   for the `i`-th eliminated variable the conditions depending on it (`ow[i]`) are evaluated for
   both of its values, which gives the tables of positions where it is forced or free; the tables
   of the positions with exactly `j` free variables are maintained (`frL`, `stepE0`), and the
   leaf is `∑ j, 2^j * popcount (E j)`, computed by a merged SWAR population count
   (`Solution/Cert/WPop.lean`). `checkElim` validates the classification of the conditions; a
   condition whose two sides are the same pair of rows holds trivially and is dropped.

7. **Sharing between leaves** (`Solution/Cert/Elim.lean`, `Side.lean`). A file is divided into
   parts of a few dozen evaluated leaves; the weighted sum of the leaves of a part is checked by
   one theorem (`sumEvE`), and the evaluator is written so that the
   kernel, which caches the value of every expression within a declaration, evaluates each
   distinct table once:
   * each side of a condition is pre-classified (`Side`: terms guarded by high variables, and
     terms independent of them), so that evaluating it takes a few reduction steps;
   * the conditions form a binary tree (`QTree`), and every subtree is evaluated as a function of
     the high variables it depends on, given as a literal (`violO t (α &&& mask)`), so that its
     value is shared by all leaves agreeing on these variables;
   * tables are handed on as *expressions* (`Option ℕ`, `SVal`) which the kernel only evaluates
     as arguments of a big-number operation, where the result is cached under the expression;
     a table that is merely passed along is never recomputed.

Every computational step is a `decide +kernel` proof of a closed Boolean or numeric equation, so
the only axioms are `propext`, `Quot.sound` and `Classical.choice`.

## Design notes for kernel reduction

* The kernel's cost for an operation on big literals is proportional to the size of the result
  (about 0.4 µs per KB: the result is written to fresh memory,
  copied and hashed, and every intermediate value is retained until the end of the declaration),
  and several µs per reduction step of the surrounding bookkeeping, because every intermediate
  expression enters the kernel's caches. Both matter: truth tables of `2^20` bits fit into the
  processor caches together with their operands and give the best throughput.
* Hot loops are written directly with recursors (`List.rec`, `Nat.rec`, `Bool.rec`) and the raw
  `Nat.land`/`Nat.lor`/… functions; equation-compiler definitions and notation type classes cost
  several times more reduction steps.
* The kernel caches the weak head normal form of every expression it meets within a
  declaration, by syntactic equality. This limits the size of one theorem (memory), and it is
  what makes the sharing of step 7 work — provided the arguments of an expensive function always
  have the same syntactic form (`forceL` turns a computed number into a literal), and provided
  big values are consumed as arguments of an operation rather than returned in tail position,
  where the cache is not consulted.
* Generated files set `Elab.async false` because asynchronous elaboration keeps the kernel's
  memory until the end of the file.
* Files are split so that `lake` checks them in parallel. Checking is dominated by memory
  traffic, so the speed-up from many threads is limited (about 3–4 on a 12-thread laptop CPU).
  A file being checked needs up to 4 GB of memory, so a parallel build needs about that much per
  job (about 30 GB in total on 12 threads).

## Status

Checking times are wall-clock for `lake build Solution` on a 12-thread laptop CPU, from a state
where `Solution/Theory` and `Solution/Cert` are built.
Checking everything below together takes 97 minutes (18 CPU-hours).

| type `(s, n)` | atoms | count | certificate | check |
|---|---|---|---|---|
| (0,0) (1,0) (0,1) (2,0) | 1–3 | 1, 2, 3, 7 | one leaf per class | seconds |
| (1,1) (3,0) | 4 | 37, 65 | one leaf per class | seconds |
| (0,2) (2,1) (4,0) | 5 | 83, 1316, 3013 | one leaf per class | seconds |
| (1,2) (3,1) (5,0) | 6 | 47965, 988464, 3849920 | 6, 26, 29 leaves with 1, 3, 5 eliminated variables | seconds |
| (0,3) | 7 | 4492953 | 24432 orbit minima, 5571 leaves | about half a minute |
| (2,2) | 7 | 2186435732 | 277824 orbit minima, 65947 leaves, 2 eliminated variables | about 4 minutes |
| (4,1) | 7 | 50265788140 | 1446336 orbit minima, 218422 leaves, 4 eliminated variables | about 15 minutes |
| (6,0) | 7 | 292352449486 | 1540944 orbit minima, all evaluated, 6 eliminated variables | about 80 minutes |

This gives the totals for up to 7 atoms (`encard_ofAtoms_seven`: 344809166311). Not covered:
`(1,3)`, a type with 8 atoms. Its identity class has 63 variables, only
one of which can be eliminated; with tables of `2^20` bits this leaves 42 high variables, i.e.
about `10^11` orbits of assignments under its 48 symmetries, of which about `6 * 10^9` need a
truth table (`certgen plan 1 3 19 22`): some 26000 CPU-hours of kernel time and a certificate of
terabytes. This type needs a further idea.

`certgen plan <s> <n> <bmin> <bmax>` estimates the certificate size and the single-thread
kernel time of the identity class for the possible choices of low variables, and
`certgen ops <s> <n> <bmax> [leaves per theorem]` simulates the sharing of big-number operations.
