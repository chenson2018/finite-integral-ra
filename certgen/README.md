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
committed files exactly, which `scripts/check-regen.sh` verifies for all types. The headline theorem
in `Solution/Atoms<k>/Symm<s>Nsymm<n>.lean` imports `Solution.Atoms<k>.S<s>N<n>.Group` and is proved by
`RACert.S<s>N<n>.count`.

## What is proved, and how

The Lean development (`Solution/Theory`, `Solution/Cert`) reduces
`Nat.card (ofSymmNsymm s n) = N` to kernel computations as follows.

1. **Classification** (`Solution/Theory`). Every finite integral relation algebra with `s`
   symmetric and `2n` nonsymmetric diversity atoms is the complex algebra of a *lawful cycle set*
   `T` on `IntegralAtom (Fin s) (Fin n)`, and two such algebras are isomorphic iff their cycle
   sets are related by an element of the group `Aut s n` of permutations of the atoms fixing the
   identity and commuting with converse. So the count is the number of orbits, and by Burnside's
   lemma `N * |Aut s n| = ∑ σ, #{T lawful | σ T = T}`.

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
   When a class spans multiple files, its `Defs` module supplies the bit-matrix columns for
   the permutations and checks them once against `cols`. Each segment uses these columns.
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

7. **Sharing between leaves** (`Solution/Cert/Elim.lean`, `Side.lean`). The one-stage orbit
   certificates use `sumEvE` to check a weighted sum of leaves in each theorem. The evaluator
   lets the kernel cache each distinct table within a declaration:
   * each side of a condition is pre-classified (`Side`: terms guarded by high variables, and
     terms independent of them), so that evaluating it takes a few reduction steps;
   * the conditions form a binary tree (`QTree`), and every subtree is evaluated as a function of
     the high variables it depends on, given as a literal (`violO t (α &&& mask)`), so that its
     value is shared by all leaves agreeing on these variables;
   * tables are handed on as *expressions* (`Option ℕ`, `SVal`) which the kernel only evaluates
     as arguments of a big-number operation, where the result is cached under the expression;
     a table that is merely passed along is never recomputed.

8. **Hypergraph split** (`Solution/Cert/Split.lean`). In the identity class of (6,0), the 20
   triples of distinct diversity atoms form a 3-uniform hypergraph. The previous split fixed
   the 30 triples `aab` with `a ≠ b` first. Every such assignment extends to a model by
   including all distinct triples and all loops `aaa`, so no outer case could be pruned.
   Fixing the hypergraph first, up to atom permutation, gives 2,136 outer cases. If a set of four atoms
   contains no hyperedge, its three pairings can only have witnesses outside the set. If one pairing
   has a witness and another has none, every completion violates associativity. Already
   927 outer cases have such a contradiction. The other 1,209 hypergraphs each admit a
   completion with every repeated-atom triple present.

   Within each representative, fix the ten triples `aab` with repeated atom 5 or 6 and
   `b ≠ a`. Each side of an associativity equation is a disjunction of positive products.
   Setting the unknown bits to zero and to one bounds that side for every completion.
   The checker tests the supplied quadruples across all 1,024 middle assignments in parallel.
   It discards a branch when one side is definitely true and the other is definitely false.
   The surviving 182,563 branches use tables of `2^20` bits with six independent loop
   variables, in batches of up to 96 evaluated leaves per theorem. The previous split
   evaluated 1,540,944 branches of the same width. The class now occupies 147 segment files,
   down from 803. Only the outer cases carry orbit weights. Every middle assignment in a
   representative contributes once, even when the hypergraph has automorphisms.

The kernel checks the closed Boolean and numeric equations, including the pruning masks and
weighted sums. The final theorems use only `propext`, `Quot.sound` and `Classical.choice`.

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
  In a 12-job sample, a (6,0) segment with 160-leaf theorems and shared columns used about
  4 GiB at peak.
  The shared (6,0) definitions module used about 11 GiB while building.

## Status

Wall-clock times below are from one fresh run per type on a 6-core, 12-thread AMD Ryzen AI 5
PRO 340 with 86 GiB RAM and Lean 4.37.0-rc1. Types ran sequentially, and Lake checked modules within
each type in parallel. Both timing columns include process startup and cover all conjugacy classes.

* **Lean check** times `lake --no-cache build +Solution.Atoms<k>.Symm<s>Nsymm<n>` on the freshly
  generated sources. The project started with an empty build directory. External dependencies
  were cached, and the shared theory and checker were built once before timing the types.
* **certgen** times one release-mode `certgen gen <s> <n> <repo-root>` with the default
  `bmax = 22`, including writing the files. Building the release binary took 1.6 s
  before timing the types. Every generated directory matched the repository byte-for-byte.

| Type `(s, n)` | Atoms | Isomorphism classes | Identity-class certificate | Lean check | `certgen` |
|---|---:|---:|---|---:|---:|
| (0,0) | 1 | 1 | 1 leaf | 1.8 s | 0.8 ms |
| (1,0) | 2 | 2 | 1 leaf | 1.8 s | 0.6 ms |
| (0,1) | 3 | 3 | 1 leaf | 1.9 s | 0.6 ms |
| (2,0) | 3 | 7 | 1 leaf | 1.8 s | 1.0 ms |
| (1,1) | 4 | 37 | 1 leaf | 1.9 s | 0.7 ms |
| (3,0) | 4 | 65 | 1 leaf | 1.9 s | 1.5 ms |
| (0,2) | 5 | 83 | 1 leaf | 2.2 s | 2.4 ms |
| (2,1) | 5 | 1,316 | 1 leaf | 2.2 s | 2.5 ms |
| (4,0) | 5 | 3,013 | 1 leaf | 2.4 s | 12 ms |
| (1,2) | 6 | 47,965 | 6 orbit minima, 6 evaluated leaves, 1 eliminated variable | 4.3 s | 90 ms |
| (3,1) | 6 | 988,464 | 26 orbit minima, 26 evaluated leaves, 3 eliminated variables | 5.0 s | 151 ms |
| (5,0) | 6 | 3,849,920 | 34 orbit minima, 29 evaluated leaves, 5 eliminated variables | 10.0 s | 79 ms |
| (0,3) | 7 | 4,492,953 | 24,432 orbit minima, 5,571 evaluated leaves | 36.0 s | 1.1 s |
| (2,2) | 7 | 2,186,435,732 | 277,824 orbit minima, 65,947 evaluated leaves, 2 eliminated variables | 3 min 02 s | 35.3 s |
| (4,1) | 7 | 50,265,788,140 | 1,446,336 orbit minima, 218,422 evaluated leaves, 4 eliminated variables | 13 min 24 s | 54.7 s |
| (6,0) | 7 | 292,352,449,486 | 2,136 hypergraph orbits, 182,563 inner leaves, 6 eliminated variables | 6 min 28 s | 1 min 01 s |
| **All types** | | | | **24 min 07 s** | **2 min 33 s** |

The totals use unrounded per-type measurements. Building the shared Lean modules took
10.6 s. Checking the atom totals and the top-level `Solution` target took another
2.3 s, bringing the staged Lean build to **24 min 20 s**.

The four seven-atom types sum to 344,809,166,311 isomorphism classes (`card_ofAtoms_seven`).
The eight-atom type `(1,3)` has 63 variables in its identity class, only
one of which can be eliminated; with tables of `2^20` bits this leaves 42 high variables, i.e.
about `10^11` orbits of assignments under its 48 symmetries, of which about `6 * 10^9` need a
truth table (`certgen plan 1 3 19 22`): some 26000 CPU-hours of kernel time and a certificate of
terabytes. This type needs a further idea.

`certgen plan <s> <n> <bmin> <bmax>` estimates the certificate size and the single-thread
kernel time of the one-stage orbit method for different choices of low variables in the identity
class. `certgen ops <s> <n> <bmax> [leaves per theorem]` simulates the sharing of big-number
operations in that method.
