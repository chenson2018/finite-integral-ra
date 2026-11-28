/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S34

open RACert RACert.Problem

theorem cover16371 : P.CoversSplit 26 10 16371 0xf000f000f000f000f000f000f000f0000000000000000000000000000000000000000a0000000a0000000a0000000a000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000200020000000000000000000000000000000000000000000000002000000000000000200 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1315, 1658]) (ps := [(13, [923], [972])]) (by decide +kernel)

theorem c16371_0 : P.sumLeaves 26 16763904 1024 = 33682912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16371) (lo := 0) (len := 1024) (W := 33682912) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem h16371 : P.leaf 36 16371 = 33682912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33682912)]) (.cons c16371_0 (.nil)) (by decide) (by decide))

theorem cover109051 : P.CoversSplit 26 10 109051 0xaaaaaaaa00000000aaaaabab0000000000000000000000000000000000000022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 881, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f109051 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (111668224 + i)

theorem c109051_0 : rowSum f109051 0 1024 = 95261260 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 109051) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover109051 (by decide)
  decide +kernel

theorem sum109051 : rowSum f109051 0 1024 = 95261260 :=
  c109051_0

theorem h109051 : P.leaf 36 109051 = 95261260 :=
  leaf_weighted (k := 26) (d := 10) (H := 109051) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 109051) (by decide) (by decide +kernel)) sum109051

theorem h16374 : P.leaf 36 16374 = 95261260 :=
  orient84 (v := 109051) (by decide) (by decide +kernel) h109051

theorem cover109055 : P.CoversSplit 26 10 109055 0xffffffff00000000fffffefe0000000000000000000000000000000000000022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 881, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f109055 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (111672320 + i)

theorem c109055_0 : rowSum f109055 0 1024 = 278654000 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 109055) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover109055 (by decide)
  decide +kernel

theorem sum109055 : rowSum f109055 0 1024 = 278654000 :=
  c109055_0

theorem h109055 : P.leaf 36 109055 = 278654000 :=
  leaf_weighted (k := 26) (d := 10) (H := 109055) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 109055) (by decide) (by decide +kernel)) sum109055

theorem h16375 : P.leaf 36 16375 = 278654000 :=
  orient84 (v := 109055) (by decide) (by decide +kernel) h109055

theorem cover40946 : P.CoversSplit 26 10 40946 0xf000f500f030f000000000000000000000000000000000000000000000000000f000f000f030f000000000000000000000000000000000000000000000000000f000f500f000f000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 922, 923, 929, 930, 1315, 1322]) (by decide +kernel)

noncomputable def f40946 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (41928704 + i)

theorem c40946_0 : rowSum f40946 0 1024 = 19145716 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40946) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40946 (by decide)
  decide +kernel

theorem sum40946 : rowSum f40946 0 1024 = 19145716 :=
  c40946_0

theorem h40946 : P.leaf 36 40946 = 19145716 :=
  leaf_weighted (k := 26) (d := 10) (H := 40946) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 40946) (by decide) (by decide +kernel)) sum40946

theorem h16376 : P.leaf 36 16376 = 19145716 :=
  orient6 (v := 40946) (by decide) (by decide +kernel) h40946

theorem cover40947 : P.CoversSplit 26 10 40947 0xf000f500f030f000000000000000000000000000000000000000000000000000f000f000f030f000000000000000000000000000000000000000000000000000f000f500f000f000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 922, 923, 929, 930, 1315, 1322]) (by decide +kernel)

noncomputable def f40947 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (41929728 + i)

theorem c40947_0 : rowSum f40947 0 1024 = 109945815 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40947) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40947 (by decide)
  decide +kernel

theorem sum40947 : rowSum f40947 0 1024 = 109945815 :=
  c40947_0

theorem h40947 : P.leaf 36 40947 = 109945815 :=
  leaf_weighted (k := 26) (d := 10) (H := 40947) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 40947) (by decide) (by decide +kernel)) sum40947

theorem h16377 : P.leaf 36 16377 = 109945815 :=
  orient6 (v := 40947) (by decide) (by decide +kernel) h40947

theorem cover40950 : P.CoversSplit 26 10 40950 0xff00ff00ff33fa00000000000000000000000000330032000000000000000000ff00fa00ff33fa00000000000000000000000000330032000000000000000000ff00ff00ff00fa00000000000000000000000000000000000000000000000000ff00fa00ff00fa00000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 922, 923, 930, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c40950_0 : P.sumLeaves 26 41932800 767 = 96044419 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 40950) (lo := 0) (len := 767) (W := 96044419) check rows elimOK (by decide) (by decide) cover40950 (by decide)
  decide +kernel

theorem c40950_1 : P.sumLeaves 26 41933567 257 = 70098392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 40950) (lo := 767) (len := 257) (W := 70098392) check rows elimOK (by decide) (by decide) cover40950 (by decide)
  decide +kernel

theorem h40950 : P.leaf 36 40950 = 166142811 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(767, 96044419), (257, 70098392)]) (.cons c40950_0 (.cons c40950_1 (.nil))) (by decide) (by decide))

theorem h16378 : P.leaf 36 16378 = 166142811 :=
  orient6 (v := 40950) (by decide) (by decide +kernel) h40950

theorem cover40951 : P.CoversSplit 26 10 40951 0xff00ff00ff33fa00000000000000000000000000330032000000000000000000ff00fa00ff33fa00000000000000000000000000330032000000000000000000ff00ff00ff00fa00000000000000000000000000000000000000000000000000ff00fa00ff00fa00000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 922, 923, 930, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c40951_0 : P.sumLeaves 26 41933824 767 = 203528490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 40951) (lo := 0) (len := 767) (W := 203528490) check rows elimOK (by decide) (by decide) cover40951 (by decide)
  decide +kernel

theorem c40951_1 : P.sumLeaves 26 41934591 257 = 138520352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 40951) (lo := 767) (len := 257) (W := 138520352) check rows elimOK (by decide) (by decide) cover40951 (by decide)
  decide +kernel

theorem h40951 : P.leaf 36 40951 = 342048842 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(767, 203528490), (257, 138520352)]) (.cons c40951_0 (.cons c40951_1 (.nil))) (by decide) (by decide))

theorem h16379 : P.leaf 36 16379 = 342048842 :=
  orient6 (v := 40951) (by decide) (by decide +kernel) h40951

theorem cover40958 : P.CoversSplit 26 10 40958 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac88888888888888888fffffafafffffac8aaaaaaaaaaaaaa88fffffafaffccfac88888888888888888ffffffffffccfac8fffffafaffccfac8ccccccccccccc8c88888888888888888fffffafaffccfac8aaaaaaaaaa88aa88ccccc8c8ccccc8c88888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f40958 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (41940992 + i)

theorem c40958_0 : rowSum f40958 0 354 = 141557932 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40958) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40958 (by decide)
  decide +kernel

theorem c40958_1 : rowSum f40958 354 136 = 348758982 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40958) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40958 (by decide)
  decide +kernel

theorem c40958_2 : rowSum f40958 490 491 = 422190852 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40958) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40958 (by decide)
  decide +kernel

theorem c40958_3 : rowSum f40958 981 43 = 168698984 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40958) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40958 (by decide)
  decide +kernel

theorem sum40958 : rowSum f40958 0 1024 = 1081206750 :=
  rowSum_append (F := f40958) (lo := 0) (n := 354) (m := 670) (A := 141557932) (B := 939648818) c40958_0 (rowSum_append (F := f40958) (lo := 354) (n := 136) (m := 534) (A := 348758982) (B := 590889836) c40958_1 (rowSum_append (F := f40958) (lo := 490) (n := 491) (m := 43) (A := 422190852) (B := 168698984) c40958_2 (c40958_3)))

theorem h40958 : P.leaf 36 40958 = 1081206750 :=
  leaf_weighted (k := 26) (d := 10) (H := 40958) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 40958) (by decide) (by decide +kernel)) sum40958

theorem h16382 : P.leaf 36 16382 = 1081206750 :=
  orient6 (v := 40958) (by decide) (by decide +kernel) h40958

theorem cover40959 : P.CoversSplit 26 10 40959 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac88888888888888888fffffafafffffac8aaaaaaaaaaaaaa88fffffafaffccfac88888888888888888ffffffffffccfac8fffffafaffccfac8ccccccccccccc8c88888888888888888fffffafaffccfac8aaaaaaaaaa88aa88ccccc8c8ccccc8c88888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f40959 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (41942016 + i)

theorem c40959_0 : rowSum f40959 0 354 = 554073794 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40959) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40959 (by decide)
  decide +kernel

theorem c40959_1 : rowSum f40959 354 136 = 820669642 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40959) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40959 (by decide)
  decide +kernel

theorem c40959_2 : rowSum f40959 490 491 = 870336016 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40959) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40959 (by decide)
  decide +kernel

theorem c40959_3 : rowSum f40959 981 43 = 331960696 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40959) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40959 (by decide)
  decide +kernel

theorem sum40959 : rowSum f40959 0 1024 = 2577040148 :=
  rowSum_append (F := f40959) (lo := 0) (n := 354) (m := 670) (A := 554073794) (B := 2022966354) c40959_0 (rowSum_append (F := f40959) (lo := 354) (n := 136) (m := 534) (A := 820669642) (B := 1202296712) c40959_1 (rowSum_append (F := f40959) (lo := 490) (n := 491) (m := 43) (A := 870336016) (B := 331960696) c40959_2 (c40959_3)))

theorem h40959 : P.leaf 36 40959 = 2577040148 :=
  leaf_weighted (k := 26) (d := 10) (H := 40959) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 40959) (by decide) (by decide +kernel)) sum40959

theorem h16383 : P.leaf 36 16383 = 2577040148 :=
  orient6 (v := 40959) (by decide) (by decide +kernel) h40959

theorem cover31200 : P.CoversSplit 26 10 31200 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h31200 : P.leaf 36 31200 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31200) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31200) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31200 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31201 : P.CoversSplit 26 10 31201 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h31201 : P.leaf 36 31201 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31201) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31201) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31201 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31203 : P.CoversSplit 26 10 31203 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h31203 : P.leaf 36 31203 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31203) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31203) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31203 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31205 : P.CoversSplit 26 10 31205 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31205 : P.leaf 36 31205 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31205) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31205) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31205 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31207 : P.CoversSplit 26 10 31207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31207 : P.leaf 36 31207 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31207) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31207) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31207 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31215 : P.CoversSplit 26 10 31215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31215 : P.leaf 36 31215 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31215) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31215) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31215 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31217 : P.CoversSplit 26 10 31217 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h31217 : P.leaf 36 31217 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31217) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31217) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31217 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31219 : P.CoversSplit 26 10 31219 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h31219 : P.leaf 36 31219 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31219) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31219) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31219 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31220 : P.CoversSplit 26 10 31220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31220 : P.leaf 36 31220 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31220) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31220) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31220 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31221 : P.CoversSplit 26 10 31221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31221 : P.leaf 36 31221 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31221) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31221) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31221 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31223 : P.CoversSplit 26 10 31223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31223 : P.leaf 36 31223 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31223) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31223) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31223 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31228 : P.CoversSplit 26 10 31228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31228 : P.leaf 36 31228 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31228) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31228) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31228 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31229 : P.CoversSplit 26 10 31229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31229 : P.leaf 36 31229 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31229) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31229) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31229 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31231 : P.CoversSplit 26 10 31231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h31231 : P.leaf 36 31231 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31231) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31231) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88516 : P.CoversSplit 26 10 88516 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88516 : P.leaf 36 88516 = 1040 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88516) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88516) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88516 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31440 : P.leaf 36 31440 = 1040 :=
  orient348 (v := 88516) (by decide) (by decide +kernel) h88516

theorem cover46897 : P.CoversSplit 26 10 46897 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 1265, 1273]) (by decide +kernel)

theorem h46897 : P.leaf 36 46897 = 63376 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 46897) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 46897) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 46897) (weight := rowWeight keep8 twice8) (xs := [255, 511, 767, 1023]) check rows elimOK (by decide) (by decide) cover46897 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31441 : P.leaf 36 31441 = 63376 :=
  orient6 (v := 46897) (by decide) (by decide +kernel) h46897

theorem cover31443 : P.CoversSplit 26 10 31443 0x8000000080000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1315, 1322]) (by decide +kernel)

theorem h31443 : P.leaf 36 31443 = 1281360 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 31443) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 31443) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31443) (weight := rowWeight keep2 twice2) (xs := [927, 959, 991, 1023]) check rows elimOK (by decide) (by decide) cover31443 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover46899 : P.CoversSplit 26 10 46899 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930]) (by decide +kernel)

theorem h46899 : P.leaf 36 46899 = 1740672 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 46899) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 46899) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 46899) (weight := rowWeight keep2 twice2) (xs := [255, 511, 767, 1023]) check rows elimOK (by decide) (by decide) cover46899 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31446 : P.leaf 36 31446 = 1740672 :=
  orient72 (v := 46899) (by decide) (by decide +kernel) h46899

theorem cover46903 : P.CoversSplit 26 10 46903 0xcc00040000000000040004000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000cc00040000000000040004000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 1265, 1315, 1658]) (by decide +kernel)

theorem h46903 : P.leaf 36 46903 = 11990400 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 46903) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 46903) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 46903) (weight := rowWeight keep9 twice9) (xs := [250, 251, 254, 255, 426, 442, 490, 506, 507, 510, 511, 762, 763, 766, 767, 938, 954, 1002, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover46903 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31447 : P.leaf 36 31447 = 11990400 :=
  orient72 (v := 46903) (by decide) (by decide +kernel) h46903

theorem cover31455 : P.CoversSplit 26 10 31455 0xffff0000ffff0500ffff0000ffff000000000000000000000030000000000000050505050505050000000000000000000000000000000000000000000000000000330000000000000033000000000000003300000000000000300000000000000001000100000000000000000000000000010001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f31455 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (32209920 + i)

theorem c31455_0 : rowSum f31455 0 1024 = 75178080 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31455) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover31455 (by decide)
  decide +kernel

theorem sum31455 : rowSum f31455 0 1024 = 75178080 :=
  c31455_0

theorem h31455 : P.leaf 36 31455 = 75178080 :=
  leaf_weighted (k := 26) (d := 10) (H := 31455) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 31455) (by decide) (by decide +kernel)) sum31455

theorem cover88548 : P.CoversSplit 26 10 88548 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88548 : P.leaf 36 88548 = 12608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88548) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88548) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88548 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31472 : P.leaf 36 31472 = 12608 :=
  orient348 (v := 88548) (by decide) (by decide +kernel) h88548

theorem cover46577 : P.CoversSplit 26 10 46577 0x8000000080000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 873, 930, 1315, 1322, 1665]) (by decide +kernel)

theorem h46577 : P.leaf 36 46577 = 697952 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 46577) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 46577) (weight := fun _ => 1) (xs := [927, 959, 991, 1023]) check rows elimOK (by decide) (by decide) cover46577 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31473 : P.leaf 36 31473 = 697952 :=
  orient4 (v := 46577) (by decide) (by decide +kernel) h46577

theorem cover47025 : P.CoversSplit 26 10 47025 0xc000000000000000c00000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000c000000000000000c00000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 873, 930, 1273, 1658]) (by decide +kernel)

theorem h47025 : P.leaf 36 47025 = 648560 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 47025) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 47025) (weight := fun _ => 1) (xs := [191, 254, 255, 446, 447, 510, 511, 703, 766, 767, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover47025 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31474 : P.leaf 36 31474 = 648560 :=
  orient72 (v := 47025) (by decide) (by decide +kernel) h47025

def seg : List (ℕ × ℕ) := [(16371, 720), (16374, 360), (16375, 360), (16376, 360), (16377, 360), (16378, 720), (16379, 720), (16382, 360), (16383, 360), (31200, 15), (31201, 180), (31203, 90), (31205, 180), (31207, 180), (31215, 45), (31217, 180), (31219, 180), (31220, 360), (31221, 720), (31223, 360), (31228, 180), (31229, 360), (31231, 180), (31440, 90), (31441, 360), (31443, 360), (31446, 180), (31447, 360), (31455, 90), (31472, 360), (31473, 720), (31474, 720)]

theorem segOK : checkSeg 20 perms 16371 31475 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16371 31475 10770 1901055133080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1901055133080)
    (SegSum.cons (w := 720) h16371 (SegSum.cons (w := 360) h16374 (SegSum.cons (w := 360) h16375 (SegSum.cons (w := 360) h16376 (SegSum.cons (w := 360) h16377 (SegSum.cons (w := 720) h16378 (SegSum.cons (w := 720) h16379 (SegSum.cons (w := 360) h16382 (SegSum.cons (w := 360) h16383 (SegSum.cons (w := 15) h31200 (SegSum.cons (w := 180) h31201 (SegSum.cons (w := 90) h31203 (SegSum.cons (w := 180) h31205 (SegSum.cons (w := 180) h31207 (SegSum.cons (w := 45) h31215 (SegSum.cons (w := 180) h31217 (SegSum.cons (w := 180) h31219 (SegSum.cons (w := 360) h31220 (SegSum.cons (w := 720) h31221 (SegSum.cons (w := 360) h31223 (SegSum.cons (w := 180) h31228 (SegSum.cons (w := 360) h31229 (SegSum.cons (w := 180) h31231 (SegSum.cons (w := 90) h31440 (SegSum.cons (w := 360) h31441 (SegSum.cons (w := 360) h31443 (SegSum.cons (w := 180) h31446 (SegSum.cons (w := 360) h31447 (SegSum.cons (w := 90) h31455 (SegSum.cons (w := 360) h31472 (SegSum.cons (w := 720) h31473 (SegSum.cons (w := 720) h31474 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S34
