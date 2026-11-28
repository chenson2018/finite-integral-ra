/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S87

open RACert RACert.Problem

theorem cover28655 : P.CoversSplit 24 10 28655 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8fffffffffafafafaffff0000fafa0000fffffffffafafafaffff0000fafa0000ffcc0000fac80000cccc0000c8c80000ffcc0000fac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1259, 1264, 1601]) (by decide +kernel)

theorem c28655_0 : P.sumLeaves 24 29342720 318 = 76827947 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 0) (len := 318) (W := 76827947) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_1 : P.sumLeaves 24 29343038 144 = 98817879 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 318) (len := 144) (W := 98817879) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_2 : P.sumLeaves 24 29343182 154 = 119300147 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 462) (len := 154) (W := 119300147) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_3 : P.sumLeaves 24 29343336 161 = 161837311 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 616) (len := 161) (W := 161837311) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_4 : P.sumLeaves 24 29343497 109 = 128934080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 777) (len := 109) (W := 128934080) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_5 : P.sumLeaves 24 29343606 112 = 219507963 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 886) (len := 112) (W := 219507963) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_6 : P.sumLeaves 24 29343718 26 = 109075038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 998) (len := 26) (W := 109075038) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem h28655 : P.leaf 34 28655 = 914300365 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(318, 76827947), (144, 98817879), (154, 119300147), (161, 161837311), (109, 128934080), (112, 219507963), (26, 109075038)]) (.cons c28655_0 (.cons c28655_1 (.cons c28655_2 (.cons c28655_3 (.cons c28655_4 (.cons c28655_5 (.cons c28655_6 (.nil)))))))) (by decide) (by decide))

theorem cover59375 : P.CoversSplit 24 10 59375 0xfffffffffefeaaaafffffffffefeaaaafffffffffefeaaaafffffffffefeaaaaffeeffeefeeeaaaacccccccccccc8888ffeeffeefeeeaaaacccccccccccc8888fffffffffefeaaaafffffffffefeaaaafffffffffafaaaaafffffffffafaaaaaffeeffeefeeeaaaacccccccccccc8888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f59375 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60800000 + i)

theorem c59375_0 : rowSum f59375 0 215 = 109202495 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59375) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59375 (by decide)
  decide +kernel

theorem c59375_1 : rowSum f59375 215 203 = 200263519 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59375) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59375 (by decide)
  decide +kernel

theorem c59375_2 : rowSum f59375 418 257 = 334601190 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59375) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59375 (by decide)
  decide +kernel

theorem c59375_3 : rowSum f59375 675 349 = 496349262 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59375) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59375 (by decide)
  decide +kernel

theorem sum59375 : rowSum f59375 0 1024 = 1140416466 :=
  rowSum_append (F := f59375) (lo := 0) (n := 215) (m := 809) (A := 109202495) (B := 1031213971) c59375_0 (rowSum_append (F := f59375) (lo := 215) (n := 203) (m := 606) (A := 200263519) (B := 830950452) c59375_1 (rowSum_append (F := f59375) (lo := 418) (n := 257) (m := 349) (A := 334601190) (B := 496349262) c59375_2 (c59375_3)))

theorem h59375 : P.leaf 34 59375 = 1140416466 :=
  leaf_weighted (k := 24) (d := 10) (H := 59375) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59375) (by decide) (by decide +kernel)) sum59375

theorem h28670 : P.leaf 34 28670 = 1140416466 :=
  orient24 (v := 59375) (by decide) (by decide +kernel) h59375

theorem cover59391 : P.CoversSplit 24 10 59391 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaacccccccccccc8888ffffffffffffaaaacccccccccccc8888ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaffffffffffffaaaacccccccccccc8888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 915, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f59391 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60816384 + i)

theorem c59391_0 : rowSum f59391 0 213 = 209873670 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59391 (by decide)
  decide +kernel

theorem c59391_1 : rowSum f59391 213 196 = 304335754 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59391 (by decide)
  decide +kernel

theorem c59391_2 : rowSum f59391 409 238 = 490760069 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59391 (by decide)
  decide +kernel

theorem c59391_3 : rowSum f59391 647 364 = 671680077 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59391 (by decide)
  decide +kernel

theorem c59391_4 : rowSum f59391 1011 13 = 69733860 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59391 (by decide)
  decide +kernel

theorem sum59391 : rowSum f59391 0 1024 = 1746383430 :=
  rowSum_append (F := f59391) (lo := 0) (n := 213) (m := 811) (A := 209873670) (B := 1536509760) c59391_0 (rowSum_append (F := f59391) (lo := 213) (n := 196) (m := 615) (A := 304335754) (B := 1232174006) c59391_1 (rowSum_append (F := f59391) (lo := 409) (n := 238) (m := 377) (A := 490760069) (B := 741413937) c59391_2 (rowSum_append (F := f59391) (lo := 647) (n := 364) (m := 13) (A := 671680077) (B := 69733860) c59391_3 (c59391_4))))

theorem h59391 : P.leaf 34 59391 = 1746383430 :=
  leaf_weighted (k := 24) (d := 10) (H := 59391) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59391) (by decide) (by decide +kernel)) sum59391

theorem h28671 : P.leaf 34 28671 = 1746383430 :=
  orient24 (v := 59391) (by decide) (by decide +kernel) h59391

theorem cover32228 : P.CoversSplit 24 10 32228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h32228 : P.leaf 34 32228 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 32228) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 32228) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32228 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32229 : P.CoversSplit 24 10 32229 0xffff0000eae00000ffff0000eae00000ffff000000000000ffff000000000000ffcc0000eac00000ffcc0000eac00000ffcc000000000000ffcc000000000000ffff0000eae000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c32229_0 : P.sumLeaves 24 33002496 758 = 39782181 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32229) (lo := 0) (len := 758) (W := 39782181) check rows elimOK (by decide) (by decide) cover32229 (by decide)
  decide +kernel

theorem c32229_1 : P.sumLeaves 24 33003254 266 = 78096624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32229) (lo := 758) (len := 266) (W := 78096624) check rows elimOK (by decide) (by decide) cover32229 (by decide)
  decide +kernel

theorem h32229 : P.leaf 34 32229 = 117878805 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(758, 39782181), (266, 78096624)]) (.cons c32229_0 (.cons c32229_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28655, 48), (28670, 24), (28671, 24), (32228, 12), (32229, 48)]

theorem segOK : checkSeg 16 perms 28655 32231 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28655 32231 156 118827797664 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 118827797664)
    (SegSum.cons (w := 48) h28655 (SegSum.cons (w := 24) h28670 (SegSum.cons (w := 24) h28671 (SegSum.cons (w := 12) h32228 (SegSum.cons (w := 48) h32229 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S87
