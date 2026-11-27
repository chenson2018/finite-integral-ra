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

namespace RACert.S4N1.C0.S106

open RACert RACert.Problem

theorem cover32228 : P.CoversSplit 24 10 32228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c32228_0 : P.sumLeaves 24 33001472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32228) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32228 (by decide)
  decide +kernel

theorem h32228 : P.leaf 34 32228 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32228_0 (.nil)) (by decide) (by decide))

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

theorem cover32231 : P.CoversSplit 24 10 32231 0xfffffffffafafafaffff0000fafa0000ffff000000000000ffff000000000000ffccffccfac8fac8ffcc0000fac80000ffcc000000000000ffcc000000000000fffffffffafafafa0000000000000000ffff05050000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32231 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (33004544 + i)

theorem c32231_0 : rowSum f32231 0 735 = 145837428 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32231) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32231 (by decide)
  decide +kernel

theorem c32231_1 : rowSum f32231 735 289 = 141983888 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32231) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32231 (by decide)
  decide +kernel

theorem sum32231 : rowSum f32231 0 1024 = 287821316 :=
  rowSum_append (F := f32231) (lo := 0) (n := 735) (m := 289) (A := 145837428) (B := 141983888) c32231_0 (c32231_1)

theorem h32231 : P.leaf 34 32231 = 287821316 :=
  leaf_weighted (k := 24) (d := 10) (H := 32231) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 32231) (by decide) (by decide +kernel)) sum32231

theorem cover32236 : P.CoversSplit 24 10 32236 0xffffffffeae0a0a0ffffffffeae0a0a0ffff000000000000ffff000000000000eec0eec0eac0a080cc00cc00c8008000eec0000000000000cc00000000000000ffffffffeae0a0a00000000000000000ffff05050000000000330001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 865, 1210, 1259]) (by decide +kernel)

noncomputable def f32236 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33009664 + i)

theorem c32236_0 : rowSum f32236 0 934 = 53857257 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32236) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32236 (by decide)
  decide +kernel

theorem c32236_1 : rowSum f32236 934 90 = 50220648 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32236) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32236 (by decide)
  decide +kernel

theorem sum32236 : rowSum f32236 0 1024 = 104077905 :=
  rowSum_append (F := f32236) (lo := 0) (n := 934) (m := 90) (A := 53857257) (B := 50220648) c32236_0 (c32236_1)

theorem h32236 : P.leaf 34 32236 = 104077905 :=
  leaf_weighted (k := 24) (d := 10) (H := 32236) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32236) (by decide) (by decide +kernel)) sum32236

theorem cover32237 : P.CoversSplit 24 10 32237 0xffffffffeae0a0a0ffffffffeae0a0a0ffff000000000000ffff000000000000ffccffcceac0a080ffccffcceac0a080ffcc000000000000ffcc000000000000ffffffffeae0a0a00000000000000000ffff05050000000000330001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32237 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (33010688 + i)

theorem c32237_0 : rowSum f32237 0 762 = 71242315 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32237) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32237 (by decide)
  decide +kernel

theorem c32237_1 : rowSum f32237 762 262 = 119600405 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32237) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32237 (by decide)
  decide +kernel

theorem sum32237 : rowSum f32237 0 1024 = 190842720 :=
  rowSum_append (F := f32237) (lo := 0) (n := 762) (m := 262) (A := 71242315) (B := 119600405) c32237_0 (c32237_1)

theorem h32237 : P.leaf 34 32237 = 190842720 :=
  leaf_weighted (k := 24) (d := 10) (H := 32237) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 32237) (by decide) (by decide +kernel)) sum32237

theorem cover32239 : P.CoversSplit 24 10 32239 0xfffffffffafafafafffffffffafafafaffff000000000000ffff000000000000ffccffccfac8fac8ffccffccfac8fac8ffcc000000000000ffcc000000000000fffffffffafafafa0000000000000000ffff05050000000000330001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32239 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33012736 + i)

theorem c32239_0 : rowSum f32239 0 686 = 154001751 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32239) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32239 (by decide)
  decide +kernel

theorem c32239_1 : rowSum f32239 686 338 = 212069644 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32239) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32239 (by decide)
  decide +kernel

theorem sum32239 : rowSum f32239 0 1024 = 366071395 :=
  rowSum_append (F := f32239) (lo := 0) (n := 686) (m := 338) (A := 154001751) (B := 212069644) c32239_0 (c32239_1)

theorem h32239 : P.leaf 34 32239 = 366071395 :=
  leaf_weighted (k := 24) (d := 10) (H := 32239) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32239) (by decide) (by decide +kernel)) sum32239

theorem cover32245 : P.CoversSplit 24 10 32245 0xfffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0fffffffffaf0f0f0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0ffccffccfac0f0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c32245_0 : P.sumLeaves 24 33018880 170 = 10599992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 0) (len := 170) (W := 10599992) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_1 : P.sumLeaves 24 33019050 140 = 24960442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 170) (len := 140) (W := 24960442) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_2 : P.sumLeaves 24 33019190 124 = 33248529 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 310) (len := 124) (W := 33248529) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_3 : P.sumLeaves 24 33019314 136 = 68411106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 434) (len := 136) (W := 68411106) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_4 : P.sumLeaves 24 33019450 168 = 58719142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 570) (len := 168) (W := 58719142) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_5 : P.sumLeaves 24 33019618 130 = 68832552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 738) (len := 130) (W := 68832552) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_6 : P.sumLeaves 24 33019748 124 = 104710918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 868) (len := 124) (W := 104710918) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem c32245_7 : P.sumLeaves 24 33019872 32 = 64421172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32245) (lo := 992) (len := 32) (W := 64421172) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem h32245 : P.leaf 34 32245 = 433903853 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(170, 10599992), (140, 24960442), (124, 33248529), (136, 68411106), (168, 58719142), (130, 68832552), (124, 104710918), (32, 64421172)]) (.cons c32245_0 (.cons c32245_1 (.cons c32245_2 (.cons c32245_3 (.cons c32245_4 (.cons c32245_5 (.cons c32245_6 (.cons c32245_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(32228, 12), (32229, 48), (32231, 24), (32236, 12), (32237, 24), (32239, 12), (32245, 24)]

theorem segOK : checkSeg 16 perms 32228 32246 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32228 32246 156 33201603576 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 33201603576)
    (SegSum.cons (w := 12) h32228 (SegSum.cons (w := 48) h32229 (SegSum.cons (w := 24) h32231 (SegSum.cons (w := 12) h32236 (SegSum.cons (w := 24) h32237 (SegSum.cons (w := 12) h32239 (SegSum.cons (w := 24) h32245 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S106
