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

namespace RACert.S4N1.C0.S88

open RACert RACert.Problem

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
  leaf_weighted (k := 24) (d := 10) (H := 32231) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 32231) (by decide) (by decide +kernel)) sum32231

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
  leaf_weighted (k := 24) (d := 10) (H := 32236) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32236) (by decide) (by decide +kernel)) sum32236

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
  leaf_weighted (k := 24) (d := 10) (H := 32237) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 32237) (by decide) (by decide +kernel)) sum32237

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
  leaf_weighted (k := 24) (d := 10) (H := 32239) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32239) (by decide) (by decide +kernel)) sum32239

theorem cover57276 : P.CoversSplit 24 10 57276 0xffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff88fa88f080cc88cc88c888c080ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff8800000000cc88cc8800000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 1202, 1308, 1601]) (by decide +kernel)

noncomputable def f57276 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (58650624 + i)

theorem c57276_0 : rowSum f57276 0 312 = 57808541 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57276) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57276 (by decide)
  decide +kernel

theorem c57276_1 : rowSum f57276 312 343 = 171231252 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57276) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57276 (by decide)
  decide +kernel

theorem c57276_2 : rowSum f57276 655 369 = 204864060 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57276) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57276 (by decide)
  decide +kernel

theorem sum57276 : rowSum f57276 0 1024 = 433903853 :=
  rowSum_append (F := f57276) (lo := 0) (n := 312) (m := 712) (A := 57808541) (B := 376095312) c57276_0 (rowSum_append (F := f57276) (lo := 312) (n := 343) (m := 369) (A := 171231252) (B := 204864060) c57276_1 (c57276_2))

theorem h57276 : P.leaf 34 57276 = 433903853 :=
  leaf_weighted (k := 24) (d := 10) (H := 57276) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 57276) (by decide) (by decide +kernel)) sum57276

theorem h32245 : P.leaf 34 32245 = 433903853 :=
  orient25 (v := 57276) (by decide) (by decide +kernel) h57276

theorem cover61372 : P.CoversSplit 24 10 61372 0xffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff88fa88f080cc88cc88c888c080ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff8880008000cc88cc8880008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 1202, 1601]) (ps := [(8, [1217, 1609], [1272]), (14, [1217, 1609], [1272])]) (by decide +kernel)

noncomputable def f61372 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (62844928 + i)

theorem c61372_0 : rowSum f61372 0 307 = 55658874 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 61372) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover61372 (by decide)
  decide +kernel

theorem c61372_1 : rowSum f61372 307 203 = 167712636 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 61372) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover61372 (by decide)
  decide +kernel

theorem c61372_2 : rowSum f61372 510 514 = 210893192 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 61372) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover61372 (by decide)
  decide +kernel

theorem sum61372 : rowSum f61372 0 1024 = 434264702 :=
  rowSum_append (F := f61372) (lo := 0) (n := 307) (m := 717) (A := 55658874) (B := 378605828) c61372_0 (rowSum_append (F := f61372) (lo := 307) (n := 203) (m := 514) (A := 167712636) (B := 210893192) c61372_1 (c61372_2))

theorem h61372 : P.leaf 34 61372 = 434264702 :=
  leaf_weighted (k := 24) (d := 10) (H := 61372) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 61372) (by decide) (by decide +kernel)) sum61372

theorem h32246 : P.leaf 34 32246 = 434264702 :=
  orient5 (v := 61372) (by decide) (by decide +kernel) h61372

theorem cover56767 : P.CoversSplit 24 10 56767 0xfffffffffffaf0f0fffffffffffaf0f0fffffffffffaf0f0fffffffffffaf0f0fffcfffcfff8f0f0ccccccccccc8c0c0fffcfffcfff8f0f0ccccccccccc8c0c0fffffffffffaf0f0fffffffffffaf0f0fffffffffafaf0f0fffffffffafaf0f0fffcfffcfff8f0f0ccccccccccc8c0c0ffccffcc00000000cccccccc00000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1217, 1308, 1601, 1609]) (by decide +kernel)

theorem c56767_0 : P.sumLeaves 24 58129408 234 = 42740305 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 0) (len := 234) (W := 42740305) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_1 : P.sumLeaves 24 58129642 122 = 58984353 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 234) (len := 122) (W := 58984353) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_2 : P.sumLeaves 24 58129764 116 = 108457431 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 356) (len := 116) (W := 108457431) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_3 : P.sumLeaves 24 58129880 146 = 104826627 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 472) (len := 146) (W := 104826627) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_4 : P.sumLeaves 24 58130026 154 = 160441822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 618) (len := 154) (W := 160441822) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_5 : P.sumLeaves 24 58130180 112 = 109372564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 772) (len := 112) (W := 109372564) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_6 : P.sumLeaves 24 58130292 116 = 213660943 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 884) (len := 116) (W := 213660943) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem c56767_7 : P.sumLeaves 24 58130408 24 = 79331003 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 56767) (lo := 1000) (len := 24) (W := 79331003) check rows elimOK (by decide) (by decide) cover56767 (by decide)
  decide +kernel

theorem h56767 : P.leaf 34 56767 = 877815048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(234, 42740305), (122, 58984353), (116, 108457431), (146, 104826627), (154, 160441822), (112, 109372564), (116, 213660943), (24, 79331003)]) (.cons c56767_0 (.cons c56767_1 (.cons c56767_2 (.cons c56767_3 (.cons c56767_4 (.cons c56767_5 (.cons c56767_6 (.cons c56767_7 (.nil))))))))) (by decide) (by decide))

theorem h32247 : P.leaf 34 32247 = 877815048 :=
  orient4 (v := 56767) (by decide) (by decide +kernel) h56767

def seg : List (ℕ × ℕ) := [(32231, 24), (32236, 12), (32237, 24), (32239, 12), (32245, 24), (32246, 24), (32247, 48)]

theorem segOK : checkSeg 16 perms 32231 32252 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32231 32252 168 80100896088 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 80100896088)
    (SegSum.cons (w := 24) h32231 (SegSum.cons (w := 12) h32236 (SegSum.cons (w := 24) h32237 (SegSum.cons (w := 12) h32239 (SegSum.cons (w := 24) h32245 (SegSum.cons (w := 24) h32246 (SegSum.cons (w := 48) h32247 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S88
