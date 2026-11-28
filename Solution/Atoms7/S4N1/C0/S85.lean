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

namespace RACert.S4N1.C0.S85

open RACert RACert.Problem

theorem cover58863 : P.CoversSplit 24 10 58863 0xfffffffffefaaaaafffffffffefaaaaafffffffffefaaaaafffffffffefaaaaaffecffecfee8aaa8ccccccccccc88888ffecffecfee8aaa8ccccccccccc88888fffffffffefaaaaafffffffffefaaaaafffffffffafaaaaafffffffffafaaaaaffecffecfee8aaa8ccccccccccc88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f58863 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60275712 + i)

theorem c58863_0 : rowSum f58863 0 220 = 62638613 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58863) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58863 (by decide)
  decide +kernel

theorem c58863_1 : rowSum f58863 220 205 = 110099792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58863) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58863 (by decide)
  decide +kernel

theorem c58863_2 : rowSum f58863 425 269 = 203217446 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58863) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58863 (by decide)
  decide +kernel

theorem c58863_3 : rowSum f58863 694 330 = 265461656 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58863) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58863 (by decide)
  decide +kernel

theorem sum58863 : rowSum f58863 0 1024 = 641417507 :=
  rowSum_append (F := f58863) (lo := 0) (n := 220) (m := 804) (A := 62638613) (B := 578778894) c58863_0 (rowSum_append (F := f58863) (lo := 220) (n := 205) (m := 599) (A := 110099792) (B := 468679102) c58863_1 (rowSum_append (F := f58863) (lo := 425) (n := 269) (m := 330) (A := 203217446) (B := 265461656) c58863_2 (c58863_3)))

theorem h58863 : P.leaf 34 58863 = 641417507 :=
  leaf_weighted (k := 24) (d := 10) (H := 58863) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58863) (by decide) (by decide +kernel)) sum58863

theorem h28158 : P.leaf 34 28158 = 641417507 :=
  orient24 (v := 58863) (by decide) (by decide +kernel) h58863

theorem cover58879 : P.CoversSplit 24 10 58879 0xfffffffffffaaaaafffffffffffaaaaafffffffffffaaaaafffffffffffaaaaafffcfffcfff8aaa8ccccccccccc88888fffcfffcfff8aaa8ccccccccccc88888fffffffffffaaaaafffffffffffaaaaafffffffffafaaaaafffffffffafaaaaafffcfffcfff8aaa8ccccccccccc88888ffccffccfac8aa88ccccccccc8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f58879 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60292096 + i)

theorem c58879_0 : rowSum f58879 0 218 = 177698182 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58879) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58879 (by decide)
  decide +kernel

theorem c58879_1 : rowSum f58879 218 202 = 256959397 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58879) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58879 (by decide)
  decide +kernel

theorem c58879_2 : rowSum f58879 420 262 = 384758947 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58879) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58879 (by decide)
  decide +kernel

theorem c58879_3 : rowSum f58879 682 342 = 466167798 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58879) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58879 (by decide)
  decide +kernel

theorem sum58879 : rowSum f58879 0 1024 = 1285584324 :=
  rowSum_append (F := f58879) (lo := 0) (n := 218) (m := 806) (A := 177698182) (B := 1107886142) c58879_0 (rowSum_append (F := f58879) (lo := 218) (n := 202) (m := 604) (A := 256959397) (B := 850926745) c58879_1 (rowSum_append (F := f58879) (lo := 420) (n := 262) (m := 342) (A := 384758947) (B := 466167798) c58879_2 (c58879_3)))

theorem h58879 : P.leaf 34 58879 = 1285584324 :=
  leaf_weighted (k := 24) (d := 10) (H := 58879) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58879) (by decide) (by decide +kernel)) sum58879

theorem h28159 : P.leaf 34 28159 = 1285584324 :=
  orient24 (v := 58879) (by decide) (by decide +kernel) h58879

theorem cover59103 : P.CoversSplit 24 10 59103 0xffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0ffffffffffffa0a0cc00cc00cc008000ffffffffffffa0a0cc00cc00cc008000ffffffffffffa0a0ffffffffffffa0a0fffffffffafaa0a0fffffffffafaa0a0ffffffffffffa0a0cc00cc00cc008000ffccffccfac8a080cc00cc00c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 573, 1202, 1217, 1601, 1609]) (by decide +kernel)

noncomputable def f59103 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60521472 + i)

theorem c59103_0 : rowSum f59103 0 245 = 54381465 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59103) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59103 (by decide)
  decide +kernel

theorem c59103_1 : rowSum f59103 245 200 = 154263533 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59103) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59103 (by decide)
  decide +kernel

theorem c59103_2 : rowSum f59103 445 309 = 265421555 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59103) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59103 (by decide)
  decide +kernel

theorem c59103_3 : rowSum f59103 754 270 = 240659447 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59103) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59103 (by decide)
  decide +kernel

theorem sum59103 : rowSum f59103 0 1024 = 714726000 :=
  rowSum_append (F := f59103) (lo := 0) (n := 245) (m := 779) (A := 54381465) (B := 660344535) c59103_0 (rowSum_append (F := f59103) (lo := 245) (n := 200) (m := 579) (A := 154263533) (B := 506081002) c59103_1 (rowSum_append (F := f59103) (lo := 445) (n := 309) (m := 270) (A := 265421555) (B := 240659447) c59103_2 (c59103_3)))

theorem h59103 : P.leaf 34 59103 = 714726000 :=
  leaf_weighted (k := 24) (d := 10) (H := 59103) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59103) (by decide) (by decide +kernel)) sum59103

theorem h28603 : P.leaf 34 28603 = 714726000 :=
  orient5 (v := 59103) (by decide) (by decide +kernel) h59103

theorem cover28604 : P.CoversSplit 24 10 28604 0xffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff88fa88f080cc88cc88c888c080ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff8880008000cc88cc8880008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 1202, 1601]) (ps := [(8, [1217, 1609], [1272]), (14, [1217, 1609], [1272])]) (by decide +kernel)

noncomputable def f28604 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (29290496 + i)

theorem c28604_0 : rowSum f28604 0 307 = 15465124 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28604 (by decide)
  decide +kernel

theorem c28604_1 : rowSum f28604 307 203 = 106598752 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28604 (by decide)
  decide +kernel

theorem c28604_2 : rowSum f28604 510 514 = 151110682 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28604 (by decide)
  decide +kernel

theorem sum28604 : rowSum f28604 0 1024 = 273174558 :=
  rowSum_append (F := f28604) (lo := 0) (n := 307) (m := 717) (A := 15465124) (B := 257709434) c28604_0 (rowSum_append (F := f28604) (lo := 307) (n := 203) (m := 514) (A := 106598752) (B := 151110682) c28604_1 (c28604_2))

theorem h28604 : P.leaf 34 28604 = 273174558 :=
  leaf_weighted (k := 24) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 28604) (by decide) (by decide +kernel)) sum28604

theorem cover40935 : P.CoversSplit 24 10 40935 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8fffffffffafafafaffff0000fafa0000fffffffffafafafaffff0000fafa0000ffcc0000fac80000cccc0000c8c80000ffcc0000fac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1258, 1264, 1601]) (by decide +kernel)

theorem c40935_0 : P.sumLeaves 24 41917440 318 = 35182049 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 0) (len := 318) (W := 35182049) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem c40935_1 : P.sumLeaves 24 41917758 144 = 66739589 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 318) (len := 144) (W := 66739589) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem c40935_2 : P.sumLeaves 24 41917902 154 = 81014380 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 462) (len := 154) (W := 81014380) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem c40935_3 : P.sumLeaves 24 41918056 161 = 95003938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 616) (len := 161) (W := 95003938) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem c40935_4 : P.sumLeaves 24 41918217 109 = 83501755 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 777) (len := 109) (W := 83501755) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem c40935_5 : P.sumLeaves 24 41918326 112 = 148612091 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 886) (len := 112) (W := 148612091) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem c40935_6 : P.sumLeaves 24 41918438 26 = 84185298 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40935) (lo := 998) (len := 26) (W := 84185298) check rows elimOK (by decide) (by decide) cover40935 (by decide)
  decide +kernel

theorem h40935 : P.leaf 34 40935 = 594239100 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(318, 35182049), (144, 66739589), (154, 81014380), (161, 95003938), (109, 83501755), (112, 148612091), (26, 84185298)]) (.cons c40935_0 (.cons c40935_1 (.cons c40935_2 (.cons c40935_3 (.cons c40935_4 (.cons c40935_5 (.cons c40935_6 (.nil)))))))) (by decide) (by decide))

theorem h28605 : P.leaf 34 28605 = 594239100 :=
  orient4 (v := 40935) (by decide) (by decide +kernel) h40935

def seg : List (ℕ × ℕ) := [(28158, 24), (28159, 24), (28603, 6), (28604, 24), (28605, 48)]

theorem segOK : checkSeg 16 perms 28158 28607 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28158 28607 126 85616066136 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 85616066136)
    (SegSum.cons (w := 24) h28158 (SegSum.cons (w := 24) h28159 (SegSum.cons (w := 6) h28603 (SegSum.cons (w := 24) h28604 (SegSum.cons (w := 48) h28605 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S85
