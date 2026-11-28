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

namespace RACert.S6N0.C0.S80

open RACert RACert.Problem

theorem cover327667 : P.CoversSplit 26 10 327667 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1658, 1665]) (by decide +kernel)

noncomputable def f327667 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (335531008 + i)

theorem c327667_0 : rowSum f327667 0 241 = 722334330 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327667) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327667 (by decide)
  decide +kernel

theorem c327667_1 : rowSum f327667 241 148 = 780575024 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327667) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327667 (by decide)
  decide +kernel

theorem c327667_2 : rowSum f327667 389 102 = 1079945208 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327667) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327667 (by decide)
  decide +kernel

theorem c327667_3 : rowSum f327667 491 403 = 1115311420 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327667) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327667 (by decide)
  decide +kernel

theorem c327667_4 : rowSum f327667 894 130 = 591008488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327667) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327667 (by decide)
  decide +kernel

theorem sum327667 : rowSum f327667 0 1024 = 4289174470 :=
  rowSum_append (F := f327667) (lo := 0) (n := 241) (m := 783) (A := 722334330) (B := 3566840140) c327667_0 (rowSum_append (F := f327667) (lo := 241) (n := 148) (m := 635) (A := 780575024) (B := 2786265116) c327667_1 (rowSum_append (F := f327667) (lo := 389) (n := 102) (m := 533) (A := 1079945208) (B := 1706319908) c327667_2 (rowSum_append (F := f327667) (lo := 491) (n := 403) (m := 130) (A := 1115311420) (B := 591008488) c327667_3 (c327667_4))))

theorem h327667 : P.leaf 36 327667 = 4289174470 :=
  leaf_weighted (k := 26) (d := 10) (H := 327667) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 327667) (by decide) (by decide +kernel)) sum327667

theorem h131065 : P.leaf 36 131065 = 4289174470 :=
  orient6 (v := 327667) (by decide) (by decide +kernel) h327667

theorem cover327678 : P.CoversSplit 26 10 327678 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f327678 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (335542272 + i)

theorem c327678_0 : rowSum f327678 0 241 = 908783986 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327678) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327678 (by decide)
  decide +kernel

theorem c327678_1 : rowSum f327678 241 148 = 1238739544 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327678) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327678 (by decide)
  decide +kernel

theorem c327678_2 : rowSum f327678 389 102 = 1961677312 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327678) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327678 (by decide)
  decide +kernel

theorem c327678_3 : rowSum f327678 491 403 = 2006627336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327678) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327678 (by decide)
  decide +kernel

theorem c327678_4 : rowSum f327678 894 130 = 1028185756 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327678) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327678 (by decide)
  decide +kernel

theorem sum327678 : rowSum f327678 0 1024 = 7144013934 :=
  rowSum_append (F := f327678) (lo := 0) (n := 241) (m := 783) (A := 908783986) (B := 6235229948) c327678_0 (rowSum_append (F := f327678) (lo := 241) (n := 148) (m := 635) (A := 1238739544) (B := 4996490404) c327678_1 (rowSum_append (F := f327678) (lo := 389) (n := 102) (m := 533) (A := 1961677312) (B := 3034813092) c327678_2 (rowSum_append (F := f327678) (lo := 491) (n := 403) (m := 130) (A := 2006627336) (B := 1028185756) c327678_3 (c327678_4))))

theorem h327678 : P.leaf 36 327678 = 7144013934 :=
  leaf_weighted (k := 26) (d := 10) (H := 327678) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 327678) (by decide) (by decide +kernel)) sum327678

theorem h131067 : P.leaf 36 131067 = 7144013934 :=
  orient80 (v := 327678) (by decide) (by decide +kernel) h327678

theorem cover327679 : P.CoversSplit 26 10 327679 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f327679 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (335543296 + i)

theorem c327679_0 : rowSum f327679 0 241 = 2373978640 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327679) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327679 (by decide)
  decide +kernel

theorem c327679_1 : rowSum f327679 241 148 = 2959877228 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327679) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327679 (by decide)
  decide +kernel

theorem c327679_2 : rowSum f327679 389 102 = 3132354596 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327679) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327679 (by decide)
  decide +kernel

theorem c327679_3 : rowSum f327679 491 403 = 3510559088 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327679) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327679 (by decide)
  decide +kernel

theorem c327679_4 : rowSum f327679 894 130 = 1471386224 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327679) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327679 (by decide)
  decide +kernel

theorem sum327679 : rowSum f327679 0 1024 = 13448155776 :=
  rowSum_append (F := f327679) (lo := 0) (n := 241) (m := 783) (A := 2373978640) (B := 11074177136) c327679_0 (rowSum_append (F := f327679) (lo := 241) (n := 148) (m := 635) (A := 2959877228) (B := 8114299908) c327679_1 (rowSum_append (F := f327679) (lo := 389) (n := 102) (m := 533) (A := 3132354596) (B := 4981945312) c327679_2 (rowSum_append (F := f327679) (lo := 491) (n := 403) (m := 130) (A := 3510559088) (B := 1471386224) c327679_3 (c327679_4))))

theorem h327679 : P.leaf 36 327679 = 13448155776 :=
  leaf_weighted (k := 26) (d := 10) (H := 327679) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 327679) (by decide) (by decide +kernel)) sum327679

theorem h131071 : P.leaf 36 131071 = 13448155776 :=
  orient6 (v := 327679) (by decide) (by decide +kernel) h327679

theorem cover227823 : P.CoversSplit 26 10 227823 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h227823 : P.leaf 36 227823 = 19872568 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 227823) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 227823) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 227823) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover227823 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover227839 : P.CoversSplit 26 10 227839 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h227839 : P.leaf 36 227839 = 25393548 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 227839) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 227839) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 227839) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover227839 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover374199 : P.CoversSplit 26 10 374199 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000002200220000000000000000000000000000000000000000003300330000000000220022 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 930]) (by decide +kernel)

noncomputable def f374199 (i : ℕ) := rowWeight keep17 twice17 i * P.leaf 26 (383179776 + i)

theorem c374199_0 : rowSum f374199 0 1024 = 180460821 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 374199) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover374199 (by decide)
  decide +kernel

theorem sum374199 : rowSum f374199 0 1024 = 180460821 :=
  c374199_0

theorem h374199 : P.leaf 36 374199 = 180460821 :=
  leaf_weighted (k := 26) (d := 10) (H := 374199) (keep := keep17) (twice := twice17) rows (by decide) (by decide) (bal17) (invRow17 (H := 374199) (by decide) (by decide +kernel)) sum374199

theorem h228023 : P.leaf 36 228023 = 180460821 :=
  orient4 (v := 374199) (by decide) (by decide +kernel) h374199

theorem cover228025 : P.CoversSplit 26 10 228025 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228025_0 : P.sumLeaves 26 233497600 1024 = 143256860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228025) (lo := 0) (len := 1024) (W := 143256860) check rows elimOK (by decide) (by decide) cover228025 (by decide)
  decide +kernel

theorem h228025 : P.leaf 36 228025 = 143256860 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 143256860)]) (.cons c228025_0 (.nil)) (by decide) (by decide))

theorem cover228027 : P.CoversSplit 26 10 228027 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228027 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (233499648 + i)

theorem c228027_0 : rowSum f228027 0 1024 = 329127888 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228027) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover228027 (by decide)
  decide +kernel

theorem sum228027 : rowSum f228027 0 1024 = 329127888 :=
  c228027_0

theorem h228027 : P.leaf 36 228027 = 329127888 :=
  leaf_weighted (k := 26) (d := 10) (H := 228027) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 228027) (by decide) (by decide +kernel)) sum228027

theorem cover228029 : P.CoversSplit 26 10 228029 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228029_0 : P.sumLeaves 26 233501696 998 = 224947572 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228029) (lo := 0) (len := 998) (W := 224947572) check rows elimOK (by decide) (by decide) cover228029 (by decide)
  decide +kernel

theorem c228029_1 : P.sumLeaves 26 233502694 26 = 197077268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228029) (lo := 998) (len := 26) (W := 197077268) check rows elimOK (by decide) (by decide) cover228029 (by decide)
  decide +kernel

theorem h228029 : P.leaf 36 228029 = 422024840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 224947572), (26, 197077268)]) (.cons c228029_0 (.cons c228029_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(131065, 180), (131067, 180), (131071, 60), (227823, 90), (227839, 60), (228023, 60), (228025, 720), (228027, 360), (228029, 720)]

theorem segOK : checkSeg 20 perms 131065 228031 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131065 228031 2430 3404491916220 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3404491916220)
    (SegSum.cons (w := 180) h131065 (SegSum.cons (w := 180) h131067 (SegSum.cons (w := 60) h131071 (SegSum.cons (w := 90) h227823 (SegSum.cons (w := 60) h227839 (SegSum.cons (w := 60) h228023 (SegSum.cons (w := 720) h228025 (SegSum.cons (w := 360) h228027 (SegSum.cons (w := 720) h228029 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S80
