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

namespace RACert.S6N0.C0.S97

open RACert RACert.Problem

theorem cover229103 : P.CoversSplit 26 10 229103 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229103_0 : P.sumLeaves 26 234601472 735 = 283780350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 0) (len := 735) (W := 283780350) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem c229103_1 : P.sumLeaves 26 234602207 228 = 806341394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 735) (len := 228) (W := 806341394) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem c229103_2 : P.sumLeaves 26 234602435 61 = 826236858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 963) (len := 61) (W := 826236858) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem h229103 : P.leaf 36 229103 = 1916358602 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 283780350), (228, 806341394), (61, 826236858)]) (.cons c229103_0 (.cons c229103_1 (.cons c229103_2 (.nil)))) (by decide) (by decide))

theorem cover229118 : P.CoversSplit 26 10 229118 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229118 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (234616832 + i)

theorem c229118_0 : rowSum f229118 0 917 = 708892371 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229118) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem c229118_1 : rowSum f229118 917 107 = 1548774780 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229118) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem sum229118 : rowSum f229118 0 1024 = 2257667151 :=
  rowSum_append (F := f229118) (lo := 0) (n := 917) (m := 107) (A := 708892371) (B := 1548774780) c229118_0 (c229118_1)

theorem h229118 : P.leaf 36 229118 = 2257667151 :=
  leaf_weighted (k := 26) (d := 10) (H := 229118) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 229118) (by decide) (by decide +kernel)) sum229118

theorem cover229119 : P.CoversSplit 26 10 229119 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000330033000000000033003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229119 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (234617856 + i)

theorem c229119_0 : rowSum f229119 0 901 = 577202923 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229119) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229119 (by decide)
  decide +kernel

theorem c229119_1 : rowSum f229119 901 123 = 2028700540 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229119) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229119 (by decide)
  decide +kernel

theorem sum229119 : rowSum f229119 0 1024 = 2605903463 :=
  rowSum_append (F := f229119) (lo := 0) (n := 901) (m := 123) (A := 577202923) (B := 2028700540) c229119_0 (c229119_1)

theorem h229119 : P.leaf 36 229119 = 2605903463 :=
  leaf_weighted (k := 26) (d := 10) (H := 229119) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 229119) (by decide) (by decide +kernel)) sum229119

theorem cover229357 : P.CoversSplit 26 10 229357 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229357 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (234861568 + i)

theorem c229357_0 : rowSum f229357 0 375 = 568448920 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_1 : rowSum f229357 375 102 = 820518114 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_2 : rowSum f229357 477 394 = 1506346456 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_3 : rowSum f229357 871 153 = 1460878800 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem sum229357 : rowSum f229357 0 1024 = 4356192290 :=
  rowSum_append (F := f229357) (lo := 0) (n := 375) (m := 649) (A := 568448920) (B := 3787743370) c229357_0 (rowSum_append (F := f229357) (lo := 375) (n := 102) (m := 547) (A := 820518114) (B := 2967225256) c229357_1 (rowSum_append (F := f229357) (lo := 477) (n := 394) (m := 153) (A := 1506346456) (B := 1460878800) c229357_2 (c229357_3)))

theorem h229357 : P.leaf 36 229357 = 4356192290 :=
  leaf_weighted (k := 26) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 229357) (by decide) (by decide +kernel)) sum229357

theorem cover229359 : P.CoversSplit 26 10 229359 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229359 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (234863616 + i)

theorem c229359_0 : rowSum f229359 0 375 = 1104656816 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_1 : rowSum f229359 375 102 = 1377121678 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_2 : rowSum f229359 477 394 = 2362320240 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_3 : rowSum f229359 871 153 = 2066805856 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem sum229359 : rowSum f229359 0 1024 = 6910904590 :=
  rowSum_append (F := f229359) (lo := 0) (n := 375) (m := 649) (A := 1104656816) (B := 5806247774) c229359_0 (rowSum_append (F := f229359) (lo := 375) (n := 102) (m := 547) (A := 1377121678) (B := 4429126096) c229359_1 (rowSum_append (F := f229359) (lo := 477) (n := 394) (m := 153) (A := 2362320240) (B := 2066805856) c229359_2 (c229359_3)))

theorem h229359 : P.leaf 36 229359 = 6910904590 :=
  leaf_weighted (k := 26) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 229359) (by decide) (by decide +kernel)) sum229359

theorem cover229375 : P.CoversSplit 26 10 229375 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229375 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (234880000 + i)

theorem c229375_0 : rowSum f229375 0 210 = 15691871 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_1 : rowSum f229375 210 141 = 1064173732 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_2 : rowSum f229375 351 102 = 1751692646 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_3 : rowSum f229375 453 392 = 2503070276 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_4 : rowSum f229375 845 179 = 3479406872 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem sum229375 : rowSum f229375 0 1024 = 8814035397 :=
  rowSum_append (F := f229375) (lo := 0) (n := 210) (m := 814) (A := 15691871) (B := 8798343526) c229375_0 (rowSum_append (F := f229375) (lo := 210) (n := 141) (m := 673) (A := 1064173732) (B := 7734169794) c229375_1 (rowSum_append (F := f229375) (lo := 351) (n := 102) (m := 571) (A := 1751692646) (B := 5982477148) c229375_2 (rowSum_append (F := f229375) (lo := 453) (n := 392) (m := 179) (A := 2503070276) (B := 3479406872) c229375_3 (c229375_4))))

theorem h229375 : P.leaf 36 229375 = 8814035397 :=
  leaf_weighted (k := 26) (d := 10) (H := 229375) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 229375) (by decide) (by decide +kernel)) sum229375

def seg : List (ℕ × ℕ) := [(229103, 720), (229118, 360), (229119, 360), (229357, 180), (229359, 180), (229375, 60)]

theorem segOK : checkSeg 20 perms 229103 241500 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 229103 241500 1860 5687583176700 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5687583176700)
    (SegSum.cons (w := 720) h229103 (SegSum.cons (w := 360) h229118 (SegSum.cons (w := 360) h229119 (SegSum.cons (w := 180) h229357 (SegSum.cons (w := 180) h229359 (SegSum.cons (w := 60) h229375 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S97
