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

theorem cover385022 : P.CoversSplit 26 10 385022 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f385022 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (394262528 + i)

theorem c385022_0 : rowSum f385022 0 229 = 851382748 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385022) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385022 (by decide)
  decide +kernel

theorem c385022_1 : rowSum f385022 229 158 = 1333349688 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385022) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385022 (by decide)
  decide +kernel

theorem c385022_2 : rowSum f385022 387 96 = 2223215838 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385022) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385022 (by decide)
  decide +kernel

theorem c385022_3 : rowSum f385022 483 395 = 2565391358 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385022) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385022 (by decide)
  decide +kernel

theorem c385022_4 : rowSum f385022 878 146 = 1862675840 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385022) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385022 (by decide)
  decide +kernel

theorem sum385022 : rowSum f385022 0 1024 = 8836015472 :=
  rowSum_append (F := f385022) (lo := 0) (n := 229) (m := 795) (A := 851382748) (B := 7984632724) c385022_0 (rowSum_append (F := f385022) (lo := 229) (n := 158) (m := 637) (A := 1333349688) (B := 6651283036) c385022_1 (rowSum_append (F := f385022) (lo := 387) (n := 96) (m := 541) (A := 2223215838) (B := 4428067198) c385022_2 (rowSum_append (F := f385022) (lo := 483) (n := 395) (m := 146) (A := 2565391358) (B := 1862675840) c385022_3 (c385022_4))))

theorem h385022 : P.leaf 36 385022 = 8836015472 :=
  leaf_weighted (k := 26) (d := 10) (H := 385022) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 385022) (by decide) (by decide +kernel)) sum385022

theorem h245758 : P.leaf 36 245758 = 8836015472 :=
  orient6 (v := 385022) (by decide) (by decide +kernel) h385022

theorem cover385023 : P.CoversSplit 26 10 385023 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f385023 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (394263552 + i)

theorem c385023_0 : rowSum f385023 0 229 = 1954479673 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385023) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385023 (by decide)
  decide +kernel

theorem c385023_1 : rowSum f385023 229 158 = 2555037756 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385023) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385023 (by decide)
  decide +kernel

theorem c385023_2 : rowSum f385023 387 96 = 2809152490 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385023) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385023 (by decide)
  decide +kernel

theorem c385023_3 : rowSum f385023 483 395 = 3330029497 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385023) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385023 (by decide)
  decide +kernel

theorem c385023_4 : rowSum f385023 878 146 = 2206569242 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385023) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385023 (by decide)
  decide +kernel

theorem sum385023 : rowSum f385023 0 1024 = 12855268658 :=
  rowSum_append (F := f385023) (lo := 0) (n := 229) (m := 795) (A := 1954479673) (B := 10900788985) c385023_0 (rowSum_append (F := f385023) (lo := 229) (n := 158) (m := 637) (A := 2555037756) (B := 8345751229) c385023_1 (rowSum_append (F := f385023) (lo := 387) (n := 96) (m := 541) (A := 2809152490) (B := 5536598739) c385023_2 (rowSum_append (F := f385023) (lo := 483) (n := 395) (m := 146) (A := 3330029497) (B := 2206569242) c385023_3 (c385023_4))))

theorem h385023 : P.leaf 36 385023 = 12855268658 :=
  leaf_weighted (k := 26) (d := 10) (H := 385023) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 385023) (by decide) (by decide +kernel)) sum385023

theorem h245759 : P.leaf 36 245759 = 12855268658 :=
  orient6 (v := 385023) (by decide) (by decide +kernel) h385023

theorem cover261091 : P.CoversSplit 26 10 261091 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1266]) (by decide +kernel)

noncomputable def f261091 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (267357184 + i)

theorem c261091_0 : rowSum f261091 0 375 = 435438458 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261091) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_1 : rowSum f261091 375 104 = 663829002 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261091) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_2 : rowSum f261091 479 396 = 964889180 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261091) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_3 : rowSum f261091 875 149 = 1016141928 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261091) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem sum261091 : rowSum f261091 0 1024 = 3080298568 :=
  rowSum_append (F := f261091) (lo := 0) (n := 375) (m := 649) (A := 435438458) (B := 2644860110) c261091_0 (rowSum_append (F := f261091) (lo := 375) (n := 104) (m := 545) (A := 663829002) (B := 1981031108) c261091_1 (rowSum_append (F := f261091) (lo := 479) (n := 396) (m := 149) (A := 964889180) (B := 1016141928) c261091_2 (c261091_3)))

theorem h261091 : P.leaf 36 261091 = 3080298568 :=
  leaf_weighted (k := 26) (d := 10) (H := 261091) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 261091) (by decide) (by decide +kernel)) sum261091

theorem cover261095 : P.CoversSplit 26 10 261095 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261095 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (267361280 + i)

theorem c261095_0 : rowSum f261095 0 434 = 1097937770 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261095) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_1 : rowSum f261095 434 191 = 1065702684 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261095) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_2 : rowSum f261095 625 226 = 1467777460 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261095) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_3 : rowSum f261095 851 173 = 2035812964 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261095) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem sum261095 : rowSum f261095 0 1024 = 5667230878 :=
  rowSum_append (F := f261095) (lo := 0) (n := 434) (m := 590) (A := 1097937770) (B := 4569293108) c261095_0 (rowSum_append (F := f261095) (lo := 434) (n := 191) (m := 399) (A := 1065702684) (B := 3503590424) c261095_1 (rowSum_append (F := f261095) (lo := 625) (n := 226) (m := 173) (A := 1467777460) (B := 2035812964) c261095_2 (c261095_3)))

theorem h261095 : P.leaf 36 261095 = 5667230878 :=
  leaf_weighted (k := 26) (d := 10) (H := 261095) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 261095) (by decide) (by decide +kernel)) sum261095

def seg : List (ℕ × ℕ) := [(245758, 360), (245759, 360), (261091, 30), (261095, 180)]

theorem segOK : checkSeg 20 perms 245758 261103 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245758 261103 930 8921372801880 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 8921372801880)
    (SegSum.cons (w := 360) h245758 (SegSum.cons (w := 360) h245759 (SegSum.cons (w := 30) h261091 (SegSum.cons (w := 180) h261095 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S97
