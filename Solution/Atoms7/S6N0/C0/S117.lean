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

namespace RACert.S6N0.C0.S117

open RACert RACert.Problem

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
  leaf_weighted (k := 26) (d := 10) (H := 261091) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 261091) (by decide) (by decide +kernel)) sum261091

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
  leaf_weighted (k := 26) (d := 10) (H := 261095) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 261095) (by decide) (by decide +kernel)) sum261095

theorem cover261103 : P.CoversSplit 26 10 261103 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261103 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (267369472 + i)

theorem c261103_0 : rowSum f261103 0 375 = 1168977164 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_1 : rowSum f261103 375 100 = 1657174462 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_2 : rowSum f261103 475 392 = 2282912488 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_3 : rowSum f261103 867 157 = 2113524928 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261103) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem sum261103 : rowSum f261103 0 1024 = 7222589042 :=
  rowSum_append (F := f261103) (lo := 0) (n := 375) (m := 649) (A := 1168977164) (B := 6053611878) c261103_0 (rowSum_append (F := f261103) (lo := 375) (n := 100) (m := 549) (A := 1657174462) (B := 4396437416) c261103_1 (rowSum_append (F := f261103) (lo := 475) (n := 392) (m := 157) (A := 2282912488) (B := 2113524928) c261103_2 (c261103_3)))

theorem h261103 : P.leaf 36 261103 = 7222589042 :=
  leaf_weighted (k := 26) (d := 10) (H := 261103) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 261103) (by decide) (by decide +kernel)) sum261103

theorem cover261111 : P.CoversSplit 26 10 261111 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261111 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (267377664 + i)

theorem c261111_0 : rowSum f261111 0 165 = 322796762 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_1 : rowSum f261111 165 181 = 1172484397 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_2 : rowSum f261111 346 185 = 2076249019 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_3 : rowSum f261111 531 154 = 1346434258 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_4 : rowSum f261111 685 175 = 2396558958 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_5 : rowSum f261111 860 164 = 2953948188 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem sum261111 : rowSum f261111 0 1024 = 10268471582 :=
  rowSum_append (F := f261111) (lo := 0) (n := 165) (m := 859) (A := 322796762) (B := 9945674820) c261111_0 (rowSum_append (F := f261111) (lo := 165) (n := 181) (m := 678) (A := 1172484397) (B := 8773190423) c261111_1 (rowSum_append (F := f261111) (lo := 346) (n := 185) (m := 493) (A := 2076249019) (B := 6696941404) c261111_2 (rowSum_append (F := f261111) (lo := 531) (n := 154) (m := 339) (A := 1346434258) (B := 5350507146) c261111_3 (rowSum_append (F := f261111) (lo := 685) (n := 175) (m := 164) (A := 2396558958) (B := 2953948188) c261111_4 (c261111_5)))))

theorem h261111 : P.leaf 36 261111 = 10268471582 :=
  leaf_weighted (k := 26) (d := 10) (H := 261111) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 261111) (by decide) (by decide +kernel)) sum261111

def seg : List (ℕ × ℕ) := [(261091, 30), (261095, 180), (261103, 90), (261111, 360)]

theorem segOK : checkSeg 20 perms 261091 261117 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 261091 261117 660 5459193298380 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5459193298380)
    (SegSum.cons (w := 30) h261091 (SegSum.cons (w := 180) h261095 (SegSum.cons (w := 90) h261103 (SegSum.cons (w := 360) h261111 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S117
