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

namespace RACert.S6N0.C0.S98

open RACert RACert.Problem

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
  leaf_weighted (k := 26) (d := 10) (H := 261103) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 261103) (by decide) (by decide +kernel)) sum261103

theorem cover819197 : P.CoversSplit 26 10 819197 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f819197 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (838857728 + i)

theorem c819197_0 : rowSum f819197 0 210 = 1347961003 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819197) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819197 (by decide)
  decide +kernel

theorem c819197_1 : rowSum f819197 210 141 = 1760553945 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819197) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819197 (by decide)
  decide +kernel

theorem c819197_2 : rowSum f819197 351 104 = 2285304118 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819197) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819197 (by decide)
  decide +kernel

theorem c819197_3 : rowSum f819197 455 392 = 2484492710 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819197) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819197 (by decide)
  decide +kernel

theorem c819197_4 : rowSum f819197 847 177 = 2390159806 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819197) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819197 (by decide)
  decide +kernel

theorem sum819197 : rowSum f819197 0 1024 = 10268471582 :=
  rowSum_append (F := f819197) (lo := 0) (n := 210) (m := 814) (A := 1347961003) (B := 8920510579) c819197_0 (rowSum_append (F := f819197) (lo := 210) (n := 141) (m := 673) (A := 1760553945) (B := 7159956634) c819197_1 (rowSum_append (F := f819197) (lo := 351) (n := 104) (m := 569) (A := 2285304118) (B := 4874652516) c819197_2 (rowSum_append (F := f819197) (lo := 455) (n := 392) (m := 177) (A := 2484492710) (B := 2390159806) c819197_3 (c819197_4))))

theorem h819197 : P.leaf 36 819197 = 10268471582 :=
  leaf_weighted (k := 26) (d := 10) (H := 819197) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 819197) (by decide) (by decide +kernel)) sum819197

theorem h261111 : P.leaf 36 261111 = 10268471582 :=
  orient80 (v := 819197) (by decide) (by decide +kernel) h819197

theorem cover261117 : P.CoversSplit 26 10 261117 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261117 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (267383808 + i)

theorem c261117_0 : rowSum f261117 0 210 = 290000145 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_1 : rowSum f261117 210 141 = 1032514316 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_2 : rowSum f261117 351 100 = 1597389168 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_3 : rowSum f261117 451 392 = 2234511784 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_4 : rowSum f261117 843 181 = 2726569100 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem sum261117 : rowSum f261117 0 1024 = 7880984513 :=
  rowSum_append (F := f261117) (lo := 0) (n := 210) (m := 814) (A := 290000145) (B := 7590984368) c261117_0 (rowSum_append (F := f261117) (lo := 210) (n := 141) (m := 673) (A := 1032514316) (B := 6558470052) c261117_1 (rowSum_append (F := f261117) (lo := 351) (n := 100) (m := 573) (A := 1597389168) (B := 4961080884) c261117_2 (rowSum_append (F := f261117) (lo := 451) (n := 392) (m := 181) (A := 2234511784) (B := 2726569100) c261117_3 (c261117_4))))

theorem h261117 : P.leaf 36 261117 = 7880984513 :=
  leaf_weighted (k := 26) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 261117) (by decide) (by decide +kernel)) sum261117

theorem cover819199 : P.CoversSplit 26 10 819199 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f819199 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (838859776 + i)

theorem c819199_0 : rowSum f819199 0 210 = 2190593064 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819199) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819199 (by decide)
  decide +kernel

theorem c819199_1 : rowSum f819199 210 141 = 2747236730 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819199) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819199 (by decide)
  decide +kernel

theorem c819199_2 : rowSum f819199 351 104 = 3377570552 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819199) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819199 (by decide)
  decide +kernel

theorem c819199_3 : rowSum f819199 455 392 = 3663333792 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819199) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819199 (by decide)
  decide +kernel

theorem c819199_4 : rowSum f819199 847 177 = 3308739382 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 819199) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover819199 (by decide)
  decide +kernel

theorem sum819199 : rowSum f819199 0 1024 = 15287473520 :=
  rowSum_append (F := f819199) (lo := 0) (n := 210) (m := 814) (A := 2190593064) (B := 13096880456) c819199_0 (rowSum_append (F := f819199) (lo := 210) (n := 141) (m := 673) (A := 2747236730) (B := 10349643726) c819199_1 (rowSum_append (F := f819199) (lo := 351) (n := 104) (m := 569) (A := 3377570552) (B := 6972073174) c819199_2 (rowSum_append (F := f819199) (lo := 455) (n := 392) (m := 177) (A := 3663333792) (B := 3308739382) c819199_3 (c819199_4))))

theorem h819199 : P.leaf 36 819199 = 15287473520 :=
  leaf_weighted (k := 26) (d := 10) (H := 819199) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 819199) (by decide) (by decide +kernel)) sum819199

theorem h261119 : P.leaf 36 261119 = 15287473520 :=
  orient80 (v := 819199) (by decide) (by decide +kernel) h819199

def seg : List (ℕ × ℕ) := [(261103, 90), (261111, 360), (261117, 360), (261119, 180)]

theorem segOK : checkSeg 20 perms 261103 262135 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 261103 262135 990 9935582441580 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9935582441580)
    (SegSum.cons (w := 90) h261103 (SegSum.cons (w := 360) h261111 (SegSum.cons (w := 360) h261117 (SegSum.cons (w := 180) h261119 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S98
