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

namespace RACert.S6N0.C0.S118

open RACert RACert.Problem

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
  leaf_weighted (k := 26) (d := 10) (H := 261117) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 261117) (by decide) (by decide +kernel)) sum261117

theorem cover261119 : P.CoversSplit 26 10 261119 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261119 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (267385856 + i)

theorem c261119_0 : rowSum f261119 0 210 = 1319322132 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_1 : rowSum f261119 210 141 = 2531135888 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_2 : rowSum f261119 351 100 = 3132136370 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_3 : rowSum f261119 451 392 = 3830122598 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_4 : rowSum f261119 843 181 = 4474756532 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem sum261119 : rowSum f261119 0 1024 = 15287473520 :=
  rowSum_append (F := f261119) (lo := 0) (n := 210) (m := 814) (A := 1319322132) (B := 13968151388) c261119_0 (rowSum_append (F := f261119) (lo := 210) (n := 141) (m := 673) (A := 2531135888) (B := 11437015500) c261119_1 (rowSum_append (F := f261119) (lo := 351) (n := 100) (m := 573) (A := 3132136370) (B := 8304879130) c261119_2 (rowSum_append (F := f261119) (lo := 451) (n := 392) (m := 181) (A := 3830122598) (B := 4474756532) c261119_3 (c261119_4))))

theorem h261119 : P.leaf 36 261119 = 15287473520 :=
  leaf_weighted (k := 26) (d := 10) (H := 261119) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 261119) (by decide) (by decide +kernel)) sum261119

theorem cover262135 : P.CoversSplit 26 10 262135 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f262135 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (268426240 + i)

theorem c262135_0 : rowSum f262135 0 181 = 451021712 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262135) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_1 : rowSum f262135 181 194 = 2085951304 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262135) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_2 : rowSum f262135 375 224 = 2505074564 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262135) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_3 : rowSum f262135 599 215 = 2288260544 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262135) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_4 : rowSum f262135 814 210 = 4322915430 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262135) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem sum262135 : rowSum f262135 0 1024 = 11653223554 :=
  rowSum_append (F := f262135) (lo := 0) (n := 181) (m := 843) (A := 451021712) (B := 11202201842) c262135_0 (rowSum_append (F := f262135) (lo := 181) (n := 194) (m := 649) (A := 2085951304) (B := 9116250538) c262135_1 (rowSum_append (F := f262135) (lo := 375) (n := 224) (m := 425) (A := 2505074564) (B := 6611175974) c262135_2 (rowSum_append (F := f262135) (lo := 599) (n := 215) (m := 210) (A := 2288260544) (B := 4322915430) c262135_3 (c262135_4))))

theorem h262135 : P.leaf 36 262135 = 11653223554 :=
  leaf_weighted (k := 26) (d := 10) (H := 262135) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 262135) (by decide) (by decide +kernel)) sum262135

def seg : List (ℕ × ℕ) := [(261117, 360), (261119, 180), (262135, 180)]

theorem segOK : checkSeg 20 perms 261117 262140 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 261117 262140 720 7686479898000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7686479898000)
    (SegSum.cons (w := 360) h261117 (SegSum.cons (w := 180) h261119 (SegSum.cons (w := 180) h262135 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S118
