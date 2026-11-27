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

namespace RACert.S6N0.C0.S79

open RACert RACert.Problem

theorem cover98300 : P.CoversSplit 26 10 98300 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98300 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100659200 + i)

theorem c98300_0 : rowSum f98300 0 428 = 236752090 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98300) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_1 : rowSum f98300 428 186 = 398249660 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98300) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_2 : rowSum f98300 614 206 = 539180772 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98300) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_3 : rowSum f98300 820 198 = 999328174 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98300) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_4 : rowSum f98300 1018 6 = 100769776 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98300) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem sum98300 : rowSum f98300 0 1024 = 2274280472 :=
  rowSum_append (F := f98300) (lo := 0) (n := 428) (m := 596) (A := 236752090) (B := 2037528382) c98300_0 (rowSum_append (F := f98300) (lo := 428) (n := 186) (m := 410) (A := 398249660) (B := 1639278722) c98300_1 (rowSum_append (F := f98300) (lo := 614) (n := 206) (m := 204) (A := 539180772) (B := 1100097950) c98300_2 (rowSum_append (F := f98300) (lo := 820) (n := 198) (m := 6) (A := 999328174) (B := 100769776) c98300_3 (c98300_4))))

theorem h98300 : P.leaf 36 98300 = 2274280472 :=
  leaf_weighted (k := 26) (d := 10) (H := 98300) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98300) (by decide) (by decide +kernel)) sum98300

theorem cover98301 : P.CoversSplit 26 10 98301 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98301_0 : P.sumLeaves 26 100660224 387 = 220499446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 0) (len := 387) (W := 220499446) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_1 : P.sumLeaves 26 100660611 104 = 481966487 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 387) (len := 104) (W := 481966487) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_2 : P.sumLeaves 26 100660715 131 = 392221131 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 491) (len := 131) (W := 392221131) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_3 : P.sumLeaves 26 100660846 118 = 502600926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 622) (len := 118) (W := 502600926) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_4 : P.sumLeaves 26 100660964 129 = 578575690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 740) (len := 129) (W := 578575690) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_5 : P.sumLeaves 26 100661093 106 = 984023096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 869) (len := 106) (W := 984023096) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_6 : P.sumLeaves 26 100661199 49 = 726298394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 975) (len := 49) (W := 726298394) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem h98301 : P.leaf 36 98301 = 3886185170 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(387, 220499446), (104, 481966487), (131, 392221131), (118, 502600926), (129, 578575690), (106, 984023096), (49, 726298394)]) (.cons c98301_0 (.cons c98301_1 (.cons c98301_2 (.cons c98301_3 (.cons c98301_4 (.cons c98301_5 (.cons c98301_6 (.nil)))))))) (by decide) (by decide))

theorem cover98303 : P.CoversSplit 26 10 98303 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98303 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100662272 + i)

theorem c98303_0 : rowSum f98303 0 180 = 14122847 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_1 : rowSum f98303 180 188 = 701189812 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_2 : rowSum f98303 368 198 = 1120200645 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_3 : rowSum f98303 566 215 = 1250836692 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_4 : rowSum f98303 781 163 = 2245238134 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_5 : rowSum f98303 944 80 = 931315868 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem sum98303 : rowSum f98303 0 1024 = 6262903998 :=
  rowSum_append (F := f98303) (lo := 0) (n := 180) (m := 844) (A := 14122847) (B := 6248781151) c98303_0 (rowSum_append (F := f98303) (lo := 180) (n := 188) (m := 656) (A := 701189812) (B := 5547591339) c98303_1 (rowSum_append (F := f98303) (lo := 368) (n := 198) (m := 458) (A := 1120200645) (B := 4427390694) c98303_2 (rowSum_append (F := f98303) (lo := 566) (n := 215) (m := 243) (A := 1250836692) (B := 3176554002) c98303_3 (rowSum_append (F := f98303) (lo := 781) (n := 163) (m := 80) (A := 2245238134) (B := 931315868) c98303_4 (c98303_5)))))

theorem h98303 : P.leaf 36 98303 = 6262903998 :=
  leaf_weighted (k := 26) (d := 10) (H := 98303) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98303) (by decide) (by decide +kernel)) sum98303

def seg : List (ℕ × ℕ) := [(98300, 360), (98301, 720), (98303, 360)]

theorem segOK : checkSeg 20 perms 98300 119623 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98300 119623 1440 5871439731600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5871439731600)
    (SegSum.cons (w := 360) h98300 (SegSum.cons (w := 720) h98301 (SegSum.cons (w := 360) h98303 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S79
