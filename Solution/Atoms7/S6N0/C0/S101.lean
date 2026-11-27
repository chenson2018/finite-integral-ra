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

namespace RACert.S6N0.C0.S101

open RACert RACert.Problem

theorem cover241535 : P.CoversSplit 26 10 241535 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241535_0 : P.sumLeaves 26 247331840 148 = 192244615 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 0) (len := 148) (W := 192244615) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_1 : P.sumLeaves 26 247331988 104 = 279867689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 148) (len := 104) (W := 279867689) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_2 : P.sumLeaves 26 247332092 148 = 426827545 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 252) (len := 148) (W := 426827545) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_3 : P.sumLeaves 26 247332240 96 = 559472627 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 400) (len := 96) (W := 559472627) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_4 : P.sumLeaves 26 247332336 128 = 527423275 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 496) (len := 128) (W := 527423275) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_5 : P.sumLeaves 26 247332464 112 = 503141651 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 624) (len := 112) (W := 503141651) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_6 : P.sumLeaves 26 247332576 128 = 637843577 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 736) (len := 128) (W := 637843577) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_7 : P.sumLeaves 26 247332704 104 = 621120108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 864) (len := 104) (W := 621120108) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem c241535_8 : P.sumLeaves 26 247332808 56 = 650130321 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241535) (lo := 968) (len := 56) (W := 650130321) check rows elimOK (by decide) (by decide) cover241535 (by decide)
  decide +kernel

theorem h241535 : P.leaf 36 241535 = 4398071408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 192244615), (104, 279867689), (148, 426827545), (96, 559472627), (128, 527423275), (112, 503141651), (128, 637843577), (104, 621120108), (56, 650130321)]) (.cons c241535_0 (.cons c241535_1 (.cons c241535_2 (.cons c241535_3 (.cons c241535_4 (.cons c241535_5 (.cons c241535_6 (.cons c241535_7 (.cons c241535_8 (.nil)))))))))) (by decide) (by decide))

theorem cover241643 : P.CoversSplit 26 10 241643 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffffffffffaaaaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f241643 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (247442432 + i)

theorem c241643_0 : rowSum f241643 0 178 = 87379633 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_1 : rowSum f241643 178 186 = 253094230 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_2 : rowSum f241643 364 198 = 615739475 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_3 : rowSum f241643 562 200 = 698455172 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_4 : rowSum f241643 762 166 = 733886262 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_5 : rowSum f241643 928 96 = 769468648 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem sum241643 : rowSum f241643 0 1024 = 3158023420 :=
  rowSum_append (F := f241643) (lo := 0) (n := 178) (m := 846) (A := 87379633) (B := 3070643787) c241643_0 (rowSum_append (F := f241643) (lo := 178) (n := 186) (m := 660) (A := 253094230) (B := 2817549557) c241643_1 (rowSum_append (F := f241643) (lo := 364) (n := 198) (m := 462) (A := 615739475) (B := 2201810082) c241643_2 (rowSum_append (F := f241643) (lo := 562) (n := 200) (m := 262) (A := 698455172) (B := 1503354910) c241643_3 (rowSum_append (F := f241643) (lo := 762) (n := 166) (m := 96) (A := 733886262) (B := 769468648) c241643_4 (c241643_5)))))

theorem h241643 : P.leaf 36 241643 = 3158023420 :=
  leaf_weighted (k := 26) (d := 10) (H := 241643) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 241643) (by decide) (by decide +kernel)) sum241643

theorem cover241647 : P.CoversSplit 26 10 241647 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffffffffffaaaaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f241647 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (247446528 + i)

theorem c241647_0 : rowSum f241647 0 178 = 335806722 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_1 : rowSum f241647 178 186 = 628813627 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_2 : rowSum f241647 364 198 = 1190344844 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_3 : rowSum f241647 562 200 = 987606929 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_4 : rowSum f241647 762 166 = 999615024 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_5 : rowSum f241647 928 96 = 1078416070 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem sum241647 : rowSum f241647 0 1024 = 5220603216 :=
  rowSum_append (F := f241647) (lo := 0) (n := 178) (m := 846) (A := 335806722) (B := 4884796494) c241647_0 (rowSum_append (F := f241647) (lo := 178) (n := 186) (m := 660) (A := 628813627) (B := 4255982867) c241647_1 (rowSum_append (F := f241647) (lo := 364) (n := 198) (m := 462) (A := 1190344844) (B := 3065638023) c241647_2 (rowSum_append (F := f241647) (lo := 562) (n := 200) (m := 262) (A := 987606929) (B := 2078031094) c241647_3 (rowSum_append (F := f241647) (lo := 762) (n := 166) (m := 96) (A := 999615024) (B := 1078416070) c241647_4 (c241647_5)))))

theorem h241647 : P.leaf 36 241647 = 5220603216 :=
  leaf_weighted (k := 26) (d := 10) (H := 241647) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 241647) (by decide) (by decide +kernel)) sum241647

def seg : List (ℕ × ℕ) := [(241535, 360), (241643, 90), (241647, 180)]

theorem segOK : checkSeg 20 perms 241535 241663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241535 241663 630 2807236393560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2807236393560)
    (SegSum.cons (w := 360) h241535 (SegSum.cons (w := 90) h241643 (SegSum.cons (w := 180) h241647 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S101
