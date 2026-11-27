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

namespace RACert.S6N0.C0.S116

open RACert RACert.Problem

theorem cover245758 : P.CoversSplit 26 10 245758 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88fffffffffffffffffffffffffffffafaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245758_0 : P.sumLeaves 26 251656192 126 = 131132164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 0) (len := 126) (W := 131132164) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_1 : P.sumLeaves 26 251656318 112 = 217992560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 126) (len := 112) (W := 217992560) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_2 : P.sumLeaves 26 251656430 126 = 506846268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 238) (len := 126) (W := 506846268) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_3 : P.sumLeaves 26 251656556 100 = 1138949705 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 364) (len := 100) (W := 1138949705) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_4 : P.sumLeaves 26 251656656 122 = 1159037856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 464) (len := 122) (W := 1159037856) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_5 : P.sumLeaves 26 251656778 112 = 945272366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 586) (len := 112) (W := 945272366) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_6 : P.sumLeaves 26 251656890 118 = 1382859166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 698) (len := 118) (W := 1382859166) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_7 : P.sumLeaves 26 251657008 104 = 1244505479 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 816) (len := 104) (W := 1244505479) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_8 : P.sumLeaves 26 251657112 96 = 1897555440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 920) (len := 96) (W := 1897555440) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem c245758_9 : P.sumLeaves 26 251657208 8 = 211864468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245758) (lo := 1016) (len := 8) (W := 211864468) check rows elimOK (by decide) (by decide) cover245758 (by decide)
  decide +kernel

theorem h245758 : P.leaf 36 245758 = 8836015472 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 131132164), (112, 217992560), (126, 506846268), (100, 1138949705), (122, 1159037856), (112, 945272366), (118, 1382859166), (104, 1244505479), (96, 1897555440), (8, 211864468)]) (.cons c245758_0 (.cons c245758_1 (.cons c245758_2 (.cons c245758_3 (.cons c245758_4 (.cons c245758_5 (.cons c245758_6 (.cons c245758_7 (.cons c245758_8 (.cons c245758_9 (.nil))))))))))) (by decide) (by decide))

theorem cover245759 : P.CoversSplit 26 10 245759 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88fffffffffffffffffffffffffffffafaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245759_0 : P.sumLeaves 26 251657216 126 = 594984808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 0) (len := 126) (W := 594984808) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_1 : P.sumLeaves 26 251657342 112 = 806935542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 126) (len := 112) (W := 806935542) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_2 : P.sumLeaves 26 251657454 126 = 1055011924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 238) (len := 126) (W := 1055011924) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_3 : P.sumLeaves 26 251657580 100 = 1509909689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 364) (len := 100) (W := 1509909689) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_4 : P.sumLeaves 26 251657680 122 = 1550689791 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 464) (len := 122) (W := 1550689791) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_5 : P.sumLeaves 26 251657802 112 = 1386682308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 586) (len := 112) (W := 1386682308) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_6 : P.sumLeaves 26 251657914 118 = 1735062429 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 698) (len := 118) (W := 1735062429) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_7 : P.sumLeaves 26 251658032 104 = 1721812929 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 816) (len := 104) (W := 1721812929) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_8 : P.sumLeaves 26 251658136 96 = 2256834746 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 920) (len := 96) (W := 2256834746) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem c245759_9 : P.sumLeaves 26 251658232 8 = 237344492 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245759) (lo := 1016) (len := 8) (W := 237344492) check rows elimOK (by decide) (by decide) cover245759 (by decide)
  decide +kernel

theorem h245759 : P.leaf 36 245759 = 12855268658 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 594984808), (112, 806935542), (126, 1055011924), (100, 1509909689), (122, 1550689791), (112, 1386682308), (118, 1735062429), (104, 1721812929), (96, 2256834746), (8, 237344492)]) (.cons c245759_0 (.cons c245759_1 (.cons c245759_2 (.cons c245759_3 (.cons c245759_4 (.cons c245759_5 (.cons c245759_6 (.cons c245759_7 (.cons c245759_8 (.cons c245759_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245758, 360), (245759, 360)]

theorem segOK : checkSeg 20 perms 245758 261091 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245758 261091 720 7808862286800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7808862286800)
    (SegSum.cons (w := 360) h245758 (SegSum.cons (w := 360) h245759 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S116
