/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S140

open RACert RACert.Problem

theorem cover261111 : P.CoversSplit 26 10 261111 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c261111_0 : P.sumLeaves 26 267377664 119 = 173699390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 0) (len := 119) (W := 173699390) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_1 : P.sumLeaves 26 267377783 104 = 203888604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 119) (len := 104) (W := 203888604) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_2 : P.sumLeaves 26 267377887 119 = 740947931 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 223) (len := 119) (W := 740947931) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_3 : P.sumLeaves 26 267378006 100 = 1204985621 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 342) (len := 100) (W := 1204985621) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_4 : P.sumLeaves 26 267378106 109 = 1361992743 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 442) (len := 109) (W := 1361992743) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_5 : P.sumLeaves 26 267378215 106 = 777974753 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 551) (len := 106) (W := 777974753) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_6 : P.sumLeaves 26 267378321 100 = 784443142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 657) (len := 100) (W := 784443142) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_7 : P.sumLeaves 26 267378421 115 = 1742903420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 757) (len := 115) (W := 1742903420) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_8 : P.sumLeaves 26 267378536 100 = 1953779890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 872) (len := 100) (W := 1953779890) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem c261111_9 : P.sumLeaves 26 267378636 52 = 1323856088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261111) (lo := 972) (len := 52) (W := 1323856088) check rows elimOK (by decide) (by decide) cover261111 (by decide)
  decide +kernel

theorem h261111 : P.leaf 36 261111 = 10268471582 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 173699390), (104, 203888604), (119, 740947931), (100, 1204985621), (109, 1361992743), (106, 777974753), (100, 784443142), (115, 1742903420), (100, 1953779890), (52, 1323856088)]) (.cons c261111_0 (.cons c261111_1 (.cons c261111_2 (.cons c261111_3 (.cons c261111_4 (.cons c261111_5 (.cons c261111_6 (.cons c261111_7 (.cons c261111_8 (.cons c261111_9 (.nil))))))))))) (by decide) (by decide))

theorem cover261117 : P.CoversSplit 26 10 261117 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c261117_0 : P.sumLeaves 26 267383808 119 = 145009720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 0) (len := 119) (W := 145009720) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_1 : P.sumLeaves 26 267383927 104 = 169691920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 119) (len := 104) (W := 169691920) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_2 : P.sumLeaves 26 267384031 119 = 477655165 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 223) (len := 119) (W := 477655165) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_3 : P.sumLeaves 26 267384150 100 = 764226428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 342) (len := 100) (W := 764226428) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_4 : P.sumLeaves 26 267384250 109 = 998363560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 442) (len := 109) (W := 998363560) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_5 : P.sumLeaves 26 267384359 106 = 766244024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 551) (len := 106) (W := 766244024) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_6 : P.sumLeaves 26 267384465 100 = 904466306 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 657) (len := 100) (W := 904466306) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_7 : P.sumLeaves 26 267384565 115 = 1216639150 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 757) (len := 115) (W := 1216639150) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_8 : P.sumLeaves 26 267384680 100 = 1379285840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 872) (len := 100) (W := 1379285840) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem c261117_9 : P.sumLeaves 26 267384780 52 = 1059402400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261117) (lo := 972) (len := 52) (W := 1059402400) check rows elimOK (by decide) (by decide) cover261117 (by decide)
  decide +kernel

theorem h261117 : P.leaf 36 261117 = 7880984513 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 145009720), (104, 169691920), (119, 477655165), (100, 764226428), (109, 998363560), (106, 766244024), (100, 904466306), (115, 1216639150), (100, 1379285840), (52, 1059402400)]) (.cons c261117_0 (.cons c261117_1 (.cons c261117_2 (.cons c261117_3 (.cons c261117_4 (.cons c261117_5 (.cons c261117_6 (.cons c261117_7 (.cons c261117_8 (.cons c261117_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(261111, 360), (261117, 360)]

theorem segOK : checkSeg 20 perms 261111 261119 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 261111 261119 720 6533804194200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6533804194200)
    (SegSum.cons (w := 360) h261111 (SegSum.cons (w := 360) h261117 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S140
