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

namespace RACert.S6N0.C0.S141

open RACert RACert.Problem

theorem cover261119 : P.CoversSplit 26 10 261119 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c261119_0 : P.sumLeaves 26 267385856 119 = 672206419 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 0) (len := 119) (W := 672206419) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_1 : P.sumLeaves 26 267385975 104 = 757488852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 119) (len := 104) (W := 757488852) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_2 : P.sumLeaves 26 267386079 119 = 1235421248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 223) (len := 119) (W := 1235421248) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_3 : P.sumLeaves 26 267386198 100 = 1533166803 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 342) (len := 100) (W := 1533166803) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_4 : P.sumLeaves 26 267386298 109 = 1711703083 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 442) (len := 109) (W := 1711703083) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_5 : P.sumLeaves 26 267386407 106 = 1543801899 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 551) (len := 106) (W := 1543801899) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_6 : P.sumLeaves 26 267386513 100 = 1654888694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 657) (len := 100) (W := 1654888694) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_7 : P.sumLeaves 26 267386613 115 = 2226327274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 757) (len := 115) (W := 2226327274) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_8 : P.sumLeaves 26 267386728 100 = 2422971744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 872) (len := 100) (W := 2422971744) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem c261119_9 : P.sumLeaves 26 267386828 52 = 1529497504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261119) (lo := 972) (len := 52) (W := 1529497504) check rows elimOK (by decide) (by decide) cover261119 (by decide)
  decide +kernel

theorem h261119 : P.leaf 36 261119 = 15287473520 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 672206419), (104, 757488852), (119, 1235421248), (100, 1533166803), (109, 1711703083), (106, 1543801899), (100, 1654888694), (115, 2226327274), (100, 2422971744), (52, 1529497504)]) (.cons c261119_0 (.cons c261119_1 (.cons c261119_2 (.cons c261119_3 (.cons c261119_4 (.cons c261119_5 (.cons c261119_6 (.cons c261119_7 (.cons c261119_8 (.cons c261119_9 (.nil))))))))))) (by decide) (by decide))

theorem cover262135 : P.CoversSplit 26 10 262135 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c262135_0 : P.sumLeaves 26 268426240 119 = 213040048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 0) (len := 119) (W := 213040048) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_1 : P.sumLeaves 26 268426359 104 = 258040384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 119) (len := 104) (W := 258040384) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_2 : P.sumLeaves 26 268426463 119 = 864511495 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 223) (len := 119) (W := 864511495) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_3 : P.sumLeaves 26 268426582 100 = 1441875071 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 342) (len := 100) (W := 1441875071) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_4 : P.sumLeaves 26 268426682 109 = 1630144130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 442) (len := 109) (W := 1630144130) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_5 : P.sumLeaves 26 268426791 106 = 911630612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 551) (len := 106) (W := 911630612) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_6 : P.sumLeaves 26 268426897 100 = 924053954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 657) (len := 100) (W := 924053954) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_7 : P.sumLeaves 26 268426997 115 = 1889278856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 757) (len := 115) (W := 1889278856) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_8 : P.sumLeaves 26 268427112 100 = 2097959924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 872) (len := 100) (W := 2097959924) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem c262135_9 : P.sumLeaves 26 268427212 52 = 1422689080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262135) (lo := 972) (len := 52) (W := 1422689080) check rows elimOK (by decide) (by decide) cover262135 (by decide)
  decide +kernel

theorem h262135 : P.leaf 36 262135 = 11653223554 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 213040048), (104, 258040384), (119, 864511495), (100, 1441875071), (109, 1630144130), (106, 911630612), (100, 924053954), (115, 1889278856), (100, 2097959924), (52, 1422689080)]) (.cons c262135_0 (.cons c262135_1 (.cons c262135_2 (.cons c262135_3 (.cons c262135_4 (.cons c262135_5 (.cons c262135_6 (.cons c262135_7 (.cons c262135_8 (.cons c262135_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(261119, 180), (262135, 180)]

theorem segOK : checkSeg 20 perms 261119 262140 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 261119 262140 360 4849325473320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4849325473320)
    (SegSum.cons (w := 180) h261119 (SegSum.cons (w := 180) h262135 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S141
