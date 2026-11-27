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

namespace RACert.S6N0.C0.S139

open RACert RACert.Problem

theorem cover261091 : P.CoversSplit 26 10 261091 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1266]) (by decide +kernel)

theorem c261091_0 : P.sumLeaves 26 267357184 375 = 217719229 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 0) (len := 375) (W := 217719229) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_1 : P.sumLeaves 26 267357559 104 = 331914501 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 375) (len := 104) (W := 331914501) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_2 : P.sumLeaves 26 267357663 119 = 317102332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 479) (len := 119) (W := 317102332) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_3 : P.sumLeaves 26 267357782 104 = 286334254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 598) (len := 104) (W := 286334254) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_4 : P.sumLeaves 26 267357886 111 = 398444188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 702) (len := 111) (W := 398444188) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_5 : P.sumLeaves 26 267357997 108 = 632797248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 813) (len := 108) (W := 632797248) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_6 : P.sumLeaves 26 267358105 100 = 858536816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 921) (len := 100) (W := 858536816) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem c261091_7 : P.sumLeaves 26 267358205 3 = 37450000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261091) (lo := 1021) (len := 3) (W := 37450000) check rows elimOK (by decide) (by decide) cover261091 (by decide)
  decide +kernel

theorem h261091 : P.leaf 36 261091 = 3080298568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(375, 217719229), (104, 331914501), (119, 317102332), (104, 286334254), (111, 398444188), (108, 632797248), (100, 858536816), (3, 37450000)]) (.cons c261091_0 (.cons c261091_1 (.cons c261091_2 (.cons c261091_3 (.cons c261091_4 (.cons c261091_5 (.cons c261091_6 (.cons c261091_7 (.nil))))))))) (by decide) (by decide))

theorem cover261095 : P.CoversSplit 26 10 261095 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c261095_0 : P.sumLeaves 26 267361280 375 = 461482586 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 0) (len := 375) (W := 461482586) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_1 : P.sumLeaves 26 267361655 100 = 725209026 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 375) (len := 100) (W := 725209026) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_2 : P.sumLeaves 26 267361755 115 = 668544384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 475) (len := 115) (W := 668544384) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_3 : P.sumLeaves 26 267361870 104 = 383293678 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 590) (len := 104) (W := 383293678) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_4 : P.sumLeaves 26 267361974 109 = 616950734 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 694) (len := 109) (W := 616950734) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_5 : P.sumLeaves 26 267362083 106 = 1096131724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 803) (len := 106) (W := 1096131724) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_6 : P.sumLeaves 26 267362189 96 = 1284128570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 909) (len := 96) (W := 1284128570) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem c261095_7 : P.sumLeaves 26 267362285 19 = 431490176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261095) (lo := 1005) (len := 19) (W := 431490176) check rows elimOK (by decide) (by decide) cover261095 (by decide)
  decide +kernel

theorem h261095 : P.leaf 36 261095 = 5667230878 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(375, 461482586), (100, 725209026), (115, 668544384), (104, 383293678), (109, 616950734), (106, 1096131724), (96, 1284128570), (19, 431490176)]) (.cons c261095_0 (.cons c261095_1 (.cons c261095_2 (.cons c261095_3 (.cons c261095_4 (.cons c261095_5 (.cons c261095_6 (.cons c261095_7 (.nil))))))))) (by decide) (by decide))

theorem cover261103 : P.CoversSplit 26 10 261103 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c261103_0 : P.sumLeaves 26 267369472 375 = 584488582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 0) (len := 375) (W := 584488582) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_1 : P.sumLeaves 26 267369847 100 = 828587231 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 375) (len := 100) (W := 828587231) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_2 : P.sumLeaves 26 267369947 115 = 874554608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 475) (len := 115) (W := 874554608) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_3 : P.sumLeaves 26 267370062 104 = 728307049 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 590) (len := 104) (W := 728307049) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_4 : P.sumLeaves 26 267370166 109 = 1047078166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 694) (len := 109) (W := 1047078166) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_5 : P.sumLeaves 26 267370275 106 = 1237327788 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 803) (len := 106) (W := 1237327788) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_6 : P.sumLeaves 26 267370381 96 = 1445128010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 909) (len := 96) (W := 1445128010) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem c261103_7 : P.sumLeaves 26 267370477 19 = 477117608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 261103) (lo := 1005) (len := 19) (W := 477117608) check rows elimOK (by decide) (by decide) cover261103 (by decide)
  decide +kernel

theorem h261103 : P.leaf 36 261103 = 7222589042 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(375, 584488582), (100, 828587231), (115, 874554608), (104, 728307049), (109, 1047078166), (106, 1237327788), (96, 1445128010), (19, 477117608)]) (.cons c261103_0 (.cons c261103_1 (.cons c261103_2 (.cons c261103_3 (.cons c261103_4 (.cons c261103_5 (.cons c261103_6 (.cons c261103_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(261091, 30), (261095, 180), (261103, 90)]

theorem segOK : checkSeg 20 perms 261091 261111 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 261091 261111 300 1762543528860 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1762543528860)
    (SegSum.cons (w := 30) h261091 (SegSum.cons (w := 180) h261095 (SegSum.cons (w := 90) h261103 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S139
