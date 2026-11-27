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

namespace RACert.S6N0.C0.S113

open RACert RACert.Problem

theorem cover229375 : P.CoversSplit 26 10 229375 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229375_0 : P.sumLeaves 26 234880000 119 = 8018015 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 0) (len := 119) (W := 8018015) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_1 : P.sumLeaves 26 234880119 104 = 9007104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 119) (len := 104) (W := 9007104) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_2 : P.sumLeaves 26 234880223 119 = 474630214 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 223) (len := 119) (W := 474630214) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_3 : P.sumLeaves 26 234880342 102 = 854594161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 342) (len := 102) (W := 854594161) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_4 : P.sumLeaves 26 234880444 111 = 914356384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 444) (len := 111) (W := 914356384) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_5 : P.sumLeaves 26 234880555 106 = 836047941 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 555) (len := 106) (W := 836047941) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_6 : P.sumLeaves 26 234880661 100 = 907315430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 661) (len := 100) (W := 907315430) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_7 : P.sumLeaves 26 234880761 117 = 1767038510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 761) (len := 117) (W := 1767038510) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_8 : P.sumLeaves 26 234880878 102 = 1999730430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 878) (len := 102) (W := 1999730430) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem c229375_9 : P.sumLeaves 26 234880980 44 = 1043297208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229375) (lo := 980) (len := 44) (W := 1043297208) check rows elimOK (by decide) (by decide) cover229375 (by decide)
  decide +kernel

theorem h229375 : P.leaf 36 229375 = 8814035397 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 8018015), (104, 9007104), (119, 474630214), (102, 854594161), (111, 914356384), (106, 836047941), (100, 907315430), (117, 1767038510), (102, 1999730430), (44, 1043297208)]) (.cons c229375_0 (.cons c229375_1 (.cons c229375_2 (.cons c229375_3 (.cons c229375_4 (.cons c229375_5 (.cons c229375_6 (.cons c229375_7 (.cons c229375_8 (.cons c229375_9 (.nil))))))))))) (by decide) (by decide))

theorem cover241500 : P.CoversSplit 26 10 241500 0xffffffffffffffffffffffffffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffff00ffffaaaaff00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241500_0 : P.sumLeaves 26 247296000 148 = 2321072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 0) (len := 148) (W := 2321072) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_1 : P.sumLeaves 26 247296148 104 = 4684256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 148) (len := 104) (W := 4684256) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_2 : P.sumLeaves 26 247296252 148 = 6132480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 252) (len := 148) (W := 6132480) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_3 : P.sumLeaves 26 247296400 96 = 11394048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 400) (len := 96) (W := 11394048) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_4 : P.sumLeaves 26 247296496 132 = 13650544 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 496) (len := 132) (W := 13650544) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_5 : P.sumLeaves 26 247296628 112 = 10272336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 628) (len := 112) (W := 10272336) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_6 : P.sumLeaves 26 247296740 132 = 21618848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 740) (len := 132) (W := 21618848) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_7 : P.sumLeaves 26 247296872 104 = 26570640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 872) (len := 104) (W := 26570640) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem c241500_8 : P.sumLeaves 26 247296976 48 = 45414784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241500) (lo := 976) (len := 48) (W := 45414784) check rows elimOK (by decide) (by decide) cover241500 (by decide)
  decide +kernel

theorem h241500 : P.leaf 36 241500 = 142059008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 2321072), (104, 4684256), (148, 6132480), (96, 11394048), (132, 13650544), (112, 10272336), (132, 21618848), (104, 26570640), (48, 45414784)]) (.cons c241500_0 (.cons c241500_1 (.cons c241500_2 (.cons c241500_3 (.cons c241500_4 (.cons c241500_5 (.cons c241500_6 (.cons c241500_7 (.cons c241500_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(229375, 60), (241500, 15)]

theorem segOK : checkSeg 20 perms 229375 241501 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 229375 241501 75 530973008940 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 530973008940)
    (SegSum.cons (w := 60) h229375 (SegSum.cons (w := 15) h241500 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S113
