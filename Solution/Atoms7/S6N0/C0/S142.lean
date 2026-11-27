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

namespace RACert.S6N0.C0.S142

open RACert RACert.Problem

theorem cover262140 : P.CoversSplit 26 10 262140 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c262140_0 : P.sumLeaves 26 268431360 119 = 43865976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 0) (len := 119) (W := 43865976) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_1 : P.sumLeaves 26 268431479 104 = 49558552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 119) (len := 104) (W := 49558552) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_2 : P.sumLeaves 26 268431583 119 = 462635630 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 223) (len := 119) (W := 462635630) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_3 : P.sumLeaves 26 268431702 100 = 850508800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 342) (len := 100) (W := 850508800) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_4 : P.sumLeaves 26 268431802 109 = 1049355078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 442) (len := 109) (W := 1049355078) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_5 : P.sumLeaves 26 268431911 106 = 847111512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 551) (len := 106) (W := 847111512) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_6 : P.sumLeaves 26 268432017 100 = 971365360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 657) (len := 100) (W := 971365360) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_7 : P.sumLeaves 26 268432117 115 = 1287767676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 757) (len := 115) (W := 1287767676) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_8 : P.sumLeaves 26 268432232 100 = 1467918352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 872) (len := 100) (W := 1467918352) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_9 : P.sumLeaves 26 268432332 52 = 1082024136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262140) (lo := 972) (len := 52) (W := 1082024136) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem h262140 : P.leaf 36 262140 = 8112111072 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 43865976), (104, 49558552), (119, 462635630), (100, 850508800), (109, 1049355078), (106, 847111512), (100, 971365360), (115, 1287767676), (100, 1467918352), (52, 1082024136)]) (.cons c262140_0 (.cons c262140_1 (.cons c262140_2 (.cons c262140_3 (.cons c262140_4 (.cons c262140_5 (.cons c262140_6 (.cons c262140_7 (.cons c262140_8 (.cons c262140_9 (.nil))))))))))) (by decide) (by decide))

theorem cover262141 : P.CoversSplit 26 10 262141 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c262141_0 : P.sumLeaves 26 268432384 119 = 209738504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 0) (len := 119) (W := 209738504) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_1 : P.sumLeaves 26 268432503 104 = 239656552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 119) (len := 104) (W := 239656552) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_2 : P.sumLeaves 26 268432607 119 = 863747610 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 223) (len := 119) (W := 863747610) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_3 : P.sumLeaves 26 268432726 100 = 1371364070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 342) (len := 100) (W := 1371364070) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_4 : P.sumLeaves 26 268432826 109 = 1495794598 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 442) (len := 109) (W := 1495794598) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_5 : P.sumLeaves 26 268432935 106 = 1352611804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 551) (len := 106) (W := 1352611804) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_6 : P.sumLeaves 26 268433041 100 = 1433272498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 657) (len := 100) (W := 1433272498) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_7 : P.sumLeaves 26 268433141 115 = 1913437894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 757) (len := 115) (W := 1913437894) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_8 : P.sumLeaves 26 268433256 100 = 2051304370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 872) (len := 100) (W := 2051304370) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_9 : P.sumLeaves 26 268433356 52 = 1310825080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262141) (lo := 972) (len := 52) (W := 1310825080) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem h262141 : P.leaf 36 262141 = 12241752980 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 209738504), (104, 239656552), (119, 863747610), (100, 1371364070), (109, 1495794598), (106, 1352611804), (100, 1433272498), (115, 1913437894), (100, 2051304370), (52, 1310825080)]) (.cons c262141_0 (.cons c262141_1 (.cons c262141_2 (.cons c262141_3 (.cons c262141_4 (.cons c262141_5 (.cons c262141_6 (.cons c262141_7 (.cons c262141_8 (.cons c262141_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(262140, 45), (262141, 180)]

theorem segOK : checkSeg 20 perms 262140 262143 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 262140 262143 225 2568560534640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2568560534640)
    (SegSum.cons (w := 45) h262140 (SegSum.cons (w := 180) h262141 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S142
