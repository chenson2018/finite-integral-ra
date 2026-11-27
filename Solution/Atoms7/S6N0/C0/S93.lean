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

namespace RACert.S6N0.C0.S93

open RACert RACert.Problem

theorem cover120819 : P.CoversSplit 26 10 120819 0xf0f00000f0f000000000000000000000f0f00000f0c000000000000000000000f0f00000f0f000000000505000005050f0f00000f0c000000000505000004040f0f00000f0f000000000000000000000f0f00000c0c000000000000000000000f0f00000f0f000000000505000005050f0f00000c0c000000000505000004040 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 873, 922, 1322]) (by decide +kernel)

theorem c120819_0 : P.sumLeaves 26 123718656 684 = 77036816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120819) (lo := 0) (len := 684) (W := 77036816) check rows elimOK (by decide) (by decide) cover120819 (by decide)
  decide +kernel

theorem c120819_1 : P.sumLeaves 26 123719340 340 = 122575564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120819) (lo := 684) (len := 340) (W := 122575564) check rows elimOK (by decide) (by decide) cover120819 (by decide)
  decide +kernel

theorem h120819 : P.leaf 36 120819 = 199612380 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(684, 77036816), (340, 122575564)]) (.cons c120819_0 (.cons c120819_1 (.nil))) (by decide) (by decide))

theorem cover120820 : P.CoversSplit 26 10 120820 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0ffccffccffccfac8ffccffccffccfac8ffccffccccccc8c8fac8fac8c8c8c8c8ffccfac8ffccfac8fac8f0c0fac8f0c0ffccfac8ccccc8c8fac8f0c0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120820_0 : P.sumLeaves 26 123719680 205 = 4531312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 0) (len := 205) (W := 4531312) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_1 : P.sumLeaves 26 123719885 171 = 14423772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 205) (len := 171) (W := 14423772) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_2 : P.sumLeaves 26 123720056 134 = 39937696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 376) (len := 134) (W := 39937696) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_3 : P.sumLeaves 26 123720190 155 = 21641914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 510) (len := 155) (W := 21641914) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_4 : P.sumLeaves 26 123720345 139 = 35627898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 665) (len := 139) (W := 35627898) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_5 : P.sumLeaves 26 123720484 116 = 25533558 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 804) (len := 116) (W := 25533558) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_6 : P.sumLeaves 26 123720600 100 = 43146928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 920) (len := 100) (W := 43146928) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_7 : P.sumLeaves 26 123720700 4 = 6953392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120820) (lo := 1020) (len := 4) (W := 6953392) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem h120820 : P.leaf 36 120820 = 191796470 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(205, 4531312), (171, 14423772), (134, 39937696), (155, 21641914), (139, 35627898), (116, 25533558), (100, 43146928), (4, 6953392)]) (.cons c120820_0 (.cons c120820_1 (.cons c120820_2 (.cons c120820_3 (.cons c120820_4 (.cons c120820_5 (.cons c120820_6 (.cons c120820_7 (.nil))))))))) (by decide) (by decide))

theorem cover120821 : P.CoversSplit 26 10 120821 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0ffffffffffccfac8ffffffffffccfac8ffffffffccccc8c8fafafafac8c8c8c8fffffafaffccfac8fafaf0f0fac8f0c0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120821_0 : P.sumLeaves 26 123720704 179 = 27141249 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 0) (len := 179) (W := 27141249) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_1 : P.sumLeaves 26 123720883 144 = 55486171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 179) (len := 144) (W := 55486171) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_2 : P.sumLeaves 26 123721027 122 = 118366768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 323) (len := 122) (W := 118366768) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_3 : P.sumLeaves 26 123721149 151 = 160922617 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 445) (len := 151) (W := 160922617) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_4 : P.sumLeaves 26 123721300 128 = 167542045 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 596) (len := 128) (W := 167542045) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_5 : P.sumLeaves 26 123721428 138 = 220635506 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 724) (len := 138) (W := 220635506) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_6 : P.sumLeaves 26 123721566 102 = 233944689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 862) (len := 102) (W := 233944689) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_7 : P.sumLeaves 26 123721668 60 = 234305566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 964) (len := 60) (W := 234305566) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem h120821 : P.leaf 36 120821 = 1218344611 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(179, 27141249), (144, 55486171), (122, 118366768), (151, 160922617), (128, 167542045), (138, 220635506), (102, 233944689), (60, 234305566)]) (.cons c120821_0 (.cons c120821_1 (.cons c120821_2 (.cons c120821_3 (.cons c120821_4 (.cons c120821_5 (.cons c120821_6 (.cons c120821_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120819, 360), (120820, 360), (120821, 720)]

theorem segOK : checkSeg 20 perms 120819 120823 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120819 120823 1440 1018115305920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1018115305920)
    (SegSum.cons (w := 360) h120819 (SegSum.cons (w := 360) h120820 (SegSum.cons (w := 720) h120821 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S93
