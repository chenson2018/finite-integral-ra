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

namespace RACert.S6N0.C0.S88

open RACert RACert.Problem

theorem cover98303 : P.CoversSplit 26 10 98303 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98303_0 : P.sumLeaves 26 100662272 135 = 8218975 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 0) (len := 135) (W := 8218975) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_1 : P.sumLeaves 26 100662407 118 = 9463296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 135) (len := 118) (W := 9463296) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_2 : P.sumLeaves 26 100662525 129 = 522185446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 253) (len := 129) (W := 522185446) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_3 : P.sumLeaves 26 100662654 106 = 695159420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 382) (len := 106) (W := 695159420) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_4 : P.sumLeaves 26 100662760 131 = 722609833 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 488) (len := 131) (W := 722609833) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_5 : P.sumLeaves 26 100662891 116 = 759115704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 619) (len := 116) (W := 759115704) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_6 : P.sumLeaves 26 100663007 131 = 1160869130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 735) (len := 131) (W := 1160869130) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_7 : P.sumLeaves 26 100663138 106 = 1446834238 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 866) (len := 106) (W := 1446834238) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem c98303_8 : P.sumLeaves 26 100663244 52 = 938447956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98303) (lo := 972) (len := 52) (W := 938447956) check rows elimOK (by decide) (by decide) cover98303 (by decide)
  decide +kernel

theorem h98303 : P.leaf 36 98303 = 6262903998 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(135, 8218975), (118, 9463296), (129, 522185446), (106, 695159420), (131, 722609833), (116, 759115704), (131, 1160869130), (106, 1446834238), (52, 938447956)]) (.cons c98303_0 (.cons c98303_1 (.cons c98303_2 (.cons c98303_3 (.cons c98303_4 (.cons c98303_5 (.cons c98303_6 (.cons c98303_7 (.cons c98303_8 (.nil)))))))))) (by decide) (by decide))

theorem cover119623 : P.CoversSplit 26 10 119623 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000505050505050505050505050505050505050505050500000505050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000505050505050505050505050505050505050505000000000505050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c119623_0 : P.sumLeaves 26 122493952 704 = 577583 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119623) (lo := 0) (len := 704) (W := 577583) check rows elimOK (by decide) (by decide) cover119623 (by decide)
  decide +kernel

theorem c119623_1 : P.sumLeaves 26 122494656 320 = 598472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119623) (lo := 704) (len := 320) (W := 598472) check rows elimOK (by decide) (by decide) cover119623 (by decide)
  decide +kernel

theorem h119623 : P.leaf 36 119623 = 1176055 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 577583), (320, 598472)]) (.cons c119623_0 (.cons c119623_1 (.nil))) (by decide) (by decide))

theorem cover119631 : P.CoversSplit 26 10 119631 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000505050505050505050505050505050505050505050500000505050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000505050505050505050505050505050505050505000000000505050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c119631_0 : P.sumLeaves 26 122502144 704 = 2305959 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119631) (lo := 0) (len := 704) (W := 2305959) check rows elimOK (by decide) (by decide) cover119631 (by decide)
  decide +kernel

theorem c119631_1 : P.sumLeaves 26 122502848 320 = 1364836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119631) (lo := 704) (len := 320) (W := 1364836) check rows elimOK (by decide) (by decide) cover119631 (by decide)
  decide +kernel

theorem h119631 : P.leaf 36 119631 = 3670795 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 2305959), (320, 1364836)]) (.cons c119631_0 (.cons c119631_1 (.nil))) (by decide) (by decide))

theorem cover119639 : P.CoversSplit 26 10 119639 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000005050000050500000000000000000000050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 1273, 1315, 1322]) (by decide +kernel)

theorem c119639_0 : P.sumLeaves 26 122510336 1024 = 7497540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119639) (lo := 0) (len := 1024) (W := 7497540) check rows elimOK (by decide) (by decide) cover119639 (by decide)
  decide +kernel

theorem h119639 : P.leaf 36 119639 = 7497540 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7497540)]) (.cons c119639_0 (.nil)) (by decide) (by decide))

theorem cover119647 : P.CoversSplit 26 10 119647 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000005050000050500000000000000000000050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 1273, 1315, 1322]) (by decide +kernel)

theorem c119647_0 : P.sumLeaves 26 122518528 1024 = 7920556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119647) (lo := 0) (len := 1024) (W := 7920556) check rows elimOK (by decide) (by decide) cover119647 (by decide)
  decide +kernel

theorem h119647 : P.leaf 36 119647 = 7920556 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7920556)]) (.cons c119647_0 (.nil)) (by decide) (by decide))

theorem cover119671 : P.CoversSplit 26 10 119671 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000505000005050000050500000505000005050000050500000505000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 922, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c119671_0 : P.sumLeaves 26 122543104 752 = 16691826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119671) (lo := 0) (len := 752) (W := 16691826) check rows elimOK (by decide) (by decide) cover119671 (by decide)
  decide +kernel

theorem c119671_1 : P.sumLeaves 26 122543856 272 = 25197006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119671) (lo := 752) (len := 272) (W := 25197006) check rows elimOK (by decide) (by decide) cover119671 (by decide)
  decide +kernel

theorem h119671 : P.leaf 36 119671 = 41888832 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(752, 16691826), (272, 25197006)]) (.cons c119671_0 (.cons c119671_1 (.nil))) (by decide) (by decide))

theorem cover119679 : P.CoversSplit 26 10 119679 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000505000005050000050500000505000005050000050500000505000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 922, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c119679_0 : P.sumLeaves 26 122551296 752 = 21269378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119679) (lo := 0) (len := 752) (W := 21269378) check rows elimOK (by decide) (by decide) cover119679 (by decide)
  decide +kernel

theorem c119679_1 : P.sumLeaves 26 122552048 272 = 26899230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119679) (lo := 752) (len := 272) (W := 26899230) check rows elimOK (by decide) (by decide) cover119679 (by decide)
  decide +kernel

theorem h119679 : P.leaf 36 119679 = 48168608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(752, 21269378), (272, 26899230)]) (.cons c119679_0 (.cons c119679_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98303, 360), (119623, 20), (119631, 20), (119639, 180), (119647, 180), (119671, 180), (119679, 180)]

theorem segOK : checkSeg 20 perms 98303 119799 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98303 119799 1120 2273727972760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2273727972760)
    (SegSum.cons (w := 360) h98303 (SegSum.cons (w := 20) h119623 (SegSum.cons (w := 20) h119631 (SegSum.cons (w := 180) h119639 (SegSum.cons (w := 180) h119647 (SegSum.cons (w := 180) h119671 (SegSum.cons (w := 180) h119679 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S88
