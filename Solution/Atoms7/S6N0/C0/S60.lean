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

namespace RACert.S6N0.C0.S60

open RACert RACert.Problem

theorem cover81882 : P.CoversSplit 26 10 81882 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000050500000505000000000000000000000505000005000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000050500000505000000000000000000000505000005000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81882_0 : P.sumLeaves 26 83847168 863 = 30913310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81882) (lo := 0) (len := 863) (W := 30913310) check rows elimOK (by decide) (by decide) cover81882 (by decide)
  decide +kernel

theorem c81882_1 : P.sumLeaves 26 83848031 161 = 62937742 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81882) (lo := 863) (len := 161) (W := 62937742) check rows elimOK (by decide) (by decide) cover81882 (by decide)
  decide +kernel

theorem h81882 : P.leaf 36 81882 = 93851052 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(863, 30913310), (161, 62937742)]) (.cons c81882_0 (.cons c81882_1 (.nil))) (by decide) (by decide))

theorem cover81883 : P.CoversSplit 26 10 81883 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000050500000505000000000000000000000505000005000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000050500000505000000000000000000000505000005000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81883_0 : P.sumLeaves 26 83848192 863 = 49521636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81883) (lo := 0) (len := 863) (W := 49521636) check rows elimOK (by decide) (by decide) cover81883 (by decide)
  decide +kernel

theorem c81883_1 : P.sumLeaves 26 83849055 161 = 120832362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81883) (lo := 863) (len := 161) (W := 120832362) check rows elimOK (by decide) (by decide) cover81883 (by decide)
  decide +kernel

theorem h81883 : P.leaf 36 81883 = 170353998 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(863, 49521636), (161, 120832362)]) (.cons c81883_0 (.cons c81883_1 (.nil))) (by decide) (by decide))

theorem cover81884 : P.CoversSplit 26 10 81884 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81884_0 : P.sumLeaves 26 83849216 502 = 20263716 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81884) (lo := 0) (len := 502) (W := 20263716) check rows elimOK (by decide) (by decide) cover81884 (by decide)
  decide +kernel

theorem c81884_1 : P.sumLeaves 26 83849718 478 = 70409498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81884) (lo := 502) (len := 478) (W := 70409498) check rows elimOK (by decide) (by decide) cover81884 (by decide)
  decide +kernel

theorem c81884_2 : P.sumLeaves 26 83850196 44 = 42963672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81884) (lo := 980) (len := 44) (W := 42963672) check rows elimOK (by decide) (by decide) cover81884 (by decide)
  decide +kernel

theorem h81884 : P.leaf 36 81884 = 133636886 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 20263716), (478, 70409498), (44, 42963672)]) (.cons c81884_0 (.cons c81884_1 (.cons c81884_2 (.nil)))) (by decide) (by decide))

theorem cover81885 : P.CoversSplit 26 10 81885 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81885_0 : P.sumLeaves 26 83850240 502 = 34846684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81885) (lo := 0) (len := 502) (W := 34846684) check rows elimOK (by decide) (by decide) cover81885 (by decide)
  decide +kernel

theorem c81885_1 : P.sumLeaves 26 83850742 478 = 136185032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81885) (lo := 502) (len := 478) (W := 136185032) check rows elimOK (by decide) (by decide) cover81885 (by decide)
  decide +kernel

theorem c81885_2 : P.sumLeaves 26 83851220 44 = 81632864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81885) (lo := 980) (len := 44) (W := 81632864) check rows elimOK (by decide) (by decide) cover81885 (by decide)
  decide +kernel

theorem h81885 : P.leaf 36 81885 = 252664580 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 34846684), (478, 136185032), (44, 81632864)]) (.cons c81885_0 (.cons c81885_1 (.cons c81885_2 (.nil)))) (by decide) (by decide))

theorem cover81886 : P.CoversSplit 26 10 81886 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000505000005050000000000000000000005050000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81886_0 : P.sumLeaves 26 83851264 502 = 64903808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81886) (lo := 0) (len := 502) (W := 64903808) check rows elimOK (by decide) (by decide) cover81886 (by decide)
  decide +kernel

theorem c81886_1 : P.sumLeaves 26 83851766 449 = 145368604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81886) (lo := 502) (len := 449) (W := 145368604) check rows elimOK (by decide) (by decide) cover81886 (by decide)
  decide +kernel

theorem c81886_2 : P.sumLeaves 26 83852215 73 = 147288364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81886) (lo := 951) (len := 73) (W := 147288364) check rows elimOK (by decide) (by decide) cover81886 (by decide)
  decide +kernel

theorem h81886 : P.leaf 36 81886 = 357560776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 64903808), (449, 145368604), (73, 147288364)]) (.cons c81886_0 (.cons c81886_1 (.cons c81886_2 (.nil)))) (by decide) (by decide))

theorem cover81887 : P.CoversSplit 26 10 81887 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000505000005050000000000000000000005050000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000505000005050000000000000000000005050000050000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81887_0 : P.sumLeaves 26 83852288 472 = 78837349 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 0) (len := 472) (W := 78837349) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem c81887_1 : P.sumLeaves 26 83852760 449 = 214919926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 472) (len := 449) (W := 214919926) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem c81887_2 : P.sumLeaves 26 83853209 103 = 316094246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81887) (lo := 921) (len := 103) (W := 316094246) check rows elimOK (by decide) (by decide) cover81887 (by decide)
  decide +kernel

theorem h81887 : P.leaf 36 81887 = 609851521 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(472, 78837349), (449, 214919926), (103, 316094246)]) (.cons c81887_0 (.cons c81887_1 (.cons c81887_2 (.nil)))) (by decide) (by decide))

theorem cover81918 : P.CoversSplit 26 10 81918 0xfffffffafffffafafffffffafffffafafffffffafffcfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafafffcfac8aaaaaaaaaa88aa88fffffffafffffafafffffffafffffafafffffffaffccfac8aaaaaaaaaa88aa880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81918_0 : P.sumLeaves 26 83884032 405 = 122450968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81918) (lo := 0) (len := 405) (W := 122450968) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_1 : P.sumLeaves 26 83884437 104 = 319299754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81918) (lo := 405) (len := 104) (W := 319299754) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_2 : P.sumLeaves 26 83884541 160 = 192564022 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81918) (lo := 509) (len := 160) (W := 192564022) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_3 : P.sumLeaves 26 83884701 152 = 370163958 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81918) (lo := 669) (len := 152) (W := 370163958) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_4 : P.sumLeaves 26 83884853 118 = 341483788 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81918) (lo := 821) (len := 118) (W := 341483788) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem c81918_5 : P.sumLeaves 26 83884971 85 = 609674762 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81918) (lo := 939) (len := 85) (W := 609674762) check rows elimOK (by decide) (by decide) cover81918 (by decide)
  decide +kernel

theorem h81918 : P.leaf 36 81918 = 1955637252 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(405, 122450968), (104, 319299754), (160, 192564022), (152, 370163958), (118, 341483788), (85, 609674762)]) (.cons c81918_0 (.cons c81918_1 (.cons c81918_2 (.cons c81918_3 (.cons c81918_4 (.cons c81918_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(81882, 360), (81883, 360), (81884, 360), (81885, 360), (81886, 720), (81887, 720), (81918, 180)]

theorem segOK : checkSeg 20 perms 81882 81919 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81882 81919 3060 1282733904960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1282733904960)
    (SegSum.cons (w := 360) h81882 (SegSum.cons (w := 360) h81883 (SegSum.cons (w := 360) h81884 (SegSum.cons (w := 360) h81885 (SegSum.cons (w := 720) h81886 (SegSum.cons (w := 720) h81887 (SegSum.cons (w := 180) h81918 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S60
