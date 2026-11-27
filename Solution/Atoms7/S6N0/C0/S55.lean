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

namespace RACert.S6N0.C0.S55

open RACert RACert.Problem

theorem cover81855 : P.CoversSplit 26 10 81855 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000330030000000000022002000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81855_0 : P.sumLeaves 26 83819520 64 = 30912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81855) (lo := 0) (len := 64) (W := 30912) check rows elimOK (by decide) (by decide) cover81855 (by decide)
  decide +kernel

theorem contract81855_1 : P.leaf 32 1309681 = 44672 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1309681) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (7, 1, 825), (8, 1, 1217), (29, 0, 1273), (31, 0, 1273), (33, 1, 538), (6, 1, 636), (16, 0, 1273), (17, 0, 1322), (9, 1, 1609)]) (ids := [8, 9, 10, 11, 12, 13, 16, 17, 19, 21, 24, 25, 26, 28, 30, 18, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 0, 0, 8, 9, 17, 10, 1, 11, 18, 19, 12, 13, 14, 0, 15, 0, 16, 1]) (bs := [15, 3]) (W := 44672) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c81855_1 : P.sumLeaves 26 83819584 64 = 44672 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1309681) rows (by decide) (by decide)).symm.trans contract81855_1

theorem c81855_2 : P.sumLeaves 26 83819648 885 = 367602075 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81855) (lo := 128) (len := 885) (W := 367602075) check rows elimOK (by decide) (by decide) cover81855 (by decide)
  decide +kernel

theorem c81855_3 : P.sumLeaves 26 83820533 11 = 77894704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81855) (lo := 1013) (len := 11) (W := 77894704) check rows elimOK (by decide) (by decide) cover81855 (by decide)
  decide +kernel

theorem h81855 : P.leaf 36 81855 = 445572363 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 30912), (64, 44672), (885, 367602075), (11, 77894704)]) (.cons c81855_0 (.cons c81855_1 (.cons c81855_2 (.cons c81855_3 (.nil))))) (by decide) (by decide))

theorem cover81864 : P.CoversSplit 26 10 81864 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f81864 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83828736 + i)

theorem c81864_0 : rowSum f81864 0 1024 = 984000 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81864) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81864 (by decide)
  decide +kernel

theorem sum81864 : rowSum f81864 0 1024 = 984000 :=
  c81864_0

theorem h81864 : P.leaf 36 81864 = 984000 :=
  leaf_weighted (k := 26) (d := 10) (H := 81864) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81864) (by decide) (by decide +kernel)) sum81864

theorem cover81865 : P.CoversSplit 26 10 81865 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f81865 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83829760 + i)

theorem c81865_0 : rowSum f81865 0 1024 = 12368504 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81865) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81865 (by decide)
  decide +kernel

theorem sum81865 : rowSum f81865 0 1024 = 12368504 :=
  c81865_0

theorem h81865 : P.leaf 36 81865 = 12368504 :=
  leaf_weighted (k := 26) (d := 10) (H := 81865) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81865) (by decide) (by decide +kernel)) sum81865

theorem cover81866 : P.CoversSplit 26 10 81866 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81866_0 : P.sumLeaves 26 83830784 962 = 7038456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81866) (lo := 0) (len := 962) (W := 7038456) check rows elimOK (by decide) (by decide) cover81866 (by decide)
  decide +kernel

theorem c81866_1 : P.sumLeaves 26 83831746 62 = 3635256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81866) (lo := 962) (len := 62) (W := 3635256) check rows elimOK (by decide) (by decide) cover81866 (by decide)
  decide +kernel

theorem h81866 : P.leaf 36 81866 = 10673712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(962, 7038456), (62, 3635256)]) (.cons c81866_0 (.cons c81866_1 (.nil))) (by decide) (by decide))

theorem cover81867 : P.CoversSplit 26 10 81867 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1266, 1315, 1658, 1665]) (by decide +kernel)

theorem c81867_0 : P.sumLeaves 26 83831808 962 = 37499950 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81867) (lo := 0) (len := 962) (W := 37499950) check rows elimOK (by decide) (by decide) cover81867 (by decide)
  decide +kernel

theorem c81867_1 : P.sumLeaves 26 83832770 62 = 21634168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81867) (lo := 962) (len := 62) (W := 21634168) check rows elimOK (by decide) (by decide) cover81867 (by decide)
  decide +kernel

theorem h81867 : P.leaf 36 81867 = 59134118 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(962, 37499950), (62, 21634168)]) (.cons c81867_0 (.cons c81867_1 (.nil))) (by decide) (by decide))

theorem cover81870 : P.CoversSplit 26 10 81870 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81870_0 : P.sumLeaves 26 83834880 502 = 8652378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81870) (lo := 0) (len := 502) (W := 8652378) check rows elimOK (by decide) (by decide) cover81870 (by decide)
  decide +kernel

theorem c81870_1 : P.sumLeaves 26 83835382 478 = 22372175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81870) (lo := 502) (len := 478) (W := 22372175) check rows elimOK (by decide) (by decide) cover81870 (by decide)
  decide +kernel

theorem c81870_2 : P.sumLeaves 26 83835860 44 = 12678516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81870) (lo := 980) (len := 44) (W := 12678516) check rows elimOK (by decide) (by decide) cover81870 (by decide)
  decide +kernel

theorem h81870 : P.leaf 36 81870 = 43703069 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 8652378), (478, 22372175), (44, 12678516)]) (.cons c81870_0 (.cons c81870_1 (.cons c81870_2 (.nil)))) (by decide) (by decide))

theorem cover81871 : P.CoversSplit 26 10 81871 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81871_0 : P.sumLeaves 26 83835904 502 = 42761503 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81871) (lo := 0) (len := 502) (W := 42761503) check rows elimOK (by decide) (by decide) cover81871 (by decide)
  decide +kernel

theorem c81871_1 : P.sumLeaves 26 83836406 478 = 120923986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81871) (lo := 502) (len := 478) (W := 120923986) check rows elimOK (by decide) (by decide) cover81871 (by decide)
  decide +kernel

theorem c81871_2 : P.sumLeaves 26 83836884 44 = 71689660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81871) (lo := 980) (len := 44) (W := 71689660) check rows elimOK (by decide) (by decide) cover81871 (by decide)
  decide +kernel

theorem h81871 : P.leaf 36 81871 = 235375149 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 42761503), (478, 120923986), (44, 71689660)]) (.cons c81871_0 (.cons c81871_1 (.cons c81871_2 (.nil)))) (by decide) (by decide))

theorem cover81882 : P.CoversSplit 26 10 81882 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000050500000505000000000000000000000505000005000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000050500000505000000000000000000000500000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1315, 1658, 1665]) (ps := [(12, [979], [880]), (17, [1322], [874])]) (by decide +kernel)

noncomputable def f81882 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83847168 + i)

theorem c81882_0 : rowSum f81882 0 989 = 71703148 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81882) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81882 (by decide)
  decide +kernel

theorem c81882_1 : rowSum f81882 989 35 = 22147904 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81882) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81882 (by decide)
  decide +kernel

theorem sum81882 : rowSum f81882 0 1024 = 93851052 :=
  rowSum_append (F := f81882) (lo := 0) (n := 989) (m := 35) (A := 71703148) (B := 22147904) c81882_0 (c81882_1)

theorem h81882 : P.leaf 36 81882 = 93851052 :=
  leaf_weighted (k := 26) (d := 10) (H := 81882) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81882) (by decide) (by decide +kernel)) sum81882

theorem cover81883 : P.CoversSplit 26 10 81883 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000050500000505000000000000000000000505000005000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000050500000505000000000000000000000505000005000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f81883 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83848192 + i)

theorem c81883_0 : rowSum f81883 0 983 = 123064890 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81883) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81883 (by decide)
  decide +kernel

theorem c81883_1 : rowSum f81883 983 41 = 47289108 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81883) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81883 (by decide)
  decide +kernel

theorem sum81883 : rowSum f81883 0 1024 = 170353998 :=
  rowSum_append (F := f81883) (lo := 0) (n := 983) (m := 41) (A := 123064890) (B := 47289108) c81883_0 (c81883_1)

theorem h81883 : P.leaf 36 81883 = 170353998 :=
  leaf_weighted (k := 26) (d := 10) (H := 81883) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81883) (by decide) (by decide +kernel)) sum81883

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

def seg : List (ℕ × ℕ) := [(81855, 360), (81864, 90), (81865, 180), (81866, 720), (81867, 720), (81870, 360), (81871, 360), (81882, 360), (81883, 360), (81884, 360), (81885, 360)]

theorem segOK : checkSeg 20 perms 81855 81886 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81855 81886 4230 547633083240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 547633083240)
    (SegSum.cons (w := 360) h81855 (SegSum.cons (w := 90) h81864 (SegSum.cons (w := 180) h81865 (SegSum.cons (w := 720) h81866 (SegSum.cons (w := 720) h81867 (SegSum.cons (w := 360) h81870 (SegSum.cons (w := 360) h81871 (SegSum.cons (w := 360) h81882 (SegSum.cons (w := 360) h81883 (SegSum.cons (w := 360) h81884 (SegSum.cons (w := 360) h81885 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))) (by decide)

end RACert.S6N0.C0.S55
