/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S20

open RACert RACert.Problem

theorem cover3567 : P.CoversSplit 24 10 3567 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 866, 915, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3567 : P.leaf 34 3567 = 3880317 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3567) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3567) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3567 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover49647 : P.CoversSplit 24 10 49647 0xf0015501f00050003031111130301010f0015501f00050003031111130301010f0005500f00050003000110030001000f0005500f00050003000110030001000f0015501f00050003031111130301010f0015501f00050003031111130301010f0005500f00050003000110030001000f0005500f00050003000110030001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 859, 865]) (by decide +kernel)

noncomputable def f49647 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (50838528 + i)

theorem c49647_0 : rowSum f49647 0 764 = 25064053 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49647) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49647 (by decide)
  decide +kernel

theorem c49647_1 : rowSum f49647 764 260 = 13699356 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49647) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49647 (by decide)
  decide +kernel

theorem sum49647 : rowSum f49647 0 1024 = 38763409 :=
  rowSum_append (F := f49647) (lo := 0) (n := 764) (m := 260) (A := 25064053) (B := 13699356) c49647_0 (c49647_1)

theorem h49647 : P.leaf 34 49647 = 38763409 :=
  leaf_weighted (k := 24) (d := 10) (H := 49647) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49647) (by decide) (by decide +kernel)) sum49647

theorem h3582 : P.leaf 34 3582 = 38763409 :=
  orient24 (v := 49647) (by decide) (by decide +kernel) h49647

theorem cover49663 : P.CoversSplit 24 10 49663 0xfff8faf8faf8faf8ffc8fac8fac8fac8fff8faf8faf8faf8ffc8fac8fac8fac8ffc8fac8fac8fac8ffc8fac8fac8fac8ffc8fac8fac8fac8ffc8fac8fac8fac8fff8faf8faf8faf8ffc8fac8fac8fac8fff8faf8faf8faf8ffc8fac8fac8fac8ffc8fac8fac8fac8ffc8fac8fac8fac8ffc8fac8fac8fac8ffc8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 915]) (by decide +kernel)

noncomputable def f49663 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (50854912 + i)

theorem c49663_0 : rowSum f49663 0 189 = 44757801 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49663) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49663 (by decide)
  decide +kernel

theorem c49663_1 : rowSum f49663 189 251 = 81829281 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49663) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49663 (by decide)
  decide +kernel

theorem c49663_2 : rowSum f49663 440 302 = 112734257 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49663) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49663 (by decide)
  decide +kernel

theorem c49663_3 : rowSum f49663 742 282 = 77997222 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49663) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49663 (by decide)
  decide +kernel

theorem sum49663 : rowSum f49663 0 1024 = 317318561 :=
  rowSum_append (F := f49663) (lo := 0) (n := 189) (m := 835) (A := 44757801) (B := 272560760) c49663_0 (rowSum_append (F := f49663) (lo := 189) (n := 251) (m := 584) (A := 81829281) (B := 190731479) c49663_1 (rowSum_append (F := f49663) (lo := 440) (n := 302) (m := 282) (A := 112734257) (B := 77997222) c49663_2 (c49663_3)))

theorem h49663 : P.leaf 34 49663 = 317318561 :=
  leaf_weighted (k := 24) (d := 10) (H := 49663) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49663) (by decide) (by decide +kernel)) sum49663

theorem h3583 : P.leaf 34 3583 = 317318561 :=
  orient24 (v := 49663) (by decide) (by decide +kernel) h49663

theorem cover3710 : P.CoversSplit 24 10 3710 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000003300330000000000000000000000000033003300000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000003300330000000000000000000000000033003300000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

noncomputable def f3710 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3799040 + i)

theorem c3710_0 : rowSum f3710 0 1024 = 7851704 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3710) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3710 (by decide)
  decide +kernel

theorem sum3710 : rowSum f3710 0 1024 = 7851704 :=
  c3710_0

theorem h3710 : P.leaf 34 3710 = 7851704 :=
  leaf_weighted (k := 24) (d := 10) (H := 3710) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 3710) (by decide) (by decide +kernel)) sum3710

theorem cover3711 : P.CoversSplit 24 10 3711 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000003300330000000000000000000000000033003300000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000003300330000000000000000000000000033003300000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

noncomputable def f3711 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3800064 + i)

theorem c3711_0 : rowSum f3711 0 1024 = 8174816 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3711 (by decide)
  decide +kernel

theorem sum3711 : rowSum f3711 0 1024 = 8174816 :=
  c3711_0

theorem h3711 : P.leaf 34 3711 = 8174816 :=
  leaf_weighted (k := 24) (d := 10) (H := 3711) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 3711) (by decide) (by decide +kernel)) sum3711

theorem h3748 : P.leaf 34 3748 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 466), (26, 1, 472), (35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h3749 : P.leaf 34 3749 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3750 : P.CoversSplit 24 10 3750 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3750 : P.leaf 34 3750 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3750) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3750) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3750 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3751 : P.CoversSplit 24 10 3751 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3751 : P.leaf 34 3751 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3751) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3752 : P.CoversSplit 24 10 3752 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 915, 1202, 1210, 1258]) (by decide +kernel)

theorem h3752 : P.leaf 34 3752 = 17424 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3752) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3752) (weight := fun _ => 1) (xs := [991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover3752 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3781 : P.CoversSplit 24 10 3781 0xcc000000c4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 536, 566, 573, 915, 916, 1202]) (by decide +kernel)

theorem h3781 : P.leaf 34 3781 = 123456 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3781) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3781) (weight := fun _ => 1) (xs := [986, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3781 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3753 : P.leaf 34 3753 = 123456 :=
  orient4 (v := 3781) (by decide) (by decide +kernel) h3781

theorem cover33886 : P.CoversSplit 24 10 33886 0x8000800080000000800080008000000080008000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 572, 573, 578, 860, 867, 872, 915, 1202, 1209, 1251]) (by decide +kernel)

theorem h33886 : P.leaf 34 33886 = 269104 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 33886) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 33886) (weight := fun _ => 1) (xs := [831, 879, 895, 927, 943, 959, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover33886 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3754 : P.leaf 34 3754 = 269104 :=
  orient5 (v := 33886) (by decide) (by decide +kernel) h33886

theorem cover33887 : P.CoversSplit 24 10 33887 0xcc00c80088000000cc00c80088000000cc00c80000000000cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 572, 573, 578, 858, 867, 872, 915, 1202, 1209, 1217, 1251]) (by decide +kernel)

theorem h33887 : P.leaf 34 33887 = 3097052 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 33887) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 33887) (weight := fun _ => 1) (xs := [826, 827, 830, 831, 875, 878, 879, 890, 891, 894, 895, 923, 927, 939, 942, 943, 954, 955, 958, 959, 987, 991, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover33887 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3755 : P.leaf 34 3755 = 3097052 :=
  orient5 (v := 33887) (by decide) (by decide +kernel) h33887

theorem cover3756 : P.CoversSplit 24 10 3756 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 915, 1202, 1210, 1258]) (by decide +kernel)

theorem h3756 : P.leaf 34 3756 = 111160 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3756) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3756) (weight := fun _ => 1) (xs := [991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover3756 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3757 : P.CoversSplit 24 10 3757 0xcc00cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 915, 1202, 1210]) (by decide +kernel)

theorem h3757 : P.leaf 34 3757 = 614224 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3757) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3757) (weight := fun _ => 1) (xs := [990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3757 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3758 : P.CoversSplit 24 10 3758 0xaa000000a00000000000000000000000aa000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 916, 921, 1202, 1258]) (by decide +kernel)

theorem h3758 : P.leaf 34 3758 = 1314276 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3758) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3758) (weight := fun _ => 1) (xs := [856, 889, 891, 893, 895, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3758 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover33919 : P.CoversSplit 24 10 33919 0xcc00c80088000000cc00c80088000000cc00c80088000000cc00c80088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 573, 578, 858, 860, 867, 872, 915, 1202, 1209]) (by decide +kernel)

theorem c33919_0 : P.sumLeaves 24 34733056 1024 = 6350768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 33919) (lo := 0) (len := 1024) (W := 6350768) check rows elimOK (by decide) (by decide) cover33919 (by decide)
  decide +kernel

theorem h33919 : P.leaf 34 33919 = 6350768 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6350768)]) (.cons c33919_0 (.nil)) (by decide) (by decide))

theorem h3759 : P.leaf 34 3759 = 6350768 :=
  orient5 (v := 33919) (by decide) (by decide +kernel) h33919

theorem cover34366 : P.CoversSplit 24 10 34366 0xcc00cc0000000000cc00cc0000000000800000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 529, 566, 572, 573, 578, 860, 915, 1209, 1258]) (ps := [(8, [531, 622], [517, 1272])]) (by decide +kernel)

theorem h34366 : P.leaf 34 34366 = 1042924 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 34366) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 34366) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 34366) (weight := rowWeight keep2 twice2) (xs := [490, 491, 494, 495, 506, 507, 510, 511, 831, 895, 938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover34366 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3766 : P.leaf 34 3766 = 1042924 :=
  orient5 (v := 34366) (by decide) (by decide +kernel) h34366

theorem cover34367 : P.CoversSplit 24 10 34367 0xcc00cc0000000000cc00cc0000000000800000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 529, 566, 572, 573, 578, 860, 915, 1209, 1258]) (ps := [(8, [531, 622], [517, 1272])]) (by decide +kernel)

theorem h34367 : P.leaf 34 34367 = 2376176 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 34367) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 34367) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 34367) (weight := rowWeight keep2 twice2) (xs := [490, 491, 494, 495, 506, 507, 510, 511, 831, 895, 938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover34367 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3767 : P.leaf 34 3767 = 2376176 :=
  orient5 (v := 34367) (by decide) (by decide +kernel) h34367

theorem cover34382 : P.CoversSplit 24 10 34382 0x8000000080000000800000008000000080000000000004008000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 572, 573, 860, 915, 921, 1202]) (by decide +kernel)

theorem h34382 : P.leaf 34 34382 = 206728 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 34382) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 34382) (weight := fun _ => 1) (xs := [778, 831, 842, 895, 927, 959, 991, 1023]) check rows elimOK (by decide) (by decide) cover34382 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3768 : P.leaf 34 3768 = 206728 :=
  orient5 (v := 34382) (by decide) (by decide +kernel) h34382

theorem cover3783 : P.CoversSplit 24 10 3783 0xff000000f40000000000000000000000ff000000f40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 536, 566, 573, 915, 916, 921, 1202, 1258]) (by decide +kernel)

theorem h3783 : P.leaf 34 3783 = 1900216 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3783) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3783) (weight := fun _ => 1) (xs := [858, 860, 861, 862, 863, 888, 889, 890, 891, 892, 893, 894, 895, 986, 988, 989, 990, 991, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3783 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3769 : P.leaf 34 3769 = 1900216 :=
  orient4 (v := 3783) (by decide) (by decide +kernel) h3783

theorem cover34398 : P.CoversSplit 24 10 34398 0xcc00cc0088000000cc00cc0088000000c400c40000000000c400c400000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 523, 572, 573, 578, 860, 915, 1202, 1209, 1258]) (ps := [(14, [965], [860, 1272])]) (by decide +kernel)

theorem c34398_0 : P.sumLeaves 24 35223552 1024 = 2094084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 34398) (lo := 0) (len := 1024) (W := 2094084) check rows elimOK (by decide) (by decide) cover34398 (by decide)
  decide +kernel

theorem h34398 : P.leaf 34 34398 = 2094084 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2094084)]) (.cons c34398_0 (.nil)) (by decide) (by decide))

theorem h3770 : P.leaf 34 3770 = 2094084 :=
  orient5 (v := 34398) (by decide) (by decide +kernel) h34398

theorem cover34399 : P.CoversSplit 24 10 34399 0xcc00cc0088000000cc00cc0088000000cc00cc0000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 572, 573, 578, 915, 1202, 1209, 1217, 1258, 1308]) (ps := [(14, [965], [1272])]) (by decide +kernel)

theorem c34399_0 : P.sumLeaves 24 35224576 1024 = 6115128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 34399) (lo := 0) (len := 1024) (W := 6115128) check rows elimOK (by decide) (by decide) cover34399 (by decide)
  decide +kernel

theorem h34399 : P.leaf 34 34399 = 6115128 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6115128)]) (.cons c34399_0 (.nil)) (by decide) (by decide))

theorem h3771 : P.leaf 34 3771 = 6115128 :=
  orient5 (v := 34399) (by decide) (by decide +kernel) h34399

theorem cover3814 : P.CoversSplit 24 10 3814 0xaa000000ab0000000000000000000000aa000000ab0000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 915, 916, 921, 1217, 1258, 1308]) (by decide +kernel)

theorem h3814 : P.leaf 34 3814 = 1286228 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3814) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3814) (weight := fun _ => 1) (xs := [475, 479, 507, 511, 856, 857, 859, 861, 863, 889, 891, 893, 895, 984, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3814 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3772 : P.leaf 34 3772 = 1286228 :=
  orient4 (v := 3814) (by decide) (by decide +kernel) h3814

theorem cover3815 : P.CoversSplit 24 10 3815 0xff000000fe0000000000000000000000ff000000fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 915, 916, 921, 1217, 1258, 1308]) (by decide +kernel)

theorem c3815_0 : P.sumLeaves 24 3906560 1024 = 3848116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3815) (lo := 0) (len := 1024) (W := 3848116) check rows elimOK (by decide) (by decide) cover3815 (by decide)
  decide +kernel

theorem h3815 : P.leaf 34 3815 = 3848116 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3848116)]) (.cons c3815_0 (.nil)) (by decide) (by decide))

theorem h3773 : P.leaf 34 3773 = 3848116 :=
  orient4 (v := 3815) (by decide) (by decide +kernel) h3815

theorem cover34430 : P.CoversSplit 24 10 34430 0xcc00cc0088000000cc00cc0088000000c400c40000000000c400c400000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 573, 578, 860, 915, 1202, 1209, 1258]) (ps := [(8, [622], [1272])]) (by decide +kernel)

theorem c34430_0 : P.sumLeaves 24 35256320 1024 = 5324280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 34430) (lo := 0) (len := 1024) (W := 5324280) check rows elimOK (by decide) (by decide) cover34430 (by decide)
  decide +kernel

theorem h34430 : P.leaf 34 34430 = 5324280 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5324280)]) (.cons c34430_0 (.nil)) (by decide) (by decide))

theorem h3774 : P.leaf 34 3774 = 5324280 :=
  orient5 (v := 34430) (by decide) (by decide +kernel) h34430

theorem cover3775 : P.CoversSplit 24 10 3775 0xff00ff00f00000000000000000000000ff00ff00f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 573, 916, 921, 1202, 1209, 1210, 1259, 1308]) (by decide +kernel)

theorem c3775_0 : P.sumLeaves 24 3865600 1024 = 10798804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3775) (lo := 0) (len := 1024) (W := 10798804) check rows elimOK (by decide) (by decide) cover3775 (by decide)
  decide +kernel

theorem h3775 : P.leaf 34 3775 = 10798804 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10798804)]) (.cons c3775_0 (.nil)) (by decide) (by decide))

theorem cover3784 : P.CoversSplit 24 10 3784 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 474, 508, 515, 516, 522, 523, 536, 573, 915, 1202, 1210, 1651]) (ps := [(14, [929], [487])]) (by decide +kernel)

theorem h3784 : P.leaf 34 3784 = 16382 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3784) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3784) (weight := fun _ => 1) (xs := [991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover3784 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover34895 : P.CoversSplit 24 10 34895 0x8000040080000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 572, 573, 858, 865, 1202, 1209, 1308, 1651]) (by decide +kernel)

theorem h34895 : P.leaf 34 34895 = 103190 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 34895) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 34895) (weight := fun _ => 1) (xs := [383, 479, 511, 842, 895, 991, 1002, 1023]) check rows elimOK (by decide) (by decide) cover34895 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3785 : P.leaf 34 3785 = 103190 :=
  orient5 (v := 34895) (by decide) (by decide +kernel) h34895

theorem cover3786 : P.CoversSplit 24 10 3786 0xaa000000a10000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 536, 916, 1202]) (by decide +kernel)

theorem h3786 : P.leaf 34 3786 = 307470 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3786) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3786) (weight := fun _ => 1) (xs := [889, 891, 893, 895, 984, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3786 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover34911 : P.CoversSplit 24 10 34911 0xcc00c800c8000000cc00c800c8000000c400c00000000000c400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 572, 573, 578, 858, 859, 866, 879, 1202, 1217, 1251]) (by decide +kernel)

theorem h34911 : P.leaf 34 34911 = 2721896 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 34911) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 34911) (weight := fun _ => 1) (xs := [826, 830, 831, 878, 879, 890, 894, 895, 923, 926, 927, 939, 942, 943, 954, 955, 958, 959, 987, 990, 991, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover34911 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3787 : P.leaf 34 3787 = 2721896 :=
  orient5 (v := 34911) (by decide) (by decide +kernel) h34911

theorem cover3788 : P.CoversSplit 24 10 3788 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 915, 1202, 1210, 1258, 1651]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h3788 : P.leaf 34 3788 = 101728 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3788) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3788) (weight := fun _ => 1) (xs := [991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover3788 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3567, 24), (3582, 12), (3583, 12), (3710, 4), (3711, 4), (3748, 24), (3749, 24), (3750, 48), (3751, 48), (3752, 48), (3753, 48), (3754, 48), (3755, 48), (3756, 48), (3757, 48), (3758, 48), (3759, 48), (3766, 24), (3767, 24), (3768, 48), (3769, 48), (3770, 48), (3771, 48), (3772, 48), (3773, 48), (3774, 48), (3775, 48), (3784, 24), (3785, 24), (3786, 48), (3787, 48), (3788, 48)]

theorem segOK : checkSeg 16 perms 3567 3789 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3567 3789 1208 6752048272 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6752048272)
    (SegSum.cons (w := 24) h3567 (SegSum.cons (w := 12) h3582 (SegSum.cons (w := 12) h3583 (SegSum.cons (w := 4) h3710 (SegSum.cons (w := 4) h3711 (SegSum.cons (w := 24) h3748 (SegSum.cons (w := 24) h3749 (SegSum.cons (w := 48) h3750 (SegSum.cons (w := 48) h3751 (SegSum.cons (w := 48) h3752 (SegSum.cons (w := 48) h3753 (SegSum.cons (w := 48) h3754 (SegSum.cons (w := 48) h3755 (SegSum.cons (w := 48) h3756 (SegSum.cons (w := 48) h3757 (SegSum.cons (w := 48) h3758 (SegSum.cons (w := 48) h3759 (SegSum.cons (w := 24) h3766 (SegSum.cons (w := 24) h3767 (SegSum.cons (w := 48) h3768 (SegSum.cons (w := 48) h3769 (SegSum.cons (w := 48) h3770 (SegSum.cons (w := 48) h3771 (SegSum.cons (w := 48) h3772 (SegSum.cons (w := 48) h3773 (SegSum.cons (w := 48) h3774 (SegSum.cons (w := 48) h3775 (SegSum.cons (w := 24) h3784 (SegSum.cons (w := 24) h3785 (SegSum.cons (w := 48) h3786 (SegSum.cons (w := 48) h3787 (SegSum.cons (w := 48) h3788 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S20
