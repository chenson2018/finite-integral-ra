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

namespace RACert.S4N1.C0.S21

open RACert RACert.Problem

theorem cover3583 : P.CoversSplit 24 10 3583 0xfffafafafffaaaaafffafafafffaaaaafffafafafffaaaaafffafafafffaaaaafff8faf8aa88aa88ffc8fac8aa88aa88fff8faf8aa88aa88ffc8fac8aa88aa88fffafafafffaaaaafffafafafffaaaaafffafafafafaaaaafffafafafafaaaaafff8faf8aa88aa88ffc8fac8aa88aa88ffc8fac8aa88aa88ffc8fac8aa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1209, 1217, 1258, 1609]) (by decide +kernel)

theorem c3583_0 : P.sumLeaves 24 3668992 195 = 9047724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 0) (len := 195) (W := 9047724) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem c3583_1 : P.sumLeaves 24 3669187 150 = 20114624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 195) (len := 150) (W := 20114624) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem c3583_2 : P.sumLeaves 24 3669337 129 = 35946291 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 345) (len := 129) (W := 35946291) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem c3583_3 : P.sumLeaves 24 3669466 162 = 48635134 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 474) (len := 162) (W := 48635134) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem c3583_4 : P.sumLeaves 24 3669628 168 = 48274390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 636) (len := 168) (W := 48274390) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem c3583_5 : P.sumLeaves 24 3669796 128 = 66555242 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 804) (len := 128) (W := 66555242) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem c3583_6 : P.sumLeaves 24 3669924 92 = 88745156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3583) (lo := 932) (len := 92) (W := 88745156) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem h3583 : P.leaf 34 3583 = 317318561 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(195, 9047724), (150, 20114624), (129, 35946291), (162, 48635134), (168, 48274390), (128, 66555242), (92, 88745156)]) (.cons c3583_0 (.cons c3583_1 (.cons c3583_2 (.cons c3583_3 (.cons c3583_4 (.cons c3583_5 (.cons c3583_6 (.nil)))))))) (by decide) (by decide))

theorem cover3710 : P.CoversSplit 24 10 3710 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000003300330000000000000000000000000033003300000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000003300330000000000000000000000000033003300000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

noncomputable def f3710 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3799040 + i)

theorem c3710_0 : rowSum f3710 0 1024 = 7851704 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3710) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3710 (by decide)
  decide +kernel

theorem sum3710 : rowSum f3710 0 1024 = 7851704 :=
  c3710_0

theorem h3710 : P.leaf 34 3710 = 7851704 :=
  leaf_weighted (k := 24) (d := 10) (H := 3710) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 3710) (by decide) (by decide +kernel)) sum3710

theorem cover3711 : P.CoversSplit 24 10 3711 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000003300330000000000000000000000000033003300000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000003300330000000000000000000000000033003300000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

noncomputable def f3711 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3800064 + i)

theorem c3711_0 : rowSum f3711 0 1024 = 8174816 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3711 (by decide)
  decide +kernel

theorem sum3711 : rowSum f3711 0 1024 = 8174816 :=
  c3711_0

theorem h3711 : P.leaf 34 3711 = 8174816 :=
  leaf_weighted (k := 24) (d := 10) (H := 3711) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 3711) (by decide) (by decide +kernel)) sum3711

theorem h3748 : P.leaf 34 3748 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 466), (26, 1, 472), (35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h3749 : P.leaf 34 3749 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3750 : P.CoversSplit 24 10 3750 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3750_0 : P.sumLeaves 24 3840000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3750) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3750 (by decide)
  decide +kernel

theorem h3750 : P.leaf 34 3750 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3750_0 (.nil)) (by decide) (by decide))

theorem cover3751 : P.CoversSplit 24 10 3751 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3751_0 : P.sumLeaves 24 3841024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3751) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3751 (by decide)
  decide +kernel

theorem h3751 : P.leaf 34 3751 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3751_0 (.nil)) (by decide) (by decide))

theorem cover3752 : P.CoversSplit 24 10 3752 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 915, 1202, 1210, 1258]) (by decide +kernel)

theorem c3752_0 : P.sumLeaves 24 3842048 1024 = 17424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3752) (lo := 0) (len := 1024) (W := 17424) check rows elimOK (by decide) (by decide) cover3752 (by decide)
  decide +kernel

theorem h3752 : P.leaf 34 3752 = 17424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17424)]) (.cons c3752_0 (.nil)) (by decide) (by decide))

theorem cover3753 : P.CoversSplit 24 10 3753 0xcc00cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 915, 1202, 1210]) (by decide +kernel)

theorem c3753_0 : P.sumLeaves 24 3843072 1024 = 123456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3753) (lo := 0) (len := 1024) (W := 123456) check rows elimOK (by decide) (by decide) cover3753 (by decide)
  decide +kernel

theorem h3753 : P.leaf 34 3753 = 123456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 123456)]) (.cons c3753_0 (.nil)) (by decide) (by decide))

theorem cover3754 : P.CoversSplit 24 10 3754 0xaa000000a00000000000000000000000aa000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 565, 573, 916, 921, 1202, 1258]) (by decide +kernel)

theorem c3754_0 : P.sumLeaves 24 3844096 1024 = 269104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3754) (lo := 0) (len := 1024) (W := 269104) check rows elimOK (by decide) (by decide) cover3754 (by decide)
  decide +kernel

theorem h3754 : P.leaf 34 3754 = 269104 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 269104)]) (.cons c3754_0 (.nil)) (by decide) (by decide))

theorem cover3755 : P.CoversSplit 24 10 3755 0xff00ff00f00000000000000000000000ff00ff00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 565, 573, 916, 921, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c3755_0 : P.sumLeaves 24 3845120 1024 = 3097052 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3755) (lo := 0) (len := 1024) (W := 3097052) check rows elimOK (by decide) (by decide) cover3755 (by decide)
  decide +kernel

theorem h3755 : P.leaf 34 3755 = 3097052 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3097052)]) (.cons c3755_0 (.nil)) (by decide) (by decide))

theorem cover3756 : P.CoversSplit 24 10 3756 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 915, 1202, 1210, 1258]) (by decide +kernel)

theorem c3756_0 : P.sumLeaves 24 3846144 1024 = 111160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3756) (lo := 0) (len := 1024) (W := 111160) check rows elimOK (by decide) (by decide) cover3756 (by decide)
  decide +kernel

theorem h3756 : P.leaf 34 3756 = 111160 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 111160)]) (.cons c3756_0 (.nil)) (by decide) (by decide))

theorem cover3757 : P.CoversSplit 24 10 3757 0xcc00cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 915, 1202, 1210]) (by decide +kernel)

theorem c3757_0 : P.sumLeaves 24 3847168 1024 = 614224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3757) (lo := 0) (len := 1024) (W := 614224) check rows elimOK (by decide) (by decide) cover3757 (by decide)
  decide +kernel

theorem h3757 : P.leaf 34 3757 = 614224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 614224)]) (.cons c3757_0 (.nil)) (by decide) (by decide))

theorem cover3758 : P.CoversSplit 24 10 3758 0xaa000000a00000000000000000000000aa000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 916, 921, 1202, 1258]) (by decide +kernel)

theorem c3758_0 : P.sumLeaves 24 3848192 1024 = 1314276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3758) (lo := 0) (len := 1024) (W := 1314276) check rows elimOK (by decide) (by decide) cover3758 (by decide)
  decide +kernel

theorem h3758 : P.leaf 34 3758 = 1314276 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1314276)]) (.cons c3758_0 (.nil)) (by decide) (by decide))

theorem cover3759 : P.CoversSplit 24 10 3759 0xff00ff00f00000000000000000000000ff00ff00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 573, 916, 921, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c3759_0 : P.sumLeaves 24 3849216 1024 = 6350768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3759) (lo := 0) (len := 1024) (W := 6350768) check rows elimOK (by decide) (by decide) cover3759 (by decide)
  decide +kernel

theorem h3759 : P.leaf 34 3759 = 6350768 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6350768)]) (.cons c3759_0 (.nil)) (by decide) (by decide))

theorem cover3766 : P.CoversSplit 24 10 3766 0xff00ff00a00000000000000000000000aa00aa005500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 573, 915, 916, 921, 1202, 1209, 1210, 1217, 1259, 1308]) (ps := [(5, [475], [517]), (8, [531, 580], [517, 573])]) (by decide +kernel)

theorem c3766_0 : P.sumLeaves 24 3856384 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3766) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3766 (by decide)
  decide +kernel

theorem contract3766_1 : P.leaf 30 60263 = 47260 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60263) (ss := [(5, 1, 475), (8, 1, 580), (27, 1, 573), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 929), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 7, 8, 9, 10, 13, 15, 20, 21, 22, 24, 26, 28, 29, 5, 23]) (cs := [2, 3, 4, 1, 5, 19, 1, 6, 7, 8, 9, 1, 1, 10, 1, 11, 1, 1, 1, 1, 12, 13, 14, 20, 15, 1, 16, 1, 17, 18]) (bs := [17, 2]) (W := 47260) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3766_1 : P.sumLeaves 24 3856832 64 = 47260 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60263) rows (by decide) (by decide)).symm.trans contract3766_1

theorem c3766_2 : P.sumLeaves 24 3856896 512 = 995664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3766) (lo := 512) (len := 512) (W := 995664) check rows elimOK (by decide) (by decide) cover3766 (by decide)
  decide +kernel

theorem h3766 : P.leaf 34 3766 = 1042924 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 47260), (512, 995664)]) (.cons c3766_0 (.cons c3766_1 (.cons c3766_2 (.nil)))) (by decide) (by decide))

theorem cover3767 : P.CoversSplit 24 10 3767 0xff00ff00a00000000000000000000000ff00ff00a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 915, 916, 921, 1202, 1210, 1259, 1308]) (ps := [(8, [580], [573])]) (by decide +kernel)

theorem c3767_0 : P.sumLeaves 24 3857408 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3767) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3767 (by decide)
  decide +kernel

theorem contract3767_1 : P.leaf 30 60279 = 62800 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60279) (ss := [(5, 1, 475), (8, 1, 580), (27, 1, 573), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 929), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 7, 8, 9, 10, 13, 15, 20, 21, 22, 24, 26, 28, 29, 5, 23]) (cs := [2, 3, 4, 1, 5, 19, 1, 6, 7, 8, 9, 1, 1, 10, 1, 11, 1, 1, 1, 1, 12, 13, 14, 20, 15, 1, 16, 1, 17, 18]) (bs := [17, 2]) (W := 62800) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3767_1 : P.sumLeaves 24 3857856 64 = 62800 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60279) rows (by decide) (by decide)).symm.trans contract3767_1

theorem c3767_2 : P.sumLeaves 24 3857920 512 = 2313376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3767) (lo := 512) (len := 512) (W := 2313376) check rows elimOK (by decide) (by decide) cover3767 (by decide)
  decide +kernel

theorem h3767 : P.leaf 34 3767 = 2376176 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 62800), (512, 2313376)]) (.cons c3767_0 (.cons c3767_1 (.cons c3767_2 (.nil)))) (by decide) (by decide))

theorem cover3768 : P.CoversSplit 24 10 3768 0xff00ff00f00000000000000000000000af00af00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 487, 508, 517, 566, 915, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c3768_0 : P.sumLeaves 24 3858432 1024 = 206728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3768) (lo := 0) (len := 1024) (W := 206728) check rows elimOK (by decide) (by decide) cover3768 (by decide)
  decide +kernel

theorem h3768 : P.leaf 34 3768 = 206728 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 206728)]) (.cons c3768_0 (.nil)) (by decide) (by decide))

theorem cover3769 : P.CoversSplit 24 10 3769 0xff00ff00f00000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 487, 517, 566, 573, 915, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c3769_0 : P.sumLeaves 24 3859456 1024 = 1900216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3769) (lo := 0) (len := 1024) (W := 1900216) check rows elimOK (by decide) (by decide) cover3769 (by decide)
  decide +kernel

theorem h3769 : P.leaf 34 3769 = 1900216 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1900216)]) (.cons c3769_0 (.nil)) (by decide) (by decide))

theorem cover3770 : P.CoversSplit 24 10 3770 0xff00ff00f00000000000000000000000af00af000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 487, 517, 573, 916, 921, 1202, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c3770_0 : P.sumLeaves 24 3860480 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3770) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3770 (by decide)
  decide +kernel

theorem contract3770_1 : P.leaf 30 60327 = 43552 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60327) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 15, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 1, 1, 12, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 43552) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3770_1 : P.sumLeaves 24 3860928 64 = 43552 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60327) rows (by decide) (by decide)).symm.trans contract3770_1

theorem c3770_2 : P.sumLeaves 24 3860992 512 = 2050532 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3770) (lo := 512) (len := 512) (W := 2050532) check rows elimOK (by decide) (by decide) cover3770 (by decide)
  decide +kernel

theorem h3770 : P.leaf 34 3770 = 2094084 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 43552), (512, 2050532)]) (.cons c3770_0 (.cons c3770_1 (.cons c3770_2 (.nil)))) (by decide) (by decide))

theorem cover3771 : P.CoversSplit 24 10 3771 0xff00ff00f00000000000000000000000ff00ff00f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 517, 573, 916, 921, 1202, 1209, 1210, 1259, 1308]) (by decide +kernel)

theorem c3771_0 : P.sumLeaves 24 3861504 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3771) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3771 (by decide)
  decide +kernel

theorem contract3771_1 : P.leaf 30 60343 = 62168 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60343) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 15, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 1, 1, 12, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 62168) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3771_1 : P.sumLeaves 24 3861952 64 = 62168 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60343) rows (by decide) (by decide)).symm.trans contract3771_1

theorem c3771_2 : P.sumLeaves 24 3862016 512 = 6052960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3771) (lo := 512) (len := 512) (W := 6052960) check rows elimOK (by decide) (by decide) cover3771 (by decide)
  decide +kernel

theorem h3771 : P.leaf 34 3771 = 6115128 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 62168), (512, 6052960)]) (.cons c3771_0 (.cons c3771_1 (.cons c3771_2 (.nil)))) (by decide) (by decide))

theorem cover3772 : P.CoversSplit 24 10 3772 0xff00ff00f00000000000000000000000af00af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 566, 573, 915, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c3772_0 : P.sumLeaves 24 3862528 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3772) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3772 (by decide)
  decide +kernel

theorem contract3772_1 : P.leaf 30 60359 = 33384 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 60359) (ss := [(18, 11, 475), (11, 1, 487), (8, 1, 580), (27, 1, 573), (6, 1, 459), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 10, 13, 15, 20, 21, 22, 24, 26, 28, 29, 5, 23]) (cs := [2, 3, 4, 5, 1, 18, 1, 6, 7, 1, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 11, 12, 13, 19, 14, 1, 15, 1, 16, 17]) (bs := [16, 2]) (W := 33384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3772_1 : P.sumLeaves 24 3862976 64 = 33384 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60359) rows (by decide) (by decide)).symm.trans contract3772_1

theorem c3772_2 : P.sumLeaves 24 3863040 512 = 1252844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3772) (lo := 512) (len := 512) (W := 1252844) check rows elimOK (by decide) (by decide) cover3772 (by decide)
  decide +kernel

theorem h3772 : P.leaf 34 3772 = 1286228 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 33384), (512, 1252844)]) (.cons c3772_0 (.cons c3772_1 (.cons c3772_2 (.nil)))) (by decide) (by decide))

theorem cover3773 : P.CoversSplit 24 10 3773 0xff00ff00f00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 915, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c3773_0 : P.sumLeaves 24 3863552 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3773) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3773 (by decide)
  decide +kernel

theorem contract3773_1 : P.leaf 30 60375 = 78000 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60375) (ss := [(18, 11, 475), (11, 1, 487), (8, 1, 580), (27, 1, 573), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 10, 13, 15, 20, 21, 22, 24, 26, 28, 29, 5, 23]) (cs := [2, 3, 4, 5, 6, 19, 1, 7, 8, 1, 9, 1, 1, 10, 1, 11, 1, 1, 1, 1, 12, 13, 14, 20, 15, 1, 16, 1, 17, 18]) (bs := [17, 2]) (W := 78000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3773_1 : P.sumLeaves 24 3864000 64 = 78000 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60375) rows (by decide) (by decide)).symm.trans contract3773_1

theorem c3773_2 : P.sumLeaves 24 3864064 512 = 3770116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3773) (lo := 512) (len := 512) (W := 3770116) check rows elimOK (by decide) (by decide) cover3773 (by decide)
  decide +kernel

theorem h3773 : P.leaf 34 3773 = 3848116 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 78000), (512, 3770116)]) (.cons c3773_0 (.cons c3773_1 (.cons c3773_2 (.nil)))) (by decide) (by decide))

theorem cover3774 : P.CoversSplit 24 10 3774 0xff00ff00f00000000000000000000000af00af000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 524, 573, 916, 921, 1202, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c3774_0 : P.sumLeaves 24 3864576 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3774) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3774 (by decide)
  decide +kernel

theorem contract3774_1 : P.leaf 30 60391 = 113476 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 60391) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 13, 15, 20, 21, 22, 24, 26, 28, 29, 5, 23]) (cs := [2, 3, 4, 5, 6, 20, 1, 7, 8, 9, 10, 1, 1, 11, 1, 12, 1, 1, 1, 1, 13, 14, 15, 21, 16, 1, 17, 1, 18, 19]) (bs := [18, 2]) (W := 113476) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3774_1 : P.sumLeaves 24 3865024 64 = 113476 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60391) rows (by decide) (by decide)).symm.trans contract3774_1

theorem c3774_2 : P.sumLeaves 24 3865088 512 = 5210804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3774) (lo := 512) (len := 512) (W := 5210804) check rows elimOK (by decide) (by decide) cover3774 (by decide)
  decide +kernel

theorem h3774 : P.leaf 34 3774 = 5324280 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 113476), (512, 5210804)]) (.cons c3774_0 (.cons c3774_1 (.cons c3774_2 (.nil)))) (by decide) (by decide))

theorem cover3775 : P.CoversSplit 24 10 3775 0xff00ff00f00000000000000000000000ff00ff00f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 573, 916, 921, 1202, 1209, 1210, 1259, 1308]) (by decide +kernel)

theorem c3775_0 : P.sumLeaves 24 3865600 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3775) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3775 (by decide)
  decide +kernel

theorem contract3775_1 : P.leaf 30 60407 = 160432 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 60407) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 5, 15, 23]) (cs := [2, 3, 4, 5, 6, 19, 1, 7, 8, 9, 10, 1, 1, 11, 1, 20, 1, 1, 1, 1, 12, 13, 14, 21, 15, 1, 16, 1, 17, 18]) (bs := [17, 3]) (W := 160432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3775_1 : P.sumLeaves 24 3866048 64 = 160432 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60407) rows (by decide) (by decide)).symm.trans contract3775_1

theorem c3775_2 : P.sumLeaves 24 3866112 512 = 10638372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3775) (lo := 512) (len := 512) (W := 10638372) check rows elimOK (by decide) (by decide) cover3775 (by decide)
  decide +kernel

theorem h3775 : P.leaf 34 3775 = 10798804 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 160432), (512, 10638372)]) (.cons c3775_0 (.cons c3775_1 (.cons c3775_2 (.nil)))) (by decide) (by decide))

theorem cover3784 : P.CoversSplit 24 10 3784 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 474, 508, 515, 516, 522, 523, 536, 573, 915, 1202, 1210, 1651]) (ps := [(14, [929], [487])]) (by decide +kernel)

theorem c3784_0 : P.sumLeaves 24 3874816 1024 = 16382 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3784) (lo := 0) (len := 1024) (W := 16382) check rows elimOK (by decide) (by decide) cover3784 (by decide)
  decide +kernel

theorem h3784 : P.leaf 34 3784 = 16382 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16382)]) (.cons c3784_0 (.nil)) (by decide) (by decide))

theorem cover3785 : P.CoversSplit 24 10 3785 0xcc00cc00c4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 474, 515, 522, 536, 573, 915, 1202, 1210, 1217, 1651]) (ps := [(14, [929], [487])]) (by decide +kernel)

theorem c3785_0 : P.sumLeaves 24 3875840 1024 = 103190 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3785) (lo := 0) (len := 1024) (W := 103190) check rows elimOK (by decide) (by decide) cover3785 (by decide)
  decide +kernel

theorem h3785 : P.leaf 34 3785 = 103190 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 103190)]) (.cons c3785_0 (.nil)) (by decide) (by decide))

theorem cover3786 : P.CoversSplit 24 10 3786 0xaa000000a10000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 536, 916, 1202]) (by decide +kernel)

theorem c3786_0 : P.sumLeaves 24 3876864 1024 = 307470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3786) (lo := 0) (len := 1024) (W := 307470) check rows elimOK (by decide) (by decide) cover3786 (by decide)
  decide +kernel

theorem h3786 : P.leaf 34 3786 = 307470 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 307470)]) (.cons c3786_0 (.nil)) (by decide) (by decide))

theorem cover3787 : P.CoversSplit 24 10 3787 0xff00ff00f40000000000000000000000ff00ff00f40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 536, 916, 1202, 1210]) (by decide +kernel)

theorem c3787_0 : P.sumLeaves 24 3877888 1024 = 2721896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3787) (lo := 0) (len := 1024) (W := 2721896) check rows elimOK (by decide) (by decide) cover3787 (by decide)
  decide +kernel

theorem h3787 : P.leaf 34 3787 = 2721896 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2721896)]) (.cons c3787_0 (.nil)) (by decide) (by decide))

theorem cover3788 : P.CoversSplit 24 10 3788 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 915, 1202, 1210, 1258, 1651]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c3788_0 : P.sumLeaves 24 3878912 1024 = 101728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3788) (lo := 0) (len := 1024) (W := 101728) check rows elimOK (by decide) (by decide) cover3788 (by decide)
  decide +kernel

theorem h3788 : P.leaf 34 3788 = 101728 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 101728)]) (.cons c3788_0 (.nil)) (by decide) (by decide))

theorem cover3789 : P.CoversSplit 24 10 3789 0xcc00cc00c4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 915, 1202, 1210, 1217, 1651]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c3789_0 : P.sumLeaves 24 3879936 1024 = 605096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3789) (lo := 0) (len := 1024) (W := 605096) check rows elimOK (by decide) (by decide) cover3789 (by decide)
  decide +kernel

theorem h3789 : P.leaf 34 3789 = 605096 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 605096)]) (.cons c3789_0 (.nil)) (by decide) (by decide))

theorem cover3790 : P.CoversSplit 24 10 3790 0xaa000000a10000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 916, 921, 1202, 1258]) (by decide +kernel)

theorem c3790_0 : P.sumLeaves 24 3880960 1024 = 957728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3790) (lo := 0) (len := 1024) (W := 957728) check rows elimOK (by decide) (by decide) cover3790 (by decide)
  decide +kernel

theorem h3790 : P.leaf 34 3790 = 957728 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 957728)]) (.cons c3790_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3583, 12), (3710, 4), (3711, 4), (3748, 24), (3749, 24), (3750, 48), (3751, 48), (3752, 48), (3753, 48), (3754, 48), (3755, 48), (3756, 48), (3757, 48), (3758, 48), (3759, 48), (3766, 24), (3767, 24), (3768, 48), (3769, 48), (3770, 48), (3771, 48), (3772, 48), (3773, 48), (3774, 48), (3775, 48), (3784, 24), (3785, 24), (3786, 48), (3787, 48), (3788, 48), (3789, 48), (3790, 48)]

theorem segOK : checkSeg 16 perms 3583 3791 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3583 3791 1268 6268775308 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6268775308)
    (SegSum.cons (w := 12) h3583 (SegSum.cons (w := 4) h3710 (SegSum.cons (w := 4) h3711 (SegSum.cons (w := 24) h3748 (SegSum.cons (w := 24) h3749 (SegSum.cons (w := 48) h3750 (SegSum.cons (w := 48) h3751 (SegSum.cons (w := 48) h3752 (SegSum.cons (w := 48) h3753 (SegSum.cons (w := 48) h3754 (SegSum.cons (w := 48) h3755 (SegSum.cons (w := 48) h3756 (SegSum.cons (w := 48) h3757 (SegSum.cons (w := 48) h3758 (SegSum.cons (w := 48) h3759 (SegSum.cons (w := 24) h3766 (SegSum.cons (w := 24) h3767 (SegSum.cons (w := 48) h3768 (SegSum.cons (w := 48) h3769 (SegSum.cons (w := 48) h3770 (SegSum.cons (w := 48) h3771 (SegSum.cons (w := 48) h3772 (SegSum.cons (w := 48) h3773 (SegSum.cons (w := 48) h3774 (SegSum.cons (w := 48) h3775 (SegSum.cons (w := 24) h3784 (SegSum.cons (w := 24) h3785 (SegSum.cons (w := 48) h3786 (SegSum.cons (w := 48) h3787 (SegSum.cons (w := 48) h3788 (SegSum.cons (w := 48) h3789 (SegSum.cons (w := 48) h3790 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S21
