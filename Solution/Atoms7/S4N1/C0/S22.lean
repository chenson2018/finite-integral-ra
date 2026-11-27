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

namespace RACert.S4N1.C0.S22

open RACert RACert.Problem

theorem cover3791 : P.CoversSplit 24 10 3791 0xff00ff00f40000000000000000000000ff00ff00f40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 916, 921, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c3791_0 : P.sumLeaves 24 3881984 1024 = 7870452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3791) (lo := 0) (len := 1024) (W := 7870452) check rows elimOK (by decide) (by decide) cover3791 (by decide)
  decide +kernel

theorem h3791 : P.leaf 34 3791 = 7870452 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7870452)]) (.cons c3791_0 (.nil)) (by decide) (by decide))

theorem cover3802 : P.CoversSplit 24 10 3802 0xff00ff00f50000000000000000000000aa00aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000880088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 487, 516, 573, 916, 921, 1202, 1209, 1210, 1259]) (ps := [(8, [537], [516]), (14, [509], [1266])]) (by decide +kernel)

theorem c3802_0 : P.sumLeaves 24 3893248 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3802) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover3802 (by decide)
  decide +kernel

theorem contract3802_1 : P.leaf 30 60837 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 467), (27, 1, 573), (29, 1, 916), (8, 0, 1266), (20, 1, 531), (21, 0, 537), (14, 0, 580), (26, 1, 509), (5, 1, 608), (12, 1, 460), (31, 1, 516)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3802_1 : P.sumLeaves 24 3893568 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60837) rows (by decide) (by decide)).symm.trans contract3802_1

theorem c3802_2 : P.sumLeaves 24 3893632 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3802) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover3802 (by decide)
  decide +kernel

theorem contract3802_3 : P.leaf 30 60839 = 34096 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 60839) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 13, 14, 19, 15, 1, 16, 1, 17, 18]) (bs := [17, 1]) (W := 34096) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3802_3 : P.sumLeaves 24 3893696 64 = 34096 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60839) rows (by decide) (by decide)).symm.trans contract3802_3

theorem c3802_4 : P.sumLeaves 24 3893760 512 = 2079186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3802) (lo := 512) (len := 512) (W := 2079186) check rows elimOK (by decide) (by decide) cover3802 (by decide)
  decide +kernel

theorem h3802 : P.leaf 34 3802 = 2113282 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (64, 0), (64, 34096), (512, 2079186)]) (.cons c3802_0 (.cons c3802_1 (.cons c3802_2 (.cons c3802_3 (.cons c3802_4 (.nil)))))) (by decide) (by decide))

theorem cover3803 : P.CoversSplit 24 10 3803 0xff00ff00f50000000000000000000000ff00ff00f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000cc00cc008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [487, 516, 573, 916, 921, 1202, 1210, 1217, 1259]) (ps := [(14, [1217], [1266])]) (by decide +kernel)

theorem c3803_0 : P.sumLeaves 24 3894272 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3803) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover3803 (by decide)
  decide +kernel

theorem contract3803_1 : P.leaf 30 60853 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 537), (20, 1, 482), (21, 0, 488), (5, 1, 608), (12, 1, 825)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3803_1 : P.sumLeaves 24 3894592 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60853) rows (by decide) (by decide)).symm.trans contract3803_1

theorem c3803_2 : P.sumLeaves 24 3894656 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3803) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover3803 (by decide)
  decide +kernel

theorem contract3803_3 : P.leaf 30 60855 = 41088 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 60855) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 13, 14, 19, 15, 1, 16, 1, 17, 18]) (bs := [17, 1]) (W := 41088) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3803_3 : P.sumLeaves 24 3894720 64 = 41088 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60855) rows (by decide) (by decide)).symm.trans contract3803_3

theorem c3803_4 : P.sumLeaves 24 3894784 512 = 5304362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3803) (lo := 512) (len := 512) (W := 5304362) check rows elimOK (by decide) (by decide) cover3803 (by decide)
  decide +kernel

theorem h3803 : P.leaf 34 3803 = 5345450 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (64, 0), (64, 41088), (512, 5304362)]) (.cons c3803_0 (.cons c3803_1 (.cons c3803_2 (.cons c3803_3 (.cons c3803_4 (.nil)))))) (by decide) (by decide))

theorem cover3804 : P.CoversSplit 24 10 3804 0xff00ff00f00000000000000000000000aa00af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 915, 1202, 1209, 1210, 1259, 1264]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c3804_0 : P.sumLeaves 24 3895296 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3804) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3804 (by decide)
  decide +kernel

theorem contract3804_1 : P.leaf 30 60871 = 26194 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60871) (ss := [(18, 1, 475), (27, 1, 573), (8, 1, 580), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 26194) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3804_1 : P.sumLeaves 24 3895744 64 = 26194 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60871) rows (by decide) (by decide)).symm.trans contract3804_1

theorem c3804_2 : P.sumLeaves 24 3895808 512 = 2007954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3804) (lo := 512) (len := 512) (W := 2007954) check rows elimOK (by decide) (by decide) cover3804 (by decide)
  decide +kernel

theorem h3804 : P.leaf 34 3804 = 2034148 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 26194), (512, 2007954)]) (.cons c3804_0 (.cons c3804_1 (.cons c3804_2 (.nil)))) (by decide) (by decide))

theorem cover3805 : P.CoversSplit 24 10 3805 0xff00ff00f50000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 915, 1202, 1209, 1210, 1259, 1264]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c3805_0 : P.sumLeaves 24 3896320 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3805) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3805 (by decide)
  decide +kernel

theorem contract3805_1 : P.leaf 30 60887 = 74700 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60887) (ss := [(18, 1, 475), (27, 1, 573), (8, 1, 580), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 74700) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3805_1 : P.sumLeaves 24 3896768 64 = 74700 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60887) rows (by decide) (by decide)).symm.trans contract3805_1

theorem c3805_2 : P.sumLeaves 24 3896832 512 = 7227044 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3805) (lo := 512) (len := 512) (W := 7227044) check rows elimOK (by decide) (by decide) cover3805 (by decide)
  decide +kernel

theorem h3805 : P.leaf 34 3805 = 7301744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 74700), (512, 7227044)]) (.cons c3805_0 (.cons c3805_1 (.cons c3805_2 (.nil)))) (by decide) (by decide))

theorem cover3806 : P.CoversSplit 24 10 3806 0xff00ff00f50000000000000000000000aa00af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 916, 921, 1202, 1209, 1210, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c3806_0 : P.sumLeaves 24 3897344 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3806) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3806 (by decide)
  decide +kernel

theorem contract3806_1 : P.leaf 30 60903 = 81888 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60903) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 81888) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3806_1 : P.sumLeaves 24 3897792 64 = 81888 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60903) rows (by decide) (by decide)).symm.trans contract3806_1

theorem c3806_2 : P.sumLeaves 24 3897856 512 = 8745720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3806) (lo := 512) (len := 512) (W := 8745720) check rows elimOK (by decide) (by decide) cover3806 (by decide)
  decide +kernel

theorem h3806 : P.leaf 34 3806 = 8827608 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 81888), (512, 8745720)]) (.cons c3806_0 (.cons c3806_1 (.cons c3806_2 (.nil)))) (by decide) (by decide))

theorem cover3807 : P.CoversSplit 24 10 3807 0xff00ff00f50000000000000000000000ff00ff00f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 916, 921, 1202, 1209, 1210, 1217, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c3807_0 : P.sumLeaves 24 3898368 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3807) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3807 (by decide)
  decide +kernel

theorem contract3807_1 : P.leaf 30 60919 = 93848 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 60919) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 93848) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3807_1 : P.sumLeaves 24 3898816 64 = 93848 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 60919) rows (by decide) (by decide)).symm.trans contract3807_1

theorem c3807_2 : P.sumLeaves 24 3898880 512 = 13675504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3807) (lo := 512) (len := 512) (W := 13675504) check rows elimOK (by decide) (by decide) cover3807 (by decide)
  decide +kernel

theorem h3807 : P.leaf 34 3807 = 13769352 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 93848), (512, 13675504)]) (.cons c3807_0 (.cons c3807_1 (.cons c3807_2 (.nil)))) (by decide) (by decide))

theorem cover3820 : P.CoversSplit 24 10 3820 0x8800000088000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 915, 1210, 1258, 1308, 1651]) (by decide +kernel)

theorem c3820_0 : P.sumLeaves 24 3911680 1024 = 648904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3820) (lo := 0) (len := 1024) (W := 648904) check rows elimOK (by decide) (by decide) cover3820 (by decide)
  decide +kernel

theorem h3820 : P.leaf 34 3820 = 648904 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 648904)]) (.cons c3820_0 (.nil)) (by decide) (by decide))

theorem cover3821 : P.CoversSplit 24 10 3821 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 915, 1210, 1217, 1308, 1651]) (by decide +kernel)

theorem c3821_0 : P.sumLeaves 24 3912704 1024 = 3341336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3821) (lo := 0) (len := 1024) (W := 3341336) check rows elimOK (by decide) (by decide) cover3821 (by decide)
  decide +kernel

theorem h3821 : P.leaf 34 3821 = 3341336 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3341336)]) (.cons c3821_0 (.nil)) (by decide) (by decide))

theorem cover3822 : P.CoversSplit 24 10 3822 0xaa000000ab0000000000000000000000aa000000ab0000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 916, 921, 1210, 1258, 1308]) (by decide +kernel)

theorem c3822_0 : P.sumLeaves 24 3913728 1024 = 5677396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3822) (lo := 0) (len := 1024) (W := 5677396) check rows elimOK (by decide) (by decide) cover3822 (by decide)
  decide +kernel

theorem h3822 : P.leaf 34 3822 = 5677396 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5677396)]) (.cons c3822_0 (.nil)) (by decide) (by decide))

theorem cover3823 : P.CoversSplit 24 10 3823 0xff00ff00fe0000000000000000000000ff00ff00fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 916, 921, 1209, 1210, 1217, 1258, 1308]) (by decide +kernel)

theorem c3823_0 : P.sumLeaves 24 3914752 1024 = 13838986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3823) (lo := 0) (len := 1024) (W := 13838986) check rows elimOK (by decide) (by decide) cover3823 (by decide)
  decide +kernel

theorem h3823 : P.leaf 34 3823 = 13838986 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13838986)]) (.cons c3823_0 (.nil)) (by decide) (by decide))

theorem cover3838 : P.CoversSplit 24 10 3838 0xff00ff00ff0000000000000000000000ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 915, 916, 921, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c3838_0 : P.sumLeaves 24 3930112 1024 = 23702292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3838) (lo := 0) (len := 1024) (W := 23702292) check rows elimOK (by decide) (by decide) cover3838 (by decide)
  decide +kernel

theorem h3838 : P.leaf 34 3838 = 23702292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23702292)]) (.cons c3838_0 (.nil)) (by decide) (by decide))

theorem cover3839 : P.CoversSplit 24 10 3839 0xff00ff00ff0000000000000000000000ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 915, 916, 921, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c3839_0 : P.sumLeaves 24 3931136 1024 = 23702292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3839) (lo := 0) (len := 1024) (W := 23702292) check rows elimOK (by decide) (by decide) cover3839 (by decide)
  decide +kernel

theorem h3839 : P.leaf 34 3839 = 23702292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23702292)]) (.cons c3839_0 (.nil)) (by decide) (by decide))

theorem cover3987 : P.CoversSplit 24 10 3987 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaa00aa00ff00ff00aa00aa00ffffffffaa00aa00ff00ff00aa00aa00ffffffffffffaaaaffffffffffffaaaaffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffaa00aa00ff00ff00aa00aa00cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 915, 1209, 1217, 1258, 1609]) (ps := [(8, [1217, 1609], [1266]), (14, [1217, 1609], [1266])]) (by decide +kernel)

noncomputable def f3987 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (4082688 + i)

theorem c3987_0 : rowSum f3987 0 307 = 210958 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3987) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3987 (by decide)
  decide +kernel

theorem c3987_1 : rowSum f3987 307 166 = 779128 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3987) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3987 (by decide)
  decide +kernel

theorem c3987_2 : rowSum f3987 473 294 = 2683696 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3987) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3987 (by decide)
  decide +kernel

theorem c3987_3 : rowSum f3987 767 257 = 5413080 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3987) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3987 (by decide)
  decide +kernel

theorem sum3987 : rowSum f3987 0 1024 = 9086862 :=
  rowSum_append (F := f3987) (lo := 0) (n := 307) (m := 717) (A := 210958) (B := 8875904) c3987_0 (rowSum_append (F := f3987) (lo := 307) (n := 166) (m := 551) (A := 779128) (B := 8096776) c3987_1 (rowSum_append (F := f3987) (lo := 473) (n := 294) (m := 257) (A := 2683696) (B := 5413080) c3987_2 (c3987_3)))

theorem h3987 : P.leaf 34 3987 = 9086862 :=
  leaf_weighted (k := 24) (d := 10) (H := 3987) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3987) (by decide) (by decide +kernel)) sum3987

theorem cover3988 : P.CoversSplit 24 10 3988 0xaa00aa0000000a00aa00aa0000000000aa00aa0000000a00aa00aa00000000000000000000000000220000000000000000000000000000002200000000000000aa00aa0000000a00aa00aa0000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 475, 479, 508, 510, 516, 559, 915, 916]) (ps := [(5, [524, 566], [516]), (8, [537], [1266]), (12, [866, 908], [915])]) (by decide +kernel)

noncomputable def f3988 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (4083712 + i)

theorem c3988_0 : rowSum f3988 0 1024 = 340224 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3988) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover3988 (by decide)
  decide +kernel

theorem sum3988 : rowSum f3988 0 1024 = 340224 :=
  c3988_0

theorem h3988 : P.leaf 34 3988 = 340224 :=
  leaf_weighted (k := 24) (d := 10) (H := 3988) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 3988) (by decide) (by decide +kernel)) sum3988

theorem cover3989 : P.CoversSplit 24 10 3989 0xff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa000000000000000000220000002200000000000000000000002200000022000000ff00ff00ff00aa00ff00ff00ff00aa00000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 475, 516, 517, 559, 915, 916, 1209, 1217]) (ps := [(8, [615], [1266]), (12, [479, 866], [915])]) (by decide +kernel)

theorem c3989_0 : P.sumLeaves 24 4084736 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3989) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3989 (by decide)
  decide +kernel

theorem contract3989_1 : P.leaf 30 63826 = 1568 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 63826) (ss := [(29, 2, 475), (2, 1, 473), (3, 1, 523), (5, 1, 524), (12, 0, 915), (26, 1, 479), (6, 1, 817), (10, 1, 803), (30, 1, 866), (27, 0, 916), (14, 1, 929), (19, 1, 929), (18, 1, 965), (25, 1, 573), (13, 1, 922), (16, 1, 1265)]) (ids := [2, 5, 6, 7, 9, 13, 15, 18, 19, 20, 21, 22, 26, 29]) (cs := [1, 1, 2, 1, 1, 3, 4, 5, 1, 6, 0, 1, 1, 7, 1, 8, 1, 1, 9, 10, 11, 12, 13, 1, 1, 0, 14, 1, 1, 15]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3989_1 : P.sumLeaves 24 4084864 64 = 1568 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 63826) rows (by decide) (by decide)).symm.trans contract3989_1

theorem c3989_2 : P.sumLeaves 24 4084928 320 = 390624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3989) (lo := 192) (len := 320) (W := 390624) check rows elimOK (by decide) (by decide) cover3989 (by decide)
  decide +kernel

theorem contract3989_3 : P.leaf 30 63832 = 1872 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 63832) (ss := [(29, 1, 475), (3, 1, 523), (5, 1, 524), (8, 1, 531), (16, 1, 531), (17, 1, 615), (12, 0, 915), (26, 1, 510), (9, 1, 538), (6, 1, 817), (10, 1, 803), (30, 1, 866), (27, 0, 916), (25, 1, 573), (18, 1, 1265), (19, 1, 1273)]) (ids := [0, 2, 5, 9, 11, 12, 13, 18, 19, 20, 21, 22, 26, 29]) (cs := [2, 1, 3, 1, 1, 4, 1, 1, 1, 5, 0, 6, 7, 8, 1, 1, 1, 1, 9, 10, 11, 12, 13, 1, 1, 0, 14, 1, 1, 15]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3989_3 : P.sumLeaves 24 4085248 64 = 1872 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 63832) rows (by decide) (by decide)).symm.trans contract3989_3

theorem c3989_4 : P.sumLeaves 24 4085312 412 = 2449532 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3989) (lo := 576) (len := 412) (W := 2449532) check rows elimOK (by decide) (by decide) cover3989 (by decide)
  decide +kernel

theorem c3989_5 : P.sumLeaves 24 4085724 36 = 2496754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3989) (lo := 988) (len := 36) (W := 2496754) check rows elimOK (by decide) (by decide) cover3989 (by decide)
  decide +kernel

theorem h3989 : P.leaf 34 3989 = 5340350 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 1568), (320, 390624), (64, 1872), (412, 2449532), (36, 2496754)]) (.cons c3989_0 (.cons c3989_1 (.cons c3989_2 (.cons c3989_3 (.cons c3989_4 (.cons c3989_5 (.nil))))))) (by decide) (by decide))

theorem cover3991 : P.CoversSplit 24 10 3991 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaa00aa00ff00ff00aa00aa00ffffffffaa00aa00ff00ff00aa00aa00ffffffffffffaaaaffffffffffffaaaa00000000000000000000000000000000ffffffffaa00aa00ff00ff00aa00aa0000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 915, 1209, 1217, 1258, 1609]) (ps := [(8, [615], [1266])]) (by decide +kernel)

noncomputable def f3991 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (4086784 + i)

theorem c3991_0 : rowSum f3991 0 424 = 815072 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3991) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover3991 (by decide)
  decide +kernel

theorem c3991_1 : rowSum f3991 424 273 = 3903992 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3991) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover3991 (by decide)
  decide +kernel

theorem c3991_2 : rowSum f3991 697 327 = 18311792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3991) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover3991 (by decide)
  decide +kernel

theorem sum3991 : rowSum f3991 0 1024 = 23030856 :=
  rowSum_append (F := f3991) (lo := 0) (n := 424) (m := 600) (A := 815072) (B := 22215784) c3991_0 (rowSum_append (F := f3991) (lo := 424) (n := 273) (m := 327) (A := 3903992) (B := 18311792) c3991_1 (c3991_2))

theorem h3991 : P.leaf 34 3991 = 23030856 :=
  leaf_weighted (k := 24) (d := 10) (H := 3991) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 3991) (by decide) (by decide +kernel)) sum3991

theorem cover3996 : P.CoversSplit 24 10 3996 0xaa00af0000000a00aa22af2200000a02aa00af0000000a00aa00af0000000a000000000000000000220023000000020000000000000000002200230000000200aa00aa0000000a00aa22aa2200000a02000000000000000000000000000000000000000000000000220022000000020000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 915]) (ps := [(8, [531], [516, 1266]), (14, [923], [915])]) (by decide +kernel)

noncomputable def f3996 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (4091904 + i)

theorem c3996_0 : rowSum f3996 0 1024 = 1939458 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3996) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3996 (by decide)
  decide +kernel

theorem sum3996 : rowSum f3996 0 1024 = 1939458 :=
  c3996_0

theorem h3996 : P.leaf 34 3996 = 1939458 :=
  leaf_weighted (k := 24) (d := 10) (H := 3996) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3996) (by decide) (by decide +kernel)) sum3996

theorem cover3997 : P.CoversSplit 24 10 3997 0xff00ff00ff00aa00ff33ff33ff33aa22ff00ff00ff00aa00ff00ff00ff00aa000000000000000000330033002200220000000000000000003300330022002200ff00ff00ff00aa00ff33ff33ff33aa22000000000000000000000000000000000000000000000000330033002200220000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 915, 1209, 1217]) (ps := [(8, [1217], [1266]), (14, [923], [915, 1266])]) (by decide +kernel)

theorem c3997_0 : P.sumLeaves 24 4092928 665 = 4496138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3997) (lo := 0) (len := 665) (W := 4496138) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem c3997_1 : P.sumLeaves 24 4093593 279 = 7500979 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3997) (lo := 665) (len := 279) (W := 7500979) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem c3997_2 : P.sumLeaves 24 4093872 80 = 23714829 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3997) (lo := 944) (len := 80) (W := 23714829) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem h3997 : P.leaf 34 3997 = 35711946 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(665, 4496138), (279, 7500979), (80, 23714829)]) (.cons c3997_0 (.cons c3997_1 (.cons c3997_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3791, 48), (3802, 24), (3803, 24), (3804, 48), (3805, 48), (3806, 48), (3807, 48), (3820, 24), (3821, 24), (3822, 48), (3823, 48), (3838, 24), (3839, 24), (3987, 3), (3988, 24), (3989, 48), (3991, 24), (3996, 12), (3997, 24)]

theorem segOK : checkSeg 16 perms 3791 3999 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3791 3999 615 5984693778 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5984693778)
    (SegSum.cons (w := 48) h3791 (SegSum.cons (w := 24) h3802 (SegSum.cons (w := 24) h3803 (SegSum.cons (w := 48) h3804 (SegSum.cons (w := 48) h3805 (SegSum.cons (w := 48) h3806 (SegSum.cons (w := 48) h3807 (SegSum.cons (w := 24) h3820 (SegSum.cons (w := 24) h3821 (SegSum.cons (w := 48) h3822 (SegSum.cons (w := 48) h3823 (SegSum.cons (w := 24) h3838 (SegSum.cons (w := 24) h3839 (SegSum.cons (w := 3) h3987 (SegSum.cons (w := 24) h3988 (SegSum.cons (w := 48) h3989 (SegSum.cons (w := 24) h3991 (SegSum.cons (w := 12) h3996 (SegSum.cons (w := 24) h3997 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S22
