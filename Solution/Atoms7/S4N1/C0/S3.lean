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

namespace RACert.S4N1.C0.S3

open RACert RACert.Problem

theorem cover571 : P.CoversSplit 24 10 571 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000800000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 517, 529, 572, 573, 866, 871, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [572])]) (by decide +kernel)

theorem c571_0 : P.sumLeaves 24 584704 1024 = 29224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 571) (lo := 0) (len := 1024) (W := 29224) check rows elimOK (by decide) (by decide) cover571 (by decide)
  decide +kernel

theorem h571 : P.leaf 34 571 = 29224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 29224)]) (.cons c571_0 (.nil)) (by decide) (by decide))

theorem cover572 : P.CoversSplit 24 10 572 0xc4000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 529, 572, 859, 866, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (14, [880], [859, 915, 1266])]) (by decide +kernel)

theorem c572_0 : P.sumLeaves 24 585728 1024 = 5456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 572) (lo := 0) (len := 1024) (W := 5456) check rows elimOK (by decide) (by decide) cover572 (by decide)
  decide +kernel

theorem h572 : P.leaf 34 572 = 5456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5456)]) (.cons c572_0 (.nil)) (by decide) (by decide))

theorem cover573 : P.CoversSplit 24 10 573 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 529, 572, 860, 866, 871, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [572]), (14, [958], [915, 1266])]) (by decide +kernel)

theorem c573_0 : P.sumLeaves 24 586752 1024 = 70528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 573) (lo := 0) (len := 1024) (W := 70528) check rows elimOK (by decide) (by decide) cover573 (by decide)
  decide +kernel

theorem h573 : P.leaf 34 573 = 70528 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 70528)]) (.cons c573_0 (.nil)) (by decide) (by decide))

theorem cover574 : P.CoversSplit 24 10 574 0xc4000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 529, 572, 859, 866, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (14, [880], [859, 915, 1266])]) (by decide +kernel)

theorem c574_0 : P.sumLeaves 24 587776 1024 = 87312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 574) (lo := 0) (len := 1024) (W := 87312) check rows elimOK (by decide) (by decide) cover574 (by decide)
  decide +kernel

theorem h574 : P.leaf 34 574 = 87312 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 87312)]) (.cons c574_0 (.nil)) (by decide) (by decide))

theorem cover575 : P.CoversSplit 24 10 575 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 529, 572, 860, 866, 871, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [572]), (14, [958], [915, 1266])]) (by decide +kernel)

theorem c575_0 : P.sumLeaves 24 588800 1024 = 252056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 575) (lo := 0) (len := 1024) (W := 252056) check rows elimOK (by decide) (by decide) cover575 (by decide)
  decide +kernel

theorem h575 : P.leaf 34 575 = 252056 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 252056)]) (.cons c575_0 (.nil)) (by decide) (by decide))

theorem cover620 : P.CoversSplit 24 10 620 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000001100110000000000000000000000000011001080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011001100000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 522, 572, 859, 872, 1209, 1217]) (ps := [(4, [558], [515]), (14, [874], [1266])]) (by decide +kernel)

theorem c620_0 : P.sumLeaves 24 634880 1024 = 13211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 620) (lo := 0) (len := 1024) (W := 13211) check rows elimOK (by decide) (by decide) cover620 (by decide)
  decide +kernel

theorem h620 : P.leaf 34 620 = 13211 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13211)]) (.cons c620_0 (.nil)) (by decide) (by decide))

theorem cover621 : P.CoversSplit 24 10 621 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000022002200000000000000000000000000220022cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000022002200000000000000000000000000220022 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 859, 872, 915, 1209]) (ps := [(18, [475], [1210])]) (by decide +kernel)

theorem c621_0 : P.sumLeaves 24 635904 320 = 5735 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 621) (lo := 0) (len := 320) (W := 5735) check rows elimOK (by decide) (by decide) cover621 (by decide)
  decide +kernel

theorem contract621_1 : P.leaf 30 9941 = 512 := by
  exact leaf_contract_factors (k := 30) (b := 9) (H := 9941) (ss := [(27, 1, 473), (29, 1, 473), (19, 1, 474), (18, 1, 475), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (7, 1, 579), (9, 1, 587), (12, 1, 866), (11, 1, 817), (31, 1, 872), (13, 1, 922), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (14, 0, 1266), (8, 1, 874), (17, 1, 1273), (20, 1, 1657)]) (ids := [4, 8, 19, 20, 21, 22, 23, 24, 26]) (cs := [1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 4, 5, 6, 7, 8, 9, 1, 10, 1, 1, 1]) (bs := [0, 9]) (W := 512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c621_1 : P.sumLeaves 24 636224 64 = 512 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9941) rows (by decide) (by decide)).symm.trans contract621_1

theorem c621_2 : P.sumLeaves 24 636288 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 621) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover621 (by decide)
  decide +kernel

theorem contract621_3 : P.leaf 30 9943 = 896 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 9943) (ss := [(27, 1, 473), (29, 1, 473), (19, 1, 474), (18, 1, 475), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (7, 1, 579), (9, 1, 587), (12, 1, 866), (11, 1, 817), (31, 1, 872), (13, 1, 922), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [6, 8, 26, 4, 19, 20, 21, 22, 23, 24]) (cs := [1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 9, 10, 11, 1, 4, 1, 1, 1]) (bs := [3, 7]) (W := 896) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c621_3 : P.sumLeaves 24 636352 64 = 896 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9943) rows (by decide) (by decide)).symm.trans contract621_3

theorem c621_4 : P.sumLeaves 24 636416 320 = 5186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 621) (lo := 512) (len := 320) (W := 5186) check rows elimOK (by decide) (by decide) cover621 (by decide)
  decide +kernel

theorem contract621_5 : P.leaf 30 9949 = 19456 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 9949) (ss := [(27, 1, 473), (29, 1, 473), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (12, 1, 866), (11, 1, 817), (31, 1, 872), (30, 1, 1209), (17, 1, 1266), (16, 1, 1272), (18, 1, 1265), (19, 1, 1273)]) (ids := [4, 5, 6, 7, 8, 11, 12, 13, 18, 19, 21, 22, 23, 24, 26, 20]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 7, 8, 9, 1, 1, 1, 1, 10, 11, 17, 12, 13, 14, 15, 1, 16, 1, 1, 1]) (bs := [15, 1]) (W := 19456) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c621_5 : P.sumLeaves 24 636736 64 = 19456 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9949) rows (by decide) (by decide)).symm.trans contract621_5

theorem c621_6 : P.sumLeaves 24 636800 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 621) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover621 (by decide)
  decide +kernel

theorem contract621_7 : P.leaf 30 9951 = 78336 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 9951) (ss := [(27, 1, 473), (29, 1, 473), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (12, 1, 866), (11, 1, 817), (31, 1, 872), (30, 1, 1209)]) (ids := [4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 24, 26, 20, 23]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 16, 17, 21, 18, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 78336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c621_7 : P.sumLeaves 24 636864 64 = 78336 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9951) rows (by decide) (by decide)).symm.trans contract621_7

theorem h621 : P.leaf 34 621 = 110121 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 5735), (64, 512), (64, 0), (64, 896), (320, 5186), (64, 19456), (64, 0), (64, 78336)]) (.cons c621_0 (.cons c621_1 (.cons c621_2 (.cons c621_3 (.cons c621_4 (.cons c621_5 (.cons c621_6 (.cons c621_7 (.nil))))))))) (by decide) (by decide))

theorem cover622 : P.CoversSplit 24 10 622 0x8000000000000400000000000000000080000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 859, 872, 915, 1217, 1258]) (ps := [(14, [874], [915, 1266])]) (by decide +kernel)

theorem c622_0 : P.sumLeaves 24 636928 1024 = 86220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 622) (lo := 0) (len := 1024) (W := 86220) check rows elimOK (by decide) (by decide) cover622 (by decide)
  decide +kernel

theorem h622 : P.leaf 34 622 = 86220 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 86220)]) (.cons c622_0 (.nil)) (by decide) (by decide))

theorem cover623 : P.CoversSplit 24 10 623 0xcc0000000000c8000000000000000000cc0000000000c80000320000000000200000000000000000000000000000000000000000000000000000000000000000cc0000000000c8000000000000000000cc0000000000880000320000000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 859, 872, 915, 1209, 1258]) (ps := [(8, [1217], [572]), (14, [1217], [915, 1266]), (18, [524], [1210])]) (by decide +kernel)

theorem c623_0 : P.sumLeaves 24 637952 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 623) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover623 (by decide)
  decide +kernel

theorem contract623_1 : P.leaf 30 9972 = 0 := by
  exact leaf_contract_zero (ss := [(19, 1, 523), (18, 1, 524), (4, 1, 529), (12, 1, 866), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (5, 1, 433), (20, 1, 530), (15, 0, 587), (17, 0, 636)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c623_1 : P.sumLeaves 24 638208 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9972) rows (by decide) (by decide)).symm.trans contract623_1

theorem contract623_2 : P.leaf 30 9973 = 0 := by
  exact leaf_contract_zero (ss := [(19, 1, 523), (18, 1, 524), (4, 1, 529), (27, 1, 572), (7, 1, 579), (9, 1, 587), (12, 1, 866), (29, 1, 915), (13, 1, 922), (15, 1, 930), (16, 1, 1265), (14, 0, 1266), (8, 1, 874)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c623_2 : P.sumLeaves 24 638272 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9973) rows (by decide) (by decide)).symm.trans contract623_2

theorem c623_3 : P.sumLeaves 24 638336 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 623) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover623 (by decide)
  decide +kernel

theorem contract623_4 : P.leaf 30 9975 = 6128 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 9975) (ss := [(19, 1, 523), (18, 1, 524), (4, 1, 529), (27, 1, 572), (7, 1, 579), (9, 1, 587), (12, 1, 866), (29, 1, 915), (13, 1, 922), (14, 1, 923), (8, 1, 580), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 3, 4, 8, 9, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 1, 4, 5, 1, 1, 1, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15, 8, 9, 10, 16, 11, 1, 12, 1, 13, 14]) (bs := [13, 2]) (W := 6128) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c623_4 : P.sumLeaves 24 638400 64 = 6128 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9975) rows (by decide) (by decide)).symm.trans contract623_4

theorem c623_5 : P.sumLeaves 24 638464 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 623) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover623 (by decide)
  decide +kernel

theorem contract623_6 : P.leaf 30 9980 = 504 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 9980) (ss := [(4, 1, 529), (12, 1, 866), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 636), (18, 1, 873), (19, 1, 881)]) (ids := [0, 1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 26, 28, 29]) (cs := [2, 3, 1, 4, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 1, 1, 8, 9, 10, 11, 12, 13, 14, 0, 15, 0, 16, 17]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c623_6 : P.sumLeaves 24 638720 64 = 504 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9980) rows (by decide) (by decide)).symm.trans contract623_6

theorem c623_7 : P.sumLeaves 24 638784 192 = 953512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 623) (lo := 832) (len := 192) (W := 953512) check rows elimOK (by decide) (by decide) cover623 (by decide)
  decide +kernel

theorem h623 : P.leaf 34 623 = 960144 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (64, 0), (64, 6128), (256, 0), (64, 504), (192, 953512)]) (.cons c623_0 (.cons c623_1 (.cons c623_2 (.cons c623_3 (.cons c623_4 (.cons c623_5 (.cons c623_6 (.cons c623_7 (.nil))))))))) (by decide) (by decide))

theorem cover638 : P.CoversSplit 24 10 638 0xc400c400440000000000000000000000c400c4004400000000310031001100000000000000000000000000000000000000000000000000000000000000000000c000c000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 859, 866, 915, 1209, 1217, 1258]) (ps := [(14, [874], [859, 915, 1266])]) (by decide +kernel)

theorem c638_0 : P.sumLeaves 24 653312 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 638) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover638 (by decide)
  decide +kernel

theorem contract638_1 : P.leaf 30 10215 = 5284 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 10215) (ss := [(27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 23, 24, 26, 28, 29, 19]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 18, 10, 11, 12, 13, 14, 1, 15, 1, 16, 17]) (bs := [16, 1]) (W := 5284) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c638_1 : P.sumLeaves 24 653760 64 = 5284 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 10215) rows (by decide) (by decide)).symm.trans contract638_1

theorem c638_2 : P.sumLeaves 24 653824 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 638) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover638 (by decide)
  decide +kernel

theorem contract638_3 : P.leaf 30 10220 = 730 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 10220) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (3, 2, 486), (17, 0, 587), (25, 1, 865), (18, 1, 873), (19, 1, 881)]) (ids := [0, 2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 24, 26, 28, 29]) (cs := [2, 2, 3, 4, 5, 0, 0, 0, 6, 7, 8, 0, 0, 0, 0, 0, 1, 1, 9, 10, 11, 12, 13, 1, 14, 0, 15, 0, 16, 17]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c638_3 : P.sumLeaves 24 654080 64 = 730 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 10220) rows (by decide) (by decide)).symm.trans contract638_3

theorem c638_4 : P.sumLeaves 24 654144 192 = 896386 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 638) (lo := 832) (len := 192) (W := 896386) check rows elimOK (by decide) (by decide) cover638 (by decide)
  decide +kernel

theorem h638 : P.leaf 34 638 = 902400 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 5284), (256, 0), (64, 730), (192, 896386)]) (.cons c638_0 (.cons c638_1 (.cons c638_2 (.cons c638_3 (.cons c638_4 (.nil)))))) (by decide) (by decide))

theorem cover639 : P.CoversSplit 24 10 639 0xcc00cc00c80000000000000000000000cc00cc00c800000000330033003200000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 859, 866, 915, 1209, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

theorem c639_0 : P.sumLeaves 24 654336 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 639) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover639 (by decide)
  decide +kernel

theorem contract639_1 : P.leaf 30 10228 = 0 := by
  exact leaf_contract_zero (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (5, 1, 433), (15, 0, 587), (17, 0, 587), (12, 1, 825), (25, 1, 865), (18, 1, 873)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c639_1 : P.sumLeaves 24 654592 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 10228) rows (by decide) (by decide)).symm.trans contract639_1

theorem contract639_2 : P.leaf 30 10229 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 572), (29, 1, 915), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (12, 1, 825)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c639_2 : P.sumLeaves 24 654656 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 10229) rows (by decide) (by decide)).symm.trans contract639_2

theorem c639_3 : P.sumLeaves 24 654720 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 639) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover639 (by decide)
  decide +kernel

theorem contract639_4 : P.leaf 30 10231 = 22624 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 10231) (ss := [(27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 17, 10, 11, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 22624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c639_4 : P.sumLeaves 24 654784 64 = 22624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 10231) rows (by decide) (by decide)).symm.trans contract639_4

theorem c639_5 : P.sumLeaves 24 654848 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 639) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover639 (by decide)
  decide +kernel

theorem contract639_6 : P.leaf 30 10236 = 3758 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 10236) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (25, 1, 865), (18, 1, 873), (19, 1, 881)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 24, 26, 28, 29]) (cs := [2, 3, 4, 5, 6, 0, 0, 0, 7, 8, 9, 0, 0, 0, 0, 0, 1, 1, 10, 11, 12, 13, 14, 1, 15, 0, 16, 0, 17, 18]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c639_6 : P.sumLeaves 24 655104 64 = 3758 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 10236) rows (by decide) (by decide)).symm.trans contract639_6

theorem c639_7 : P.sumLeaves 24 655168 192 = 3664694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 639) (lo := 832) (len := 192) (W := 3664694) check rows elimOK (by decide) (by decide) cover639 (by decide)
  decide +kernel

theorem h639 : P.leaf 34 639 = 3691076 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (64, 0), (64, 22624), (256, 0), (64, 3758), (192, 3664694)]) (.cons c639_0 (.cons c639_1 (.cons c639_2 (.cons c639_3 (.cons c639_4 (.cons c639_5 (.cons c639_6 (.cons c639_7 (.nil))))))))) (by decide) (by decide))

theorem h676 : P.leaf 34 676 = 0 := by
  exact leaf_contract_zero (ss := [(27, 6, 466), (33, 0, 468), (26, 6, 472), (35, 0, 475), (13, 2, 479), (14, 0, 510), (16, 3, 486), (18, 4, 487), (34, 12, 866), (31, 12, 872), (12, 1, 951), (6, 1, 458), (10, 1, 458), (11, 1, 459), (28, 1, 465), (29, 1, 473), (30, 1, 515), (32, 1, 522)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h677 : P.leaf 34 677 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (12, 5, 510), (33, 0, 566), (31, 5, 468), (5, 1, 811), (10, 1, 852), (34, 1, 867), (27, 1, 473), (29, 1, 473), (32, 1, 522), (28, 1, 871), (8, 0, 874), (21, 0, 482), (20, 1, 433)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h679 : P.leaf 34 679 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (34, 5, 475), (16, 3, 529), (33, 0, 566), (31, 5, 468), (18, 4, 536), (10, 1, 852), (12, 1, 852), (5, 1, 510), (28, 1, 871), (11, 1, 901), (29, 1, 921), (3, 1, 958), (13, 1, 873), (4, 1, 922), (14, 1, 958), (8, 1, 531), (26, 1, 517), (27, 1, 573), (17, 1, 880), (19, 1, 929), (30, 1, 1209), (32, 1, 1258)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover680 : P.CoversSplit 24 10 680 0x8000000000000000000000000000000000000000000000000000000000000000000000001000100000000000100010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 859, 872]) (by decide +kernel)

noncomputable def f680 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (696320 + i)

theorem c680_0 : rowSum f680 0 1024 = 2880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 680) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover680 (by decide)
  decide +kernel

theorem sum680 : rowSum f680 0 1024 = 2880 :=
  c680_0

theorem h680 : P.leaf 34 680 = 2880 :=
  leaf_weighted (k := 24) (d := 10) (H := 680) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 680) (by decide) (by decide +kernel)) sum680

theorem h681 : P.leaf 34 681 = 9024 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 681) (ss := [(18, 11, 475), (35, 14, 487), (14, 1, 524), (16, 1, 529), (15, 1, 558), (11, 1, 559), (33, 1, 566), (10, 1, 852), (12, 1, 852), (34, 1, 867), (27, 1, 473), (29, 1, 473), (32, 1, 522), (28, 1, 871), (31, 1, 860), (30, 1, 1209)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 11, 15, 17, 18, 19, 20, 21, 24, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 10, 1, 1, 1, 11, 1, 12, 13, 14, 15, 16, 18, 19, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [16, 2]) (W := 9024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h683 : P.leaf 34 683 = 40416 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 683) (ss := [(35, 1, 524), (16, 1, 529), (33, 1, 566), (18, 1, 536), (10, 1, 852), (12, 1, 852), (11, 1, 818), (34, 1, 867), (28, 1, 871), (31, 1, 860), (29, 1, 921), (30, 1, 1209), (32, 1, 1258)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 15, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 10, 11, 12, 1, 13, 1, 14, 15, 16, 17, 18, 21, 22, 19, 20, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [19, 2]) (W := 40416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover684 : P.CoversSplit 24 10 684 0x8000000000000000000000000000000000000000000000000000000000000000000000001000100000000000100010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 859, 872]) (by decide +kernel)

noncomputable def f684 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (700416 + i)

theorem c684_0 : rowSum f684 0 1024 = 16912 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 684) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover684 (by decide)
  decide +kernel

theorem sum684 : rowSum f684 0 1024 = 16912 :=
  c684_0

theorem h684 : P.leaf 34 684 = 16912 :=
  leaf_weighted (k := 24) (d := 10) (H := 684) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 684) (by decide) (by decide +kernel)) sum684

theorem h685 : P.leaf 34 685 = 94336 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 685) (ss := [(35, 1, 524), (11, 1, 475), (16, 1, 529), (33, 1, 566), (18, 1, 536), (12, 1, 866), (34, 1, 867), (27, 1, 473), (29, 1, 473), (32, 1, 522), (28, 1, 871), (31, 1, 860), (30, 1, 1209)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 15, 17, 18, 19, 20, 21, 24, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 11, 12, 13, 1, 14, 1, 15, 16, 17, 18, 19, 21, 22, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [19, 2]) (W := 94336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover687 : P.CoversSplit 24 10 687 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 860, 871, 879, 916, 921, 1209, 1258]) (by decide +kernel)

noncomputable def f687 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (703488 + i)

theorem c687_0 : rowSum f687 0 1024 = 395888 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 687) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover687 (by decide)
  decide +kernel

theorem sum687 : rowSum f687 0 1024 = 395888 :=
  c687_0

theorem h687 : P.leaf 34 687 = 395888 :=
  leaf_weighted (k := 24) (d := 10) (H := 687) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 687) (by decide) (by decide +kernel)) sum687

theorem cover695 : P.CoversSplit 24 10 695 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 859, 860, 867, 871, 916, 921, 1209, 1251, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

noncomputable def f695 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (711680 + i)

theorem c695_0 : rowSum f695 0 1024 = 51440 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 695) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover695 (by decide)
  decide +kernel

theorem sum695 : rowSum f695 0 1024 = 51440 :=
  c695_0

theorem h695 : P.leaf 34 695 = 51440 :=
  leaf_weighted (k := 24) (d := 10) (H := 695) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 695) (by decide) (by decide +kernel)) sum695

theorem h696 : P.leaf 34 696 = 7184 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 696) (ss := [(16, 10, 468), (18, 11, 475), (33, 14, 486), (35, 14, 487), (15, 1, 509), (34, 1, 866), (12, 1, 867), (6, 1, 458), (10, 1, 458), (11, 1, 459), (31, 1, 872), (28, 1, 860), (14, 1, 880), (29, 1, 915), (30, 1, 1209), (32, 1, 1259)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 15, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 1, 1, 1, 10, 1, 11, 12, 13, 14, 15, 18, 19, 16, 17, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [16, 2]) (W := 7184) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover697 : P.CoversSplit 24 10 697 0xf0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 871, 879, 915, 1209, 1251, 1259, 1264, 1308]) (ps := [(8, [580], [573]), (14, [487, 923], [487, 915])]) (by decide +kernel)

theorem c697_0 : P.sumLeaves 24 713728 960 = 2176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 697) (lo := 0) (len := 960) (W := 2176) check rows elimOK (by decide) (by decide) cover697 (by decide)
  decide +kernel

theorem contract697_1 : P.leaf 30 11167 = 38656 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 11167) (ss := [(18, 11, 475), (14, 1, 487), (15, 1, 558), (11, 1, 559), (12, 1, 817), (10, 1, 811), (28, 1, 871), (31, 1, 860), (29, 1, 915), (30, 1, 1209)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 11, 14, 15, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 10, 1, 1, 11, 12, 1, 13, 14, 15, 16, 17, 20, 21, 18, 19, 1, 1, 1, 1]) (bs := [18, 2]) (W := 38656) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c697_1 : P.sumLeaves 24 714688 64 = 38656 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 11167) rows (by decide) (by decide)).symm.trans contract697_1

theorem h697 : P.leaf 34 697 = 40832 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 2176), (64, 38656)]) (.cons c697_0 (.cons c697_1 (.nil))) (by decide) (by decide))

theorem cover699 : P.CoversSplit 24 10 699 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 871, 879, 921, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f699 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (715776 + i)

theorem c699_0 : rowSum f699 0 1024 = 87104 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 699) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover699 (by decide)
  decide +kernel

theorem sum699 : rowSum f699 0 1024 = 87104 :=
  c699_0

theorem h699 : P.leaf 34 699 = 87104 :=
  leaf_weighted (k := 24) (d := 10) (H := 699) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 699) (by decide) (by decide +kernel)) sum699

theorem cover700 : P.CoversSplit 24 10 700 0xf4210000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 566, 573, 859, 866, 872, 915, 1209, 1251, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573]), (14, [874, 880], [859, 915])]) (by decide +kernel)

noncomputable def f700 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (716800 + i)

theorem c700_0 : rowSum f700 0 1024 = 49152 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 700) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover700 (by decide)
  decide +kernel

theorem sum700 : rowSum f700 0 1024 = 49152 :=
  c700_0

theorem h700 : P.leaf 34 700 = 49152 :=
  leaf_weighted (k := 24) (d := 10) (H := 700) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 700) (by decide) (by decide +kernel)) sum700

theorem cover701 : P.CoversSplit 24 10 701 0xf0300000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 867, 871, 915, 1209, 1251, 1259, 1264, 1308]) (ps := [(8, [580], [573]), (14, [874], [915])]) (by decide +kernel)

theorem c701_0 : P.sumLeaves 24 717824 1024 = 286976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 701) (lo := 0) (len := 1024) (W := 286976) check rows elimOK (by decide) (by decide) cover701 (by decide)
  decide +kernel

theorem h701 : P.leaf 34 701 = 286976 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 286976)]) (.cons c701_0 (.nil)) (by decide) (by decide))

theorem cover703 : P.CoversSplit 24 10 703 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 867, 871, 916, 921, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

noncomputable def f703 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (719872 + i)

theorem c703_0 : rowSum f703 0 1024 = 922928 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 703) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover703 (by decide)
  decide +kernel

theorem sum703 : rowSum f703 0 1024 = 922928 :=
  c703_0

theorem h703 : P.leaf 34 703 = 922928 :=
  leaf_weighted (k := 24) (d := 10) (H := 703) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 703) (by decide) (by decide +kernel)) sum703

theorem cover716 : P.CoversSplit 24 10 716 0x8000000000000000000000000000000000000000000000000000000000000000000000001111101000000000110010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 859, 872, 1301]) (ps := [(14, [874], [1266])]) (by decide +kernel)

noncomputable def f716 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (733184 + i)

theorem c716_0 : rowSum f716 0 1024 = 53236 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 716) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover716 (by decide)
  decide +kernel

theorem sum716 : rowSum f716 0 1024 = 53236 :=
  c716_0

theorem h716 : P.leaf 34 716 = 53236 :=
  leaf_weighted (k := 24) (d := 10) (H := 716) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 716) (by decide) (by decide +kernel)) sum716

theorem cover717 : P.CoversSplit 24 10 717 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 536, 573, 859, 860, 871, 879, 1209]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c717_0 : P.sumLeaves 24 734208 1024 = 74368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 717) (lo := 0) (len := 1024) (W := 74368) check rows elimOK (by decide) (by decide) cover717 (by decide)
  decide +kernel

theorem h717 : P.leaf 34 717 = 74368 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 74368)]) (.cons c717_0 (.nil)) (by decide) (by decide))

theorem cover719 : P.CoversSplit 24 10 719 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 860, 871, 879, 916, 921, 1209, 1258]) (ps := [(14, [958], [1266])]) (by decide +kernel)

noncomputable def f719 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (736256 + i)

theorem c719_0 : rowSum f719 0 1024 = 447288 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 719) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover719 (by decide)
  decide +kernel

theorem sum719 : rowSum f719 0 1024 = 447288 :=
  c719_0

theorem h719 : P.leaf 34 719 = 447288 :=
  leaf_weighted (k := 24) (d := 10) (H := 719) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 719) (by decide) (by decide +kernel)) sum719

theorem cover732 : P.CoversSplit 24 10 732 0xf4210000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 859, 866, 872, 915, 1210, 1251, 1259, 1264]) (ps := [(14, [874, 880], [859, 915, 1266])]) (by decide +kernel)

noncomputable def f732 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (749568 + i)

theorem c732_0 : rowSum f732 0 1024 = 62140 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 732) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover732 (by decide)
  decide +kernel

theorem sum732 : rowSum f732 0 1024 = 62140 :=
  c732_0

theorem h732 : P.leaf 34 732 = 62140 :=
  leaf_weighted (k := 24) (d := 10) (H := 732) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 732) (by decide) (by decide +kernel)) sum732

theorem cover733 : P.CoversSplit 24 10 733 0xf0300000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 860, 867, 871, 915, 1210, 1251, 1259, 1264]) (ps := [(14, [880, 929], [915, 1266])]) (by decide +kernel)

theorem c733_0 : P.sumLeaves 24 750592 1024 = 313392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 733) (lo := 0) (len := 1024) (W := 313392) check rows elimOK (by decide) (by decide) cover733 (by decide)
  decide +kernel

theorem h733 : P.leaf 34 733 = 313392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 313392)]) (.cons c733_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(571, 24), (572, 48), (573, 48), (574, 48), (575, 48), (620, 12), (621, 12), (622, 24), (623, 24), (638, 12), (639, 12), (676, 8), (677, 24), (679, 24), (680, 24), (681, 48), (683, 24), (684, 24), (685, 48), (687, 24), (695, 8), (696, 24), (697, 48), (699, 24), (700, 24), (701, 48), (703, 24), (716, 24), (717, 48), (719, 24), (732, 24), (733, 48)]

theorem segOK : checkSeg 16 perms 571 735 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 571 735 928 192115840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 192115840)
    (SegSum.cons (w := 24) h571 (SegSum.cons (w := 48) h572 (SegSum.cons (w := 48) h573 (SegSum.cons (w := 48) h574 (SegSum.cons (w := 48) h575 (SegSum.cons (w := 12) h620 (SegSum.cons (w := 12) h621 (SegSum.cons (w := 24) h622 (SegSum.cons (w := 24) h623 (SegSum.cons (w := 12) h638 (SegSum.cons (w := 12) h639 (SegSum.cons (w := 8) h676 (SegSum.cons (w := 24) h677 (SegSum.cons (w := 24) h679 (SegSum.cons (w := 24) h680 (SegSum.cons (w := 48) h681 (SegSum.cons (w := 24) h683 (SegSum.cons (w := 24) h684 (SegSum.cons (w := 48) h685 (SegSum.cons (w := 24) h687 (SegSum.cons (w := 8) h695 (SegSum.cons (w := 24) h696 (SegSum.cons (w := 48) h697 (SegSum.cons (w := 24) h699 (SegSum.cons (w := 24) h700 (SegSum.cons (w := 48) h701 (SegSum.cons (w := 24) h703 (SegSum.cons (w := 24) h716 (SegSum.cons (w := 48) h717 (SegSum.cons (w := 24) h719 (SegSum.cons (w := 24) h732 (SegSum.cons (w := 48) h733 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S3
