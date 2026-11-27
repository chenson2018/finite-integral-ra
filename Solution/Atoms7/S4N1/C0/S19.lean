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

namespace RACert.S4N1.C0.S19

open RACert RACert.Problem

theorem cover3276 : P.CoversSplit 24 10 3276 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3276_0 : P.sumLeaves 24 3354624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3276) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3276 (by decide)
  decide +kernel

theorem h3276 : P.leaf 34 3276 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3276_0 (.nil)) (by decide) (by decide))

theorem h3277 : P.leaf 34 3277 = 12544 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 3277) (ss := [(30, 1, 466), (11, 1, 472), (18, 1, 524), (35, 33, 536), (32, 17, 565), (33, 1, 1272), (17, 1, 523), (27, 1, 473), (6, 1, 459), (29, 1, 473), (26, 1, 515), (10, 1, 809), (12, 1, 817), (28, 1, 858), (34, 1, 915), (31, 1, 1209)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 10, 11, 12, 1, 1, 13, 14, 15, 16, 17, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [15, 3]) (W := 12544) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h3278 : P.leaf 34 3278 = 90624 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 3278) (ss := [(32, 1, 466), (3, 1, 472), (30, 18, 524), (35, 1, 536), (18, 1, 566), (4, 1, 417), (11, 1, 879), (10, 1, 809), (29, 1, 916), (28, 1, 858), (26, 1, 515), (27, 1, 522), (34, 1, 916), (31, 1, 1209)]) (ids := [0, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 17, 18, 19, 23, 31, 20, 21, 22]) (cs := [2, 1, 1, 3, 4, 5, 6, 7, 1, 1, 8, 9, 10, 11, 12, 13, 1, 14, 15, 16, 19, 20, 21, 17, 1, 1, 1, 1, 1, 1, 1, 18, 1, 1]) (bs := [17, 3]) (W := 90624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover3279 : P.CoversSplit 24 10 3279 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem c3279_0 : P.sumLeaves 24 3357696 1024 = 402592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3279) (lo := 0) (len := 1024) (W := 402592) check rows elimOK (by decide) (by decide) cover3279 (by decide)
  decide +kernel

theorem h3279 : P.leaf 34 3279 = 402592 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 402592)]) (.cons c3279_0 (.nil)) (by decide) (by decide))

theorem cover3290 : P.CoversSplit 24 10 3290 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 487, 516, 573, 858, 865, 867, 909, 916, 921, 1210, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c3290_0 : P.sumLeaves 24 3368960 1024 = 116064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3290) (lo := 0) (len := 1024) (W := 116064) check rows elimOK (by decide) (by decide) cover3290 (by decide)
  decide +kernel

theorem h3290 : P.leaf 34 3290 = 116064 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 116064)]) (.cons c3290_0 (.nil)) (by decide) (by decide))

theorem cover3291 : P.CoversSplit 24 10 3291 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [487, 516, 573, 858, 865, 867, 909, 916, 921, 1202, 1210, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c3291_0 : P.sumLeaves 24 3369984 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3291) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3291 (by decide)
  decide +kernel

theorem contract3291_1 : P.leaf 30 52663 = 7872 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 52663) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (30, 1, 867), (11, 1, 879), (12, 1, 818), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (31, 1, 1210), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 7, 8, 20, 26, 4, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 11, 6, 1, 7, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 12, 13, 14, 15, 1, 10, 1, 1, 1]) (bs := [9, 5]) (W := 7872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3291_1 : P.sumLeaves 24 3370432 64 = 7872 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52663) rows (by decide) (by decide)).symm.trans contract3291_1

theorem c3291_2 : P.sumLeaves 24 3370496 512 = 1106560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3291) (lo := 512) (len := 512) (W := 1106560) check rows elimOK (by decide) (by decide) cover3291 (by decide)
  decide +kernel

theorem h3291 : P.leaf 34 3291 = 1114432 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 7872), (512, 1106560)]) (.cons c3291_0 (.cons c3291_1 (.cons c3291_2 (.nil)))) (by decide) (by decide))

theorem cover3292 : P.CoversSplit 24 10 3292 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 858, 865, 915, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c3292_0 : P.sumLeaves 24 3371008 1024 = 57424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3292) (lo := 0) (len := 1024) (W := 57424) check rows elimOK (by decide) (by decide) cover3292 (by decide)
  decide +kernel

theorem h3292 : P.leaf 34 3292 = 57424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 57424)]) (.cons c3292_0 (.nil)) (by decide) (by decide))

theorem cover3293 : P.CoversSplit 24 10 3293 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 865, 915, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c3293_0 : P.sumLeaves 24 3372032 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3293) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3293 (by decide)
  decide +kernel

theorem contract3293_1 : P.leaf 30 52695 = 3520 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 52695) (ss := [(27, 1, 473), (29, 1, 473), (18, 11, 475), (11, 1, 487), (6, 1, 459), (8, 1, 580), (10, 1, 809), (12, 1, 817), (13, 1, 922), (14, 1, 929), (30, 1, 1251), (31, 1, 1210), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 20, 26, 5, 13, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 1, 9, 1, 6, 1, 1, 1, 1, 1, 10, 1, 1, 1, 1, 1, 1, 7, 11, 12, 13, 14, 1, 8, 1, 1, 1]) (bs := [7, 6]) (W := 3520) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3293_1 : P.sumLeaves 24 3372480 64 = 3520 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52695) rows (by decide) (by decide)).symm.trans contract3293_1

theorem c3293_2 : P.sumLeaves 24 3372544 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3293) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover3293 (by decide)
  decide +kernel

theorem contract3293_3 : P.leaf 30 52701 = 49248 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 52701) (ss := [(27, 1, 473), (29, 1, 473), (11, 1, 475), (6, 1, 459), (31, 1, 536), (10, 1, 809), (12, 1, 817), (30, 1, 1210), (17, 1, 1266), (19, 1, 1273), (16, 1, 1308), (18, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 12, 13, 18, 19, 20, 22, 23, 24, 26, 21]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 10, 11, 1, 1, 1, 1, 12, 13, 14, 19, 15, 16, 17, 1, 18, 1, 1, 1]) (bs := [17, 1]) (W := 49248) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3293_3 : P.sumLeaves 24 3372864 64 = 49248 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52701) rows (by decide) (by decide)).symm.trans contract3293_3

theorem c3293_4 : P.sumLeaves 24 3372928 128 = 237056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3293) (lo := 896) (len := 128) (W := 237056) check rows elimOK (by decide) (by decide) cover3293 (by decide)
  decide +kernel

theorem h3293 : P.leaf 34 3293 = 289824 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 3520), (320, 0), (64, 49248), (128, 237056)]) (.cons c3293_0 (.cons c3293_1 (.cons c3293_2 (.cons c3293_3 (.cons c3293_4 (.nil)))))) (by decide) (by decide))

theorem cover3294 : P.CoversSplit 24 10 3294 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 916, 921, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c3294_0 : P.sumLeaves 24 3373056 1024 = 754352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3294) (lo := 0) (len := 1024) (W := 754352) check rows elimOK (by decide) (by decide) cover3294 (by decide)
  decide +kernel

theorem h3294 : P.leaf 34 3294 = 754352 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 754352)]) (.cons c3294_0 (.nil)) (by decide) (by decide))

theorem cover3295 : P.CoversSplit 24 10 3295 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 865, 916, 921, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c3295_0 : P.sumLeaves 24 3374080 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3295) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3295 (by decide)
  decide +kernel

theorem contract3295_1 : P.leaf 30 52727 = 25776 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 52727) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (11, 1, 879), (29, 1, 916), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (31, 1, 1210), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 10, 13, 20, 21, 24, 26, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 10, 1, 1, 11, 1, 1, 1, 1, 1, 1, 12, 13, 16, 17, 14, 1, 15, 1, 1, 1]) (bs := [14, 2]) (W := 25776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3295_1 : P.sumLeaves 24 3374528 64 = 25776 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52727) rows (by decide) (by decide)).symm.trans contract3295_1

theorem c3295_2 : P.sumLeaves 24 3374592 512 = 3508432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3295) (lo := 512) (len := 512) (W := 3508432) check rows elimOK (by decide) (by decide) cover3295 (by decide)
  decide +kernel

theorem h3295 : P.leaf 34 3295 = 3534208 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 25776), (512, 3508432)]) (.cons c3295_0 (.cons c3295_1 (.cons c3295_2 (.nil)))) (by decide) (by decide))

theorem cover3308 : P.CoversSplit 24 10 3308 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3308_0 : P.sumLeaves 24 3387392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3308) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3308 (by decide)
  decide +kernel

theorem h3308 : P.leaf 34 3308 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3308_0 (.nil)) (by decide) (by decide))

theorem cover3309 : P.CoversSplit 24 10 3309 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 915, 1209, 1217, 1272, 1651]) (by decide +kernel)

theorem c3309_0 : P.sumLeaves 24 3388416 1024 = 54048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3309) (lo := 0) (len := 1024) (W := 54048) check rows elimOK (by decide) (by decide) cover3309 (by decide)
  decide +kernel

theorem h3309 : P.leaf 34 3309 = 54048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 54048)]) (.cons c3309_0 (.nil)) (by decide) (by decide))

theorem cover3310 : P.CoversSplit 24 10 3310 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 916, 1209, 1272]) (by decide +kernel)

theorem c3310_0 : P.sumLeaves 24 3389440 1024 = 234008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3310) (lo := 0) (len := 1024) (W := 234008) check rows elimOK (by decide) (by decide) cover3310 (by decide)
  decide +kernel

theorem h3310 : P.leaf 34 3310 = 234008 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 234008)]) (.cons c3310_0 (.nil)) (by decide) (by decide))

theorem cover3311 : P.CoversSplit 24 10 3311 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 915, 916, 1209, 1272]) (by decide +kernel)

theorem c3311_0 : P.sumLeaves 24 3390464 1024 = 620640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3311) (lo := 0) (len := 1024) (W := 620640) check rows elimOK (by decide) (by decide) cover3311 (by decide)
  decide +kernel

theorem h3311 : P.leaf 34 3311 = 620640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 620640)]) (.cons c3311_0 (.nil)) (by decide) (by decide))

theorem cover3326 : P.CoversSplit 24 10 3326 0xf0005500f00000000000000000000000f0005500f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0004400c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 916, 921, 1209, 1259, 1308]) (by decide +kernel)

theorem c3326_0 : P.sumLeaves 24 3405824 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3326) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3326 (by decide)
  decide +kernel

theorem contract3326_1 : P.leaf 30 53223 = 46816 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 53223) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (19, 1, 866), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 5, 13, 15, 23]) (cs := [2, 3, 4, 5, 6, 18, 1, 7, 8, 9, 10, 1, 1, 19, 1, 20, 1, 1, 1, 1, 11, 12, 13, 21, 14, 1, 15, 1, 16, 17]) (bs := [16, 4]) (W := 46816) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3326_1 : P.sumLeaves 24 3406272 64 = 46816 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 53223) rows (by decide) (by decide)).symm.trans contract3326_1

theorem c3326_2 : P.sumLeaves 24 3406336 512 = 3538700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3326) (lo := 512) (len := 512) (W := 3538700) check rows elimOK (by decide) (by decide) cover3326 (by decide)
  decide +kernel

theorem h3326 : P.leaf 34 3326 = 3585516 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 46816), (512, 3538700)]) (.cons c3326_0 (.cons c3326_1 (.cons c3326_2 (.nil)))) (by decide) (by decide))

theorem cover3327 : P.CoversSplit 24 10 3327 0xff00fa00ff0000000000000000000000ff00fa00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00c800cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 865, 916, 921, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c3327_0 : P.sumLeaves 24 3406848 1024 = 14087490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3327) (lo := 0) (len := 1024) (W := 14087490) check rows elimOK (by decide) (by decide) cover3327 (by decide)
  decide +kernel

theorem h3327 : P.leaf 34 3327 = 14087490 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14087490)]) (.cons c3327_0 (.nil)) (by decide) (by decide))

theorem cover3456 : P.CoversSplit 24 10 3456 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3456_0 : P.sumLeaves 24 3538944 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3456) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3456 (by decide)
  decide +kernel

theorem h3456 : P.leaf 34 3456 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3456_0 (.nil)) (by decide) (by decide))

theorem cover3457 : P.CoversSplit 24 10 3457 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002200000011000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 565, 858, 865, 915, 1209, 1217, 1609]) (by decide +kernel)

theorem c3457_0 : P.sumLeaves 24 3539968 512 = 480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3457) (lo := 0) (len := 512) (W := 480) check rows elimOK (by decide) (by decide) cover3457 (by decide)
  decide +kernel

theorem contract3457_1 : P.leaf 30 55320 = 3693 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 55320) (ss := [(30, 1, 466), (11, 1, 472), (29, 2, 474), (2, 0, 522), (3, 0, 411), (13, 0, 480), (14, 0, 480), (16, 0, 481), (15, 0, 487), (17, 0, 489), (27, 0, 865), (25, 1, 572)]) (ids := [2, 3, 4, 5, 6, 7, 8, 10, 16, 17, 18, 19, 20, 21, 22, 24, 26, 29]) (cs := [0, 0, 2, 3, 4, 5, 6, 7, 8, 1, 9, 0, 0, 0, 0, 0, 10, 11, 12, 13, 14, 15, 16, 1, 17, 0, 18, 0, 1, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3457_1 : P.sumLeaves 24 3540480 64 = 3693 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55320) rows (by decide) (by decide)).symm.trans contract3457_1

theorem c3457_2 : P.sumLeaves 24 3540544 448 = 2368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3457) (lo := 576) (len := 448) (W := 2368) check rows elimOK (by decide) (by decide) cover3457 (by decide)
  decide +kernel

theorem h3457 : P.leaf 34 3457 = 6541 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 480), (64, 3693), (448, 2368)]) (.cons c3457_0 (.cons c3457_1 (.cons c3457_2 (.nil)))) (by decide) (by decide))

theorem cover3459 : P.CoversSplit 24 10 3459 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 565, 858, 865, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f3459 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (3542016 + i)

theorem c3459_0 : rowSum f3459 0 1024 = 35544 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3459) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3459 (by decide)
  decide +kernel

theorem sum3459 : rowSum f3459 0 1024 = 35544 :=
  c3459_0

theorem h3459 : P.leaf 34 3459 = 35544 :=
  leaf_weighted (k := 24) (d := 10) (H := 3459) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3459) (by decide) (by decide +kernel)) sum3459

theorem cover3460 : P.CoversSplit 24 10 3460 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3460_0 : P.sumLeaves 24 3543040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3460) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3460 (by decide)
  decide +kernel

theorem h3460 : P.leaf 34 3460 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3460_0 (.nil)) (by decide) (by decide))

theorem h3461 : P.leaf 34 3461 = 9408 := by
  apply (leaf_contract (k := 34) (b := 19) (H := 3461) (ss := [(30, 1, 466), (11, 1, 472), (3, 1, 502), (4, 1, 417), (5, 1, 502), (32, 1, 523), (27, 1, 473), (6, 1, 459), (29, 1, 473), (26, 1, 515), (10, 1, 809), (12, 1, 817), (28, 1, 858), (34, 1, 915), (31, 1, 1209)]) (ids := [0, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 31, 33]) (cs := [2, 1, 1, 1, 1, 3, 4, 5, 1, 1, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1, 1, 1, 1, 1, 1, 1, 19, 1, 20]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem cover3463 : P.CoversSplit 24 10 3463 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 565, 858, 865, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f3463 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (3546112 + i)

theorem c3463_0 : rowSum f3463 0 1024 = 88528 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3463) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover3463 (by decide)
  decide +kernel

theorem sum3463 : rowSum f3463 0 1024 = 88528 :=
  c3463_0

theorem h3463 : P.leaf 34 3463 = 88528 :=
  leaf_weighted (k := 24) (d := 10) (H := 3463) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 3463) (by decide) (by decide +kernel)) sum3463

theorem cover3468 : P.CoversSplit 24 10 3468 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3468_0 : P.sumLeaves 24 3551232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3468) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3468 (by decide)
  decide +kernel

theorem h3468 : P.leaf 34 3468 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3468_0 (.nil)) (by decide) (by decide))

theorem cover3469 : P.CoversSplit 24 10 3469 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002200000011000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 565, 858, 865, 915, 1209, 1217, 1609]) (by decide +kernel)

theorem c3469_0 : P.sumLeaves 24 3552256 512 = 10512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3469) (lo := 0) (len := 512) (W := 10512) check rows elimOK (by decide) (by decide) cover3469 (by decide)
  decide +kernel

theorem contract3469_1 : P.leaf 30 55512 = 5928 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 55512) (ss := [(30, 1, 466), (11, 1, 472), (29, 0, 522), (2, 1, 410), (27, 0, 473), (3, 0, 523), (16, 0, 529), (13, 1, 530), (14, 1, 531), (17, 0, 536), (15, 1, 538), (25, 1, 572)]) (ids := [2, 3, 4, 5, 6, 7, 8, 10, 16, 17, 18, 19, 20, 21, 22, 24, 26, 29]) (cs := [1, 0, 2, 3, 4, 5, 6, 7, 8, 1, 9, 1, 1, 1, 0, 0, 10, 11, 12, 13, 14, 15, 16, 1, 17, 0, 18, 0, 1, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3469_1 : P.sumLeaves 24 3552768 64 = 5928 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55512) rows (by decide) (by decide)).symm.trans contract3469_1

theorem c3469_2 : P.sumLeaves 24 3552832 448 = 68608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3469) (lo := 576) (len := 448) (W := 68608) check rows elimOK (by decide) (by decide) cover3469 (by decide)
  decide +kernel

theorem h3469 : P.leaf 34 3469 = 85048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 10512), (64, 5928), (448, 68608)]) (.cons c3469_0 (.cons c3469_1 (.cons c3469_2 (.nil)))) (by decide) (by decide))

theorem cover3471 : P.CoversSplit 24 10 3471 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 565, 858, 865, 1209, 1217, 1258]) (by decide +kernel)

noncomputable def f3471 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (3554304 + i)

theorem c3471_0 : rowSum f3471 0 1024 = 750364 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3471) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3471 (by decide)
  decide +kernel

theorem sum3471 : rowSum f3471 0 1024 = 750364 :=
  c3471_0

theorem h3471 : P.leaf 34 3471 = 750364 :=
  leaf_weighted (k := 24) (d := 10) (H := 3471) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3471) (by decide) (by decide +kernel)) sum3471

theorem cover3474 : P.CoversSplit 24 10 3474 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000a000000000000000a0a0000000000000a000000000000000a0a0555500005555a0a0555500005555a0a0555500005050a0a0555500005050a0a0555000005500a000550000005500a000550000005000a000550000005000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 866, 1217, 1258, 1609]) (ps := [(8, [1609], [509, 1266])]) (by decide +kernel)

theorem contract3474_0 : P.leaf 30 55584 = 1024 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 55584) (ss := [(2, 1, 466), (26, 6, 479), (5, 3, 523), (3, 1, 529), (10, 1, 865), (29, 1, 865), (30, 19, 866), (19, 18, 867), (18, 11, 872), (12, 1, 915), (8, 0, 1266), (7, 6, 467), (9, 6, 468), (14, 1, 1609)]) (ids := [2, 4, 9, 11, 13, 14, 15, 18, 19, 20, 21, 22, 23, 25, 26, 29]) (cs := [1, 1, 2, 1, 3, 3, 0, 3, 1, 4, 1, 5, 1, 6, 7, 8, 4, 4, 9, 10, 11, 12, 13, 14, 3, 15, 16, 1, 4, 17]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3474_0 : P.sumLeaves 24 3557376 64 = 1024 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55584) rows (by decide) (by decide)).symm.trans contract3474_0

theorem contract3474_1 : P.leaf 30 55585 = 1772 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 55585) (ss := [(26, 6, 479), (2, 1, 480), (3, 1, 523), (30, 19, 866), (19, 18, 867), (18, 11, 872), (8, 0, 1266), (7, 6, 467), (9, 6, 468), (14, 1, 1609), (5, 1, 580), (29, 1, 1609)]) (ids := [2, 4, 8, 9, 10, 11, 13, 14, 15, 18, 19, 20, 21, 22, 23, 25, 26, 29]) (cs := [1, 1, 2, 1, 3, 3, 0, 3, 4, 5, 6, 7, 1, 8, 9, 10, 5, 5, 11, 12, 13, 14, 15, 16, 3, 17, 18, 1, 5, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3474_1 : P.sumLeaves 24 3557440 64 = 1772 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55585) rows (by decide) (by decide)).symm.trans contract3474_1

theorem c3474_2 : P.sumLeaves 24 3557504 445 = 120122 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3474) (lo := 128) (len := 445) (W := 120122) check rows elimOK (by decide) (by decide) cover3474 (by decide)
  decide +kernel

theorem c3474_3 : P.sumLeaves 24 3557949 3 = 864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3474) (lo := 573) (len := 3) (W := 864) check rows elimOK (by decide) (by decide) cover3474 (by decide)
  decide +kernel

theorem contract3474_4 : P.leaf 30 55593 = 2016 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 55593) (ss := [(26, 6, 479), (2, 1, 480), (3, 1, 523), (8, 1, 531), (6, 1, 467), (10, 1, 458), (28, 1, 465), (16, 1, 531), (7, 1, 530), (17, 1, 537), (9, 1, 538), (11, 1, 809), (12, 1, 460), (30, 1, 858), (31, 1, 516), (18, 1, 1265), (19, 1, 1273)]) (ids := [2, 3, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6, 1, 1, 1, 1, 7, 8, 9, 13, 14, 10, 1, 11, 1, 12, 1, 1]) (bs := [11, 2]) (W := 2016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3474_4 : P.sumLeaves 24 3557952 64 = 2016 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55593) rows (by decide) (by decide)).symm.trans contract3474_4

theorem c3474_5 : P.sumLeaves 24 3558016 64 = 5232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3474) (lo := 640) (len := 64) (W := 5232) check rows elimOK (by decide) (by decide) cover3474 (by decide)
  decide +kernel

theorem contract3474_6 : P.leaf 30 55595 = 11760 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 55595) (ss := [(26, 6, 479), (2, 1, 480), (3, 1, 523), (30, 1, 866), (6, 1, 465), (10, 1, 458), (28, 1, 465), (31, 1, 516), (11, 1, 809), (12, 1, 460)]) (ids := [2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 1, 2, 3, 1, 4, 5, 6, 1, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 11760) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3474_6 : P.sumLeaves 24 3558080 64 = 11760 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55595) rows (by decide) (by decide)).symm.trans contract3474_6

theorem contract3474_7 : P.leaf 30 55596 = 2016 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 55596) (ss := [(2, 1, 466), (26, 6, 479), (5, 1, 523), (8, 1, 531), (6, 1, 467), (12, 1, 460), (28, 1, 465), (31, 1, 516), (16, 1, 531), (7, 1, 530), (17, 1, 537), (9, 1, 538), (10, 1, 809), (11, 1, 809), (30, 1, 858), (18, 1, 1265), (19, 1, 1273)]) (ids := [1, 2, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6, 1, 1, 1, 1, 7, 8, 9, 13, 14, 10, 1, 11, 1, 12, 1, 1]) (bs := [11, 2]) (W := 2016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3474_7 : P.sumLeaves 24 3558144 64 = 2016 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55596) rows (by decide) (by decide)).symm.trans contract3474_7

theorem contract3474_8 : P.leaf 30 55597 = 7488 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 55597) (ss := [(26, 6, 479), (8, 1, 531), (6, 1, 467), (16, 1, 531), (7, 1, 530), (17, 1, 537), (9, 1, 538), (10, 1, 809), (11, 1, 809), (12, 1, 460), (28, 1, 858), (30, 1, 858), (31, 1, 516), (18, 1, 1265), (19, 1, 1273)]) (ids := [0, 1, 2, 3, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 1, 1, 1, 1, 9, 10, 11, 15, 16, 12, 1, 13, 1, 14, 1, 1]) (bs := [13, 2]) (W := 7488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3474_8 : P.sumLeaves 24 3558208 64 = 7488 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55597) rows (by decide) (by decide)).symm.trans contract3474_8

theorem contract3474_9 : P.leaf 30 55598 = 14272 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 55598) (ss := [(2, 1, 466), (26, 6, 479), (5, 1, 523), (30, 1, 866), (6, 1, 465), (12, 1, 460), (28, 1, 465), (31, 1, 516), (10, 1, 809), (11, 1, 809)]) (ids := [1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 5, 6, 1, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 14272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3474_9 : P.sumLeaves 24 3558272 64 = 14272 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55598) rows (by decide) (by decide)).symm.trans contract3474_9

theorem c3474_10 : P.sumLeaves 24 3558336 64 = 50880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3474) (lo := 960) (len := 64) (W := 50880) check rows elimOK (by decide) (by decide) cover3474 (by decide)
  decide +kernel

theorem h3474 : P.leaf 34 3474 = 217446 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 1024), (64, 1772), (445, 120122), (3, 864), (64, 2016), (64, 5232), (64, 11760), (64, 2016), (64, 7488), (64, 14272), (64, 50880)]) (.cons c3474_0 (.cons c3474_1 (.cons c3474_2 (.cons c3474_3 (.cons c3474_4 (.cons c3474_5 (.cons c3474_6 (.cons c3474_7 (.cons c3474_8 (.cons c3474_9 (.cons c3474_10 (.nil)))))))))))) (by decide) (by decide))

theorem cover3475 : P.CoversSplit 24 10 3475 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000fff8000055000000ff00000055000000fff8000055000000ff00000055000000fffa000000000000fffa000000000000fffa000000000000fffa000000000000fff8000055000000ff00000055000000ff00000050000000ff00000050000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 866, 915, 1209, 1217, 1258, 1609]) (ps := [(8, [1609], [1266])]) (by decide +kernel)

theorem contract3475_0 : P.leaf 30 55600 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 480), (5, 3, 523), (3, 1, 529), (30, 1, 866), (11, 1, 872), (12, 1, 915), (29, 1, 915), (8, 0, 1266), (14, 0, 531), (31, 1, 1217)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3475_0 : P.sumLeaves 24 3558400 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55600) rows (by decide) (by decide)).symm.trans contract3475_0

theorem contract3475_1 : P.leaf 30 55601 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 480), (3, 1, 523), (30, 1, 866), (11, 1, 872), (8, 0, 1266), (14, 0, 531), (5, 1, 433), (12, 1, 825), (31, 1, 1217)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3475_1 : P.sumLeaves 24 3558464 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55601) rows (by decide) (by decide)).symm.trans contract3475_1

theorem c3475_2 : P.sumLeaves 24 3558528 384 = 153744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3475) (lo := 128) (len := 384) (W := 153744) check rows elimOK (by decide) (by decide) cover3475 (by decide)
  decide +kernel

theorem contract3475_3 : P.leaf 30 55608 = 10656 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 55608) (ss := [(2, 1, 480), (5, 3, 523), (3, 1, 529), (8, 1, 531), (16, 1, 531), (17, 1, 537), (30, 1, 866), (11, 1, 872), (12, 1, 915), (29, 1, 915), (18, 1, 1265), (7, 1, 530), (19, 1, 1273), (9, 1, 538)]) (ids := [2, 4, 8, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29]) (cs := [1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5, 6, 7, 1, 1, 1, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 1, 17]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3475_3 : P.sumLeaves 24 3558912 64 = 10656 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55608) rows (by decide) (by decide)).symm.trans contract3475_3

theorem c3475_4 : P.sumLeaves 24 3558976 192 = 289712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3475) (lo := 576) (len := 192) (W := 289712) check rows elimOK (by decide) (by decide) cover3475 (by decide)
  decide +kernel

theorem contract3475_5 : P.leaf 30 55612 = 34848 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 55612) (ss := [(5, 1, 523), (8, 1, 531), (16, 1, 531), (17, 1, 537), (30, 1, 866), (11, 1, 872), (12, 1, 817), (31, 1, 1209), (18, 1, 1265), (7, 1, 530), (19, 1, 1273), (9, 1, 538)]) (ids := [0, 1, 2, 4, 8, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) (cs := [2, 3, 4, 1, 5, 1, 1, 1, 6, 1, 1, 7, 8, 9, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3475_5 : P.sumLeaves 24 3559168 64 = 34848 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55612) rows (by decide) (by decide)).symm.trans contract3475_5

theorem c3475_6 : P.sumLeaves 24 3559232 192 = 978464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3475) (lo := 832) (len := 192) (W := 978464) check rows elimOK (by decide) (by decide) cover3475 (by decide)
  decide +kernel

theorem h3475 : P.leaf 34 3475 = 1467424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (384, 153744), (64, 10656), (192, 289712), (64, 34848), (192, 978464)]) (.cons c3475_0 (.cons c3475_1 (.cons c3475_2 (.cons c3475_3 (.cons c3475_4 (.cons c3475_5 (.cons c3475_6 (.nil)))))))) (by decide) (by decide))

theorem cover3476 : P.CoversSplit 24 10 3476 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 475, 479, 508, 516, 865, 866, 915, 916, 1209, 1217]) (ps := [(6, [479], [473]), (8, [537], [1266])]) (by decide +kernel)

theorem c3476_0 : P.sumLeaves 24 3559424 1024 = 15936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3476) (lo := 0) (len := 1024) (W := 15936) check rows elimOK (by decide) (by decide) cover3476 (by decide)
  decide +kernel

theorem h3476 : P.leaf 34 3476 = 15936 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15936)]) (.cons c3476_0 (.nil)) (by decide) (by decide))

theorem cover3477 : P.CoversSplit 24 10 3477 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000220000000000000000000000000000002200000011000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 475, 516, 517, 559, 858, 865, 866, 915, 1209, 1217]) (ps := [(8, [615], [1266]), (12, [479], [915])]) (by decide +kernel)

theorem c3477_0 : P.sumLeaves 24 3560448 448 = 416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3477) (lo := 0) (len := 448) (W := 416) check rows elimOK (by decide) (by decide) cover3477 (by decide)
  decide +kernel

theorem contract3477_1 : P.leaf 30 55639 = 8984 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 55639) (ss := [(27, 1, 473), (29, 1, 473), (2, 1, 475), (30, 1, 866), (11, 1, 872), (6, 1, 459), (10, 1, 809), (12, 1, 817), (14, 1, 923), (19, 1, 929), (18, 1, 965), (13, 1, 922), (31, 1, 1209), (16, 1, 1265), (17, 1, 1273)]) (ids := [1, 2, 3, 6, 7, 13, 18, 19, 20, 22, 23, 24, 26, 5, 21]) (cs := [1, 2, 3, 4, 1, 15, 5, 6, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8, 9, 10, 16, 11, 12, 13, 1, 14, 1, 1, 1]) (bs := [13, 2]) (W := 8984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3477_1 : P.sumLeaves 24 3560896 64 = 8984 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55639) rows (by decide) (by decide)).symm.trans contract3477_1

theorem contract3477_2 : P.leaf 30 55640 = 272 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 55640) (ss := [(29, 1, 475), (5, 3, 523), (8, 1, 531), (16, 1, 531), (3, 1, 529), (17, 1, 615), (10, 0, 865), (6, 0, 809), (12, 0, 459), (11, 1, 461), (27, 0, 459), (31, 1, 468), (26, 1, 479), (9, 1, 538), (25, 1, 573), (23, 1, 811), (30, 1, 866), (18, 1, 1265), (19, 1, 1273)]) (ids := [0, 2, 5, 11, 12, 18, 19, 20, 22, 26, 13]) (cs := [2, 1, 3, 1, 0, 4, 1, 1, 0, 1, 0, 5, 6, 12, 1, 1, 1, 1, 7, 8, 9, 1, 10, 1, 1, 0, 11, 1, 1, 1]) (bs := [10, 1]) (W := 272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3477_2 : P.sumLeaves 24 3560960 64 = 272 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55640) rows (by decide) (by decide)).symm.trans contract3477_2

theorem c3477_3 : P.sumLeaves 24 3561024 256 = 2736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3477) (lo := 576) (len := 256) (W := 2736) check rows elimOK (by decide) (by decide) cover3477 (by decide)
  decide +kernel

theorem contract3477_4 : P.leaf 30 55645 = 17488 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 55645) (ss := [(27, 1, 473), (29, 1, 473), (8, 1, 531), (16, 1, 531), (17, 1, 615), (30, 1, 866), (11, 1, 872), (6, 1, 459), (10, 1, 809), (12, 1, 817), (31, 1, 1209), (18, 1, 1265), (19, 1, 1273), (9, 1, 538)]) (ids := [0, 1, 2, 3, 5, 11, 12, 13, 18, 19, 20, 22, 24, 26, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 1, 1, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 10, 11, 12, 16, 13, 17, 14, 1, 15, 1, 1, 1]) (bs := [14, 2]) (W := 17488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3477_4 : P.sumLeaves 24 3561280 64 = 17488 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55645) rows (by decide) (by decide)).symm.trans contract3477_4

theorem c3477_5 : P.sumLeaves 24 3561344 128 = 114288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3477) (lo := 896) (len := 128) (W := 114288) check rows elimOK (by decide) (by decide) cover3477 (by decide)
  decide +kernel

theorem h3477 : P.leaf 34 3477 = 144184 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 416), (64, 8984), (64, 272), (256, 2736), (64, 17488), (128, 114288)]) (.cons c3477_0 (.cons c3477_1 (.cons c3477_2 (.cons c3477_3 (.cons c3477_4 (.cons c3477_5 (.nil))))))) (by decide) (by decide))

theorem cover3478 : P.CoversSplit 24 10 3478 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000a000000000000000a0a0000000000000a000000000000000a0a0000000000000a0a000000000000000000000000000000000000000000000a0a0000000000000a00000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 479, 516, 858, 865, 866, 1217, 1609]) (ps := [(8, [537], [1266])]) (by decide +kernel)

theorem c3478_0 : P.sumLeaves 24 3561472 192 = 2592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3478) (lo := 0) (len := 192) (W := 2592) check rows elimOK (by decide) (by decide) cover3478 (by decide)
  decide +kernel

theorem contract3478_1 : P.leaf 30 55651 = 4608 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 55651) (ss := [(26, 1, 479), (2, 1, 480), (28, 1, 465), (31, 1, 516), (3, 1, 523), (30, 1, 858), (19, 1, 866), (18, 1, 867), (11, 1, 872), (10, 1, 809), (12, 1, 901), (14, 1, 965), (16, 1, 1265), (17, 1, 1273)]) (ids := [2, 3, 4, 5, 6, 7, 11, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 8, 1, 9, 1, 1, 1, 1, 10, 11, 12, 16, 17, 13, 1, 14, 1, 15, 1, 1]) (bs := [14, 2]) (W := 4608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3478_1 : P.sumLeaves 24 3561664 64 = 4608 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55651) rows (by decide) (by decide)).symm.trans contract3478_1

theorem c3478_2 : P.sumLeaves 24 3561728 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3478) (lo := 256) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3478 (by decide)
  decide +kernel

theorem contract3478_3 : P.leaf 30 55654 = 11904 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 55654) (ss := [(2, 1, 466), (26, 1, 479), (28, 1, 465), (31, 1, 516), (5, 1, 523), (30, 1, 858), (19, 1, 866), (18, 1, 867), (11, 1, 872), (12, 1, 817), (14, 1, 965)]) (ids := [1, 2, 4, 5, 6, 7, 8, 11, 13, 14, 15, 18, 19, 20, 21, 23, 25, 27, 22]) (cs := [1, 2, 3, 1, 4, 5, 6, 7, 8, 1, 1, 9, 1, 10, 11, 12, 1, 1, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 1]) (W := 11904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3478_3 : P.sumLeaves 24 3561856 64 = 11904 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55654) rows (by decide) (by decide)).symm.trans contract3478_3

theorem contract3478_4 : P.leaf 30 55655 = 20384 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 55655) (ss := [(26, 1, 479), (28, 1, 858), (31, 1, 516), (30, 1, 858), (19, 1, 866), (18, 1, 867), (11, 1, 872), (10, 1, 809), (12, 1, 817), (14, 1, 965), (16, 1, 1265), (17, 1, 1273)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 11, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 10, 1, 11, 1, 1, 1, 1, 12, 13, 14, 18, 19, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 2]) (W := 20384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3478_4 : P.sumLeaves 24 3561920 64 = 20384 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55655) rows (by decide) (by decide)).symm.trans contract3478_4

theorem c3478_5 : P.sumLeaves 24 3561984 64 = 1344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3478) (lo := 512) (len := 64) (W := 1344) check rows elimOK (by decide) (by decide) cover3478 (by decide)
  decide +kernel

theorem contract3478_6 : P.leaf 30 55657 = 4512 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 55657) (ss := [(26, 6, 479), (3, 1, 523), (8, 1, 531), (6, 1, 468), (16, 1, 531), (17, 1, 615), (9, 1, 538), (10, 1, 809), (11, 1, 809), (12, 1, 817), (28, 1, 858), (31, 1, 516), (30, 1, 858), (18, 1, 1265), (19, 1, 1273)]) (ids := [0, 2, 3, 5, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 1, 3, 4, 1, 5, 1, 1, 1, 1, 1, 6, 7, 8, 1, 1, 1, 1, 9, 10, 11, 15, 16, 12, 1, 13, 1, 14, 1, 1]) (bs := [13, 2]) (W := 4512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3478_6 : P.sumLeaves 24 3562048 64 = 4512 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55657) rows (by decide) (by decide)).symm.trans contract3478_6

theorem c3478_7 : P.sumLeaves 24 3562112 128 = 60584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3478) (lo := 640) (len := 128) (W := 60584) check rows elimOK (by decide) (by decide) cover3478 (by decide)
  decide +kernel

theorem contract3478_8 : P.leaf 30 55660 = 3616 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 55660) (ss := [(2, 1, 466), (26, 6, 479), (5, 1, 523), (8, 1, 531), (6, 1, 468), (28, 1, 465), (31, 1, 516), (16, 1, 531), (17, 1, 615), (9, 1, 538), (10, 1, 809), (11, 1, 809), (12, 1, 817), (30, 1, 858), (18, 1, 1265), (19, 1, 1273)]) (ids := [1, 2, 5, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6, 7, 1, 1, 1, 1, 8, 9, 10, 14, 15, 11, 1, 12, 1, 13, 1, 1]) (bs := [12, 2]) (W := 3616) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3478_8 : P.sumLeaves 24 3562240 64 = 3616 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55660) rows (by decide) (by decide)).symm.trans contract3478_8

theorem contract3478_9 : P.leaf 30 55661 = 13808 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 55661) (ss := [(26, 6, 479), (8, 1, 531), (6, 1, 468), (16, 1, 531), (17, 1, 615), (9, 1, 538), (10, 1, 809), (11, 1, 809), (12, 1, 817), (28, 1, 858), (31, 1, 516), (30, 1, 858), (18, 1, 1265), (19, 1, 1273)]) (ids := [0, 1, 2, 3, 5, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 1, 1, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 10, 11, 12, 16, 17, 13, 1, 14, 1, 15, 1, 1]) (bs := [14, 2]) (W := 13808) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3478_9 : P.sumLeaves 24 3562304 64 = 13808 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55661) rows (by decide) (by decide)).symm.trans contract3478_9

theorem c3478_10 : P.sumLeaves 24 3562368 128 = 226176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3478) (lo := 896) (len := 128) (W := 226176) check rows elimOK (by decide) (by decide) cover3478 (by decide)
  decide +kernel

theorem h3478 : P.leaf 34 3478 = 349528 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 2592), (64, 4608), (128, 0), (64, 11904), (64, 20384), (64, 1344), (64, 4512), (128, 60584), (64, 3616), (64, 13808), (128, 226176)]) (.cons c3478_0 (.cons c3478_1 (.cons c3478_2 (.cons c3478_3 (.cons c3478_4 (.cons c3478_5 (.cons c3478_6 (.cons c3478_7 (.cons c3478_8 (.cons c3478_9 (.cons c3478_10 (.nil)))))))))))) (by decide) (by decide))

theorem cover3479 : P.CoversSplit 24 10 3479 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000fff8000055000000ff00000055000000fff8000055000000ff00000055000000fffa000000000000fffa00000000000000000000000000000000000000000000fff8000055000000ff0000005500000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 858, 865, 866, 915, 1209, 1217, 1258, 1609]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c3479_0 : P.sumLeaves 24 3562496 512 = 311876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3479) (lo := 0) (len := 512) (W := 311876) check rows elimOK (by decide) (by decide) cover3479 (by decide)
  decide +kernel

theorem contract3479_1 : P.leaf 30 55672 = 28152 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 55672) (ss := [(5, 3, 523), (3, 1, 529), (8, 1, 531), (16, 1, 531), (17, 1, 615), (30, 1, 866), (11, 1, 872), (12, 1, 901), (29, 1, 915), (18, 1, 1265), (19, 1, 1273), (9, 1, 538)]) (ids := [0, 2, 4, 5, 8, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29]) (cs := [2, 1, 3, 1, 4, 5, 1, 1, 6, 1, 1, 7, 8, 9, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1, 1, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3479_1 : P.sumLeaves 24 3563008 64 = 28152 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55672) rows (by decide) (by decide)).symm.trans contract3479_1

theorem c3479_2 : P.sumLeaves 24 3563072 442 = 2328870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3479) (lo := 576) (len := 442) (W := 2328870) check rows elimOK (by decide) (by decide) cover3479 (by decide)
  decide +kernel

theorem c3479_3 : P.sumLeaves 24 3563514 6 = 923300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3479) (lo := 1018) (len := 6) (W := 923300) check rows elimOK (by decide) (by decide) cover3479 (by decide)
  decide +kernel

theorem h3479 : P.leaf 34 3479 = 3592198 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 311876), (64, 28152), (442, 2328870), (6, 923300)]) (.cons c3479_0 (.cons c3479_1 (.cons c3479_2 (.cons c3479_3 (.nil))))) (by decide) (by decide))

theorem cover3484 : P.CoversSplit 24 10 3484 0x8000000000000400000000000000000080000000000000000000000000000000000000000000000020000000000001000000000000000000200000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000200000000000010000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 865, 915, 1209, 1217]) (ps := [(8, [531], [1266])]) (by decide +kernel)

theorem c3484_0 : P.sumLeaves 24 3567616 1024 = 77868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3484) (lo := 0) (len := 1024) (W := 77868) check rows elimOK (by decide) (by decide) cover3484 (by decide)
  decide +kernel

theorem h3484 : P.leaf 34 3484 = 77868 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 77868)]) (.cons c3484_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3276, 48), (3277, 48), (3278, 48), (3279, 48), (3290, 24), (3291, 24), (3292, 48), (3293, 48), (3294, 48), (3295, 48), (3308, 24), (3309, 24), (3310, 48), (3311, 48), (3326, 24), (3327, 24), (3456, 3), (3457, 12), (3459, 12), (3460, 24), (3461, 48), (3463, 24), (3468, 12), (3469, 24), (3471, 12), (3474, 6), (3475, 12), (3476, 48), (3477, 48), (3478, 48), (3479, 48), (3484, 24)]

theorem segOK : checkSeg 16 perms 3276 3485 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3276 3485 1029 974597568 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 974597568)
    (SegSum.cons (w := 48) h3276 (SegSum.cons (w := 48) h3277 (SegSum.cons (w := 48) h3278 (SegSum.cons (w := 48) h3279 (SegSum.cons (w := 24) h3290 (SegSum.cons (w := 24) h3291 (SegSum.cons (w := 48) h3292 (SegSum.cons (w := 48) h3293 (SegSum.cons (w := 48) h3294 (SegSum.cons (w := 48) h3295 (SegSum.cons (w := 24) h3308 (SegSum.cons (w := 24) h3309 (SegSum.cons (w := 48) h3310 (SegSum.cons (w := 48) h3311 (SegSum.cons (w := 24) h3326 (SegSum.cons (w := 24) h3327 (SegSum.cons (w := 3) h3456 (SegSum.cons (w := 12) h3457 (SegSum.cons (w := 12) h3459 (SegSum.cons (w := 24) h3460 (SegSum.cons (w := 48) h3461 (SegSum.cons (w := 24) h3463 (SegSum.cons (w := 12) h3468 (SegSum.cons (w := 24) h3469 (SegSum.cons (w := 12) h3471 (SegSum.cons (w := 6) h3474 (SegSum.cons (w := 12) h3475 (SegSum.cons (w := 48) h3476 (SegSum.cons (w := 48) h3477 (SegSum.cons (w := 48) h3478 (SegSum.cons (w := 48) h3479 (SegSum.cons (w := 24) h3484 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S19
