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

theorem cover3485 : P.CoversSplit 24 10 3485 0xcc000000000040000000000000000000cc0000000000400000000000000000000000000000000000330000001100100000000000000000003300000011001000cc004000000040000000000000000000cc0040000000400000000000000000000000000000000000330010001100100000000000000000003300100010001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 858, 865, 915, 1209, 1217, 1258]) (by decide +kernel)

theorem c3485_0 : P.sumLeaves 24 3568640 128 = 1176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3485) (lo := 0) (len := 128) (W := 1176) check rows elimOK (by decide) (by decide) cover3485 (by decide)
  decide +kernel

theorem contract3485_1 : P.leaf 30 55762 = 8580 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 55762) (ss := [(5, 3, 523), (3, 1, 529), (27, 0, 865), (11, 1, 872), (14, 1, 923), (29, 1, 1258), (6, 0, 473), (10, 0, 459), (12, 0, 459), (23, 1, 810), (19, 18, 1308)]) (ids := [0, 2, 5, 6, 7, 11, 13, 14, 15, 16, 18, 19, 20, 22, 24, 26, 28, 29, 23]) (cs := [2, 1, 3, 1, 0, 4, 5, 6, 0, 1, 0, 7, 1, 8, 9, 10, 11, 11, 12, 13, 14, 1, 15, 20, 16, 0, 17, 1, 18, 19]) (bs := [18, 1]) (W := 8580) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3485_1 : P.sumLeaves 24 3568768 64 = 8580 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 55762) rows (by decide) (by decide)).symm.trans contract3485_1

theorem c3485_2 : P.sumLeaves 24 3568832 832 = 733826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3485) (lo := 192) (len := 832) (W := 733826) check rows elimOK (by decide) (by decide) cover3485 (by decide)
  decide +kernel

theorem h3485 : P.leaf 34 3485 = 743582 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 1176), (64, 8580), (832, 733826)]) (.cons c3485_0 (.cons c3485_1 (.cons c3485_2 (.nil)))) (by decide) (by decide))

theorem cover3486 : P.CoversSplit 24 10 3486 0xa0a0000000000505a0a0000000000505a0a0000000000000a0a0000000000000a0a0000000000500a000000000000500a0a0000000000000a000000000000000a0a0000000000505a0a000000000050500000000000000000000000000000000a0a0000000000500a00000000000050000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 1217, 1609]) (ps := [(8, [531], [1266])]) (by decide +kernel)

theorem c3486_0 : P.sumLeaves 24 3569664 1024 = 3034331 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3486) (lo := 0) (len := 1024) (W := 3034331) check rows elimOK (by decide) (by decide) cover3486 (by decide)
  decide +kernel

theorem h3486 : P.leaf 34 3486 = 3034331 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3034331)]) (.cons c3486_0 (.nil)) (by decide) (by decide))

theorem cover3487 : P.CoversSplit 24 10 3487 0xfffa000000005050fffa000000005050fffa000000005050fffa000000005050fff8000055005000ff00000055005000fff8000055005000ff00000055005000fffa505000005050fffa505000005050fffa505000005050fffa505000005050fff8505055005000ff00500055005000ff00500050005000ff00500050005000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 865, 1209, 1217, 1258, 1609]) (ps := [(8, [1609], [1266])]) (by decide +kernel)

theorem c3487_0 : P.sumLeaves 24 3570688 366 = 1058154 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3487) (lo := 0) (len := 366) (W := 1058154) check rows elimOK (by decide) (by decide) cover3487 (by decide)
  decide +kernel

theorem c3487_1 : P.sumLeaves 24 3571054 302 = 2818160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3487) (lo := 366) (len := 302) (W := 2818160) check rows elimOK (by decide) (by decide) cover3487 (by decide)
  decide +kernel

theorem c3487_2 : P.sumLeaves 24 3571356 351 = 12238180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3487) (lo := 668) (len := 351) (W := 12238180) check rows elimOK (by decide) (by decide) cover3487 (by decide)
  decide +kernel

theorem c3487_3 : P.sumLeaves 24 3571707 5 = 4146200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3487) (lo := 1019) (len := 5) (W := 4146200) check rows elimOK (by decide) (by decide) cover3487 (by decide)
  decide +kernel

theorem h3487 : P.leaf 34 3487 = 20260694 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(366, 1058154), (302, 2818160), (351, 12238180), (5, 4146200)]) (.cons c3487_0 (.cons c3487_1 (.cons c3487_2 (.cons c3487_3 (.nil))))) (by decide) (by decide))

theorem cover3492 : P.CoversSplit 24 10 3492 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3492_0 : P.sumLeaves 24 3575808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3492) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3492 (by decide)
  decide +kernel

theorem h3492 : P.leaf 34 3492 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3492_0 (.nil)) (by decide) (by decide))

theorem cover3493 : P.CoversSplit 24 10 3493 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 475, 515, 522, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem c3493_0 : P.sumLeaves 24 3576832 1024 = 36512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3493) (lo := 0) (len := 1024) (W := 36512) check rows elimOK (by decide) (by decide) cover3493 (by decide)
  decide +kernel

theorem h3493 : P.leaf 34 3493 = 36512 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 36512)]) (.cons c3493_0 (.nil)) (by decide) (by decide))

theorem cover3494 : P.CoversSplit 24 10 3494 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem c3494_0 : P.sumLeaves 24 3577856 1024 = 55504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3494) (lo := 0) (len := 1024) (W := 55504) check rows elimOK (by decide) (by decide) cover3494 (by decide)
  decide +kernel

theorem h3494 : P.leaf 34 3494 = 55504 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 55504)]) (.cons c3494_0 (.nil)) (by decide) (by decide))

theorem cover3495 : P.CoversSplit 24 10 3495 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c3495_0 : P.sumLeaves 24 3578880 1024 = 209920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3495) (lo := 0) (len := 1024) (W := 209920) check rows elimOK (by decide) (by decide) cover3495 (by decide)
  decide +kernel

theorem h3495 : P.leaf 34 3495 = 209920 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 209920)]) (.cons c3495_0 (.nil)) (by decide) (by decide))

theorem cover3496 : P.CoversSplit 24 10 3496 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3496_0 : P.sumLeaves 24 3579904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3496) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3496 (by decide)
  decide +kernel

theorem h3496 : P.leaf 34 3496 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3496_0 (.nil)) (by decide) (by decide))

theorem cover3497 : P.CoversSplit 24 10 3497 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 474, 515, 522, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem c3497_0 : P.sumLeaves 24 3580928 1024 = 123392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3497) (lo := 0) (len := 1024) (W := 123392) check rows elimOK (by decide) (by decide) cover3497 (by decide)
  decide +kernel

theorem h3497 : P.leaf 34 3497 = 123392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 123392)]) (.cons c3497_0 (.nil)) (by decide) (by decide))

theorem cover3498 : P.CoversSplit 24 10 3498 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem c3498_0 : P.sumLeaves 24 3581952 1024 = 54800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3498) (lo := 0) (len := 1024) (W := 54800) check rows elimOK (by decide) (by decide) cover3498 (by decide)
  decide +kernel

theorem h3498 : P.leaf 34 3498 = 54800 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 54800)]) (.cons c3498_0 (.nil)) (by decide) (by decide))

theorem cover3499 : P.CoversSplit 24 10 3499 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c3499_0 : P.sumLeaves 24 3582976 1024 = 545752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3499) (lo := 0) (len := 1024) (W := 545752) check rows elimOK (by decide) (by decide) cover3499 (by decide)
  decide +kernel

theorem h3499 : P.leaf 34 3499 = 545752 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 545752)]) (.cons c3499_0 (.nil)) (by decide) (by decide))

theorem cover3500 : P.CoversSplit 24 10 3500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3500_0 : P.sumLeaves 24 3584000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3500) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3500 (by decide)
  decide +kernel

theorem h3500 : P.leaf 34 3500 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3500_0 (.nil)) (by decide) (by decide))

theorem cover3501 : P.CoversSplit 24 10 3501 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem c3501_0 : P.sumLeaves 24 3585024 1024 = 166496 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3501) (lo := 0) (len := 1024) (W := 166496) check rows elimOK (by decide) (by decide) cover3501 (by decide)
  decide +kernel

theorem h3501 : P.leaf 34 3501 = 166496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 166496)]) (.cons c3501_0 (.nil)) (by decide) (by decide))

theorem cover3502 : P.CoversSplit 24 10 3502 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem c3502_0 : P.sumLeaves 24 3586048 1024 = 381120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3502) (lo := 0) (len := 1024) (W := 381120) check rows elimOK (by decide) (by decide) cover3502 (by decide)
  decide +kernel

theorem h3502 : P.leaf 34 3502 = 381120 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 381120)]) (.cons c3502_0 (.nil)) (by decide) (by decide))

theorem cover3503 : P.CoversSplit 24 10 3503 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c3503_0 : P.sumLeaves 24 3587072 1024 = 1187447 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3503) (lo := 0) (len := 1024) (W := 1187447) check rows elimOK (by decide) (by decide) cover3503 (by decide)
  decide +kernel

theorem h3503 : P.leaf 34 3503 = 1187447 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1187447)]) (.cons c3503_0 (.nil)) (by decide) (by decide))

theorem cover3510 : P.CoversSplit 24 10 3510 0xf0f5000000000000f0f5000000000000a0a0000000000000a0a0000000000000f0f0000000000000f000000000000000a0a0000000000000a000000000000000f0f5000000000000f0f500000000000000000000000000000000000000000000f0f0000000000000f00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 866, 908, 1209, 1210, 1308]) (by decide +kernel)

theorem c3510_0 : P.sumLeaves 24 3594240 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3510) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3510 (by decide)
  decide +kernel

theorem contract3510_1 : P.leaf 30 56162 = 7872 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 56162) (ss := [(2, 1, 466), (5, 3, 524), (3, 1, 529), (10, 1, 865), (29, 1, 865), (30, 19, 866), (18, 1, 867), (19, 11, 872), (11, 1, 901), (28, 1, 858), (12, 1, 901), (13, 1, 922), (14, 1, 965), (31, 1, 1251)]) (ids := [2, 4, 5, 6, 7, 13, 14, 15, 18, 19, 20, 23, 24, 25, 21, 22]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 1, 1, 1, 1, 1, 7, 8, 9, 1, 1, 10, 11, 12, 16, 17, 13, 14, 15, 1, 1, 1, 1]) (bs := [14, 2]) (W := 7872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3510_1 : P.sumLeaves 24 3594368 64 = 7872 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56162) rows (by decide) (by decide)).symm.trans contract3510_1

theorem contract3510_2 : P.leaf 30 56163 = 17056 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 56163) (ss := [(2, 1, 480), (3, 1, 524), (30, 19, 866), (18, 1, 867), (19, 11, 872), (11, 1, 901), (10, 1, 809), (12, 1, 901), (14, 1, 965), (31, 1, 1251), (16, 1, 1265)]) (ids := [2, 3, 4, 5, 6, 7, 11, 13, 15, 18, 19, 20, 22, 23, 24, 25, 26, 27, 21]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 8, 1, 9, 1, 10, 1, 1, 11, 12, 13, 20, 14, 15, 16, 17, 18, 19, 1, 1]) (bs := [18, 1]) (W := 17056) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3510_2 : P.sumLeaves 24 3594432 64 = 17056 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56163) rows (by decide) (by decide)).symm.trans contract3510_2

theorem c3510_3 : P.sumLeaves 24 3594496 320 = 120672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3510) (lo := 256) (len := 320) (W := 120672) check rows elimOK (by decide) (by decide) cover3510 (by decide)
  decide +kernel

theorem contract3510_4 : P.leaf 30 56169 = 18216 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 56169) (ss := [(8, 1, 531), (6, 1, 468), (16, 1, 531), (10, 1, 809), (11, 1, 809), (12, 1, 817), (30, 1, 866), (26, 1, 517), (31, 1, 517), (28, 1, 858), (18, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 1, 1, 1, 8, 9, 10, 1, 11, 1, 12, 13, 14, 15, 19, 20, 16, 1, 17, 1, 18, 1, 1]) (bs := [17, 2]) (W := 18216) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3510_4 : P.sumLeaves 24 3594816 64 = 18216 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56169) rows (by decide) (by decide)).symm.trans contract3510_4

theorem c3510_5 : P.sumLeaves 24 3594880 128 = 161892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3510) (lo := 640) (len := 128) (W := 161892) check rows elimOK (by decide) (by decide) cover3510 (by decide)
  decide +kernel

theorem contract3510_6 : P.leaf 30 56172 = 16960 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 56172) (ss := [(2, 1, 466), (5, 1, 524), (8, 1, 531), (6, 1, 468), (16, 1, 531), (10, 1, 809), (11, 1, 809), (12, 1, 817), (30, 1, 866), (26, 1, 517), (31, 1, 517), (28, 1, 858), (18, 1, 1265)]) (ids := [1, 2, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 1, 6, 7, 8, 1, 9, 1, 10, 11, 12, 13, 17, 18, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 16960) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3510_6 : P.sumLeaves 24 3595008 64 = 16960 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56172) rows (by decide) (by decide)).symm.trans contract3510_6

theorem contract3510_7 : P.leaf 30 56173 = 41032 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 56173) (ss := [(8, 1, 531), (6, 1, 468), (16, 1, 531), (10, 1, 809), (11, 1, 809), (12, 1, 817), (30, 1, 866), (26, 1, 517), (31, 1, 517), (28, 1, 858), (18, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 1, 1, 1, 8, 9, 10, 1, 11, 1, 12, 13, 14, 15, 19, 20, 16, 1, 17, 1, 18, 1, 1]) (bs := [17, 2]) (W := 41032) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3510_7 : P.sumLeaves 24 3595072 64 = 41032 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56173) rows (by decide) (by decide)).symm.trans contract3510_7

theorem c3510_8 : P.sumLeaves 24 3595136 128 = 612776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3510) (lo := 896) (len := 128) (W := 612776) check rows elimOK (by decide) (by decide) cover3510 (by decide)
  decide +kernel

theorem h3510 : P.leaf 34 3510 = 996476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 7872), (64, 17056), (320, 120672), (64, 18216), (128, 161892), (64, 16960), (64, 41032), (128, 612776)]) (.cons c3510_0 (.cons c3510_1 (.cons c3510_2 (.cons c3510_3 (.cons c3510_4 (.cons c3510_5 (.cons c3510_6 (.cons c3510_7 (.cons c3510_8 (.nil)))))))))) (by decide) (by decide))

theorem cover3511 : P.CoversSplit 24 10 3511 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000fff8000000000000ff00000000000000fff8000000000000ff00000000000000fffa000000000000fffa00000000000000000000000000000000000000000000fff8000000000000ff0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 866, 915, 1202, 1209, 1210, 1308]) (by decide +kernel)

theorem c3511_0 : P.sumLeaves 24 3595264 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3511) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3511 (by decide)
  decide +kernel

theorem contract3511_1 : P.leaf 30 56178 = 25408 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 56178) (ss := [(2, 1, 480), (5, 3, 524), (3, 1, 529), (30, 1, 866), (11, 1, 872), (12, 1, 901), (29, 1, 915), (14, 1, 965), (19, 1, 929), (18, 1, 965), (13, 1, 922), (31, 1, 1251)]) (ids := [2, 4, 5, 6, 7, 8, 13, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 7, 1, 1, 1, 1, 8, 9, 10, 1, 1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3511_1 : P.sumLeaves 24 3595392 64 = 25408 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56178) rows (by decide) (by decide)).symm.trans contract3511_1

theorem c3511_2 : P.sumLeaves 24 3595456 639 = 2321576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3511) (lo := 192) (len := 639) (W := 2321576) check rows elimOK (by decide) (by decide) cover3511 (by decide)
  decide +kernel

theorem c3511_3 : P.sumLeaves 24 3596095 193 = 4146308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3511) (lo := 831) (len := 193) (W := 4146308) check rows elimOK (by decide) (by decide) cover3511 (by decide)
  decide +kernel

theorem h3511 : P.leaf 34 3511 = 6493292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 25408), (639, 2321576), (193, 4146308)]) (.cons c3511_0 (.cons c3511_1 (.cons c3511_2 (.cons c3511_3 (.nil))))) (by decide) (by decide))

theorem cover3514 : P.CoversSplit 24 10 3514 0xf0f5000000000000f0f5000000000000a0a0000000000000a0a0000000000000f0f0000000000000f000000000000000a0a0000000000000a000000000000000f0f5000000000000f0f500000000000000000000000000000000000000000000f0f0000000000000f00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 867, 1209, 1210, 1251, 1308]) (by decide +kernel)

theorem c3514_0 : P.sumLeaves 24 3598336 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3514) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3514 (by decide)
  decide +kernel

theorem contract3514_1 : P.leaf 30 56226 = 10464 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 56226) (ss := [(2, 1, 466), (5, 3, 524), (3, 1, 529), (10, 1, 865), (29, 1, 865), (19, 1, 866), (30, 18, 867), (11, 1, 872), (18, 1, 879), (28, 1, 858), (12, 1, 901), (15, 1, 930), (14, 1, 965), (31, 1, 1251)]) (ids := [2, 4, 5, 6, 7, 11, 14, 15, 18, 19, 23, 24, 25, 20, 21, 22]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 1, 1, 1, 7, 1, 1, 8, 9, 1, 1, 10, 11, 15, 16, 17, 12, 13, 14, 1, 1, 1, 1]) (bs := [13, 3]) (W := 10464) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3514_1 : P.sumLeaves 24 3598464 64 = 10464 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56226) rows (by decide) (by decide)).symm.trans contract3514_1

theorem contract3514_2 : P.leaf 30 56227 = 25312 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 56227) (ss := [(2, 1, 487), (3, 1, 524), (19, 1, 866), (30, 18, 867), (11, 1, 872), (10, 1, 809), (18, 1, 879), (12, 1, 901), (14, 1, 965), (31, 1, 1251), (16, 1, 1265)]) (ids := [2, 3, 4, 5, 6, 7, 11, 13, 15, 18, 19, 20, 22, 23, 24, 25, 26, 27, 21]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 8, 1, 9, 1, 10, 1, 1, 11, 12, 13, 20, 14, 15, 16, 17, 18, 19, 1, 1]) (bs := [18, 1]) (W := 25312) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3514_2 : P.sumLeaves 24 3598528 64 = 25312 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56227) rows (by decide) (by decide)).symm.trans contract3514_2

theorem c3514_3 : P.sumLeaves 24 3598592 320 = 160528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3514) (lo := 256) (len := 320) (W := 160528) check rows elimOK (by decide) (by decide) cover3514 (by decide)
  decide +kernel

theorem contract3514_4 : P.leaf 30 56233 = 47792 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 56233) (ss := [(30, 1, 867), (26, 1, 517), (6, 1, 486), (31, 1, 517), (10, 1, 809), (11, 1, 809), (12, 1, 818), (28, 1, 858), (16, 1, 1272), (18, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 10, 11, 1, 12, 1, 13, 14, 15, 16, 20, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 47792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3514_4 : P.sumLeaves 24 3598912 64 = 47792 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56233) rows (by decide) (by decide)).symm.trans contract3514_4

theorem c3514_5 : P.sumLeaves 24 3598976 128 = 265400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3514) (lo := 640) (len := 128) (W := 265400) check rows elimOK (by decide) (by decide) cover3514 (by decide)
  decide +kernel

theorem contract3514_6 : P.leaf 30 56236 = 17824 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 56236) (ss := [(2, 1, 466), (5, 1, 524), (30, 1, 867), (26, 1, 517), (6, 1, 486), (31, 1, 517), (10, 1, 809), (11, 1, 809), (12, 1, 818), (28, 1, 858), (8, 1, 1266), (16, 1, 1272), (18, 1, 1265)]) (ids := [1, 2, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 1, 6, 7, 8, 1, 9, 1, 10, 11, 12, 13, 17, 18, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 17824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3514_6 : P.sumLeaves 24 3599104 64 = 17824 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56236) rows (by decide) (by decide)).symm.trans contract3514_6

theorem contract3514_7 : P.leaf 30 56237 = 110576 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 56237) (ss := [(30, 1, 867), (26, 1, 517), (6, 1, 486), (31, 1, 517), (10, 1, 809), (11, 1, 809), (12, 1, 818), (28, 1, 858), (16, 1, 1272), (18, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 12, 13, 15, 17, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 10, 11, 1, 12, 1, 13, 14, 15, 16, 20, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 110576) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3514_7 : P.sumLeaves 24 3599168 64 = 110576 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56237) rows (by decide) (by decide)).symm.trans contract3514_7

theorem c3514_8 : P.sumLeaves 24 3599232 128 = 863152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3514) (lo := 896) (len := 128) (W := 863152) check rows elimOK (by decide) (by decide) cover3514 (by decide)
  decide +kernel

theorem h3514 : P.leaf 34 3514 = 1501048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 10464), (64, 25312), (320, 160528), (64, 47792), (128, 265400), (64, 17824), (64, 110576), (128, 863152)]) (.cons c3514_0 (.cons c3514_1 (.cons c3514_2 (.cons c3514_3 (.cons c3514_4 (.cons c3514_5 (.cons c3514_6 (.cons c3514_7 (.cons c3514_8 (.nil)))))))))) (by decide) (by decide))

theorem cover3515 : P.CoversSplit 24 10 3515 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000fff8000000000000ff00000000000000fff8000000000000ff00000000000000fffa000000000000fffa00000000000000000000000000000000000000000000fff8000000000000ff0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 867, 916, 1202, 1209, 1210, 1308]) (by decide +kernel)

theorem c3515_0 : P.sumLeaves 24 3599360 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3515) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3515 (by decide)
  decide +kernel

theorem contract3515_1 : P.leaf 30 56242 = 42624 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 56242) (ss := [(2, 1, 487), (5, 3, 524), (3, 1, 529), (30, 1, 867), (11, 1, 872), (12, 1, 901), (29, 1, 916), (14, 1, 965), (18, 1, 923), (19, 1, 965), (15, 1, 930), (31, 1, 1251)]) (ids := [2, 4, 5, 6, 7, 8, 11, 14, 15, 18, 19, 21, 22, 23, 24, 25, 26, 20]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 7, 1, 1, 8, 1, 1, 9, 10, 1, 1, 11, 12, 19, 13, 14, 15, 16, 17, 18, 1, 1, 1]) (bs := [17, 1]) (W := 42624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3515_1 : P.sumLeaves 24 3599488 64 = 42624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56242) rows (by decide) (by decide)).symm.trans contract3515_1

theorem c3515_2 : P.sumLeaves 24 3599552 639 = 4119712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3515) (lo := 192) (len := 639) (W := 4119712) check rows elimOK (by decide) (by decide) cover3515 (by decide)
  decide +kernel

theorem c3515_3 : P.sumLeaves 24 3600191 193 = 6949808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3515) (lo := 831) (len := 193) (W := 6949808) check rows elimOK (by decide) (by decide) cover3515 (by decide)
  decide +kernel

theorem h3515 : P.leaf 34 3515 = 11112144 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 42624), (639, 4119712), (193, 6949808)]) (.cons c3515_0 (.cons c3515_1 (.cons c3515_2 (.cons c3515_3 (.nil))))) (by decide) (by decide))

theorem cover3516 : P.CoversSplit 24 10 3516 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000300000000000000000000000000000002000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 915, 1202, 1209, 1210, 1251, 1308]) (by decide +kernel)

theorem c3516_0 : P.sumLeaves 24 3600384 1024 = 204732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3516) (lo := 0) (len := 1024) (W := 204732) check rows elimOK (by decide) (by decide) cover3516 (by decide)
  decide +kernel

theorem h3516 : P.leaf 34 3516 = 204732 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 204732)]) (.cons c3516_0 (.nil)) (by decide) (by decide))

theorem cover3517 : P.CoversSplit 24 10 3517 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000330000000000000000000000000000003300000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000330000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 915, 1202, 1209, 1210, 1251, 1258, 1308]) (by decide +kernel)

theorem c3517_0 : P.sumLeaves 24 3601408 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3517) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3517 (by decide)
  decide +kernel

theorem contract3517_1 : P.leaf 30 56274 = 13256 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 56274) (ss := [(5, 3, 524), (3, 1, 529), (27, 0, 865), (11, 1, 872), (14, 1, 923), (30, 1, 1251), (31, 1, 1251), (29, 1, 1258), (6, 0, 473), (10, 0, 459), (12, 0, 459), (23, 1, 810), (19, 1, 1272), (18, 1, 1308)]) (ids := [0, 2, 5, 6, 7, 11, 13, 14, 15, 18, 19, 20, 22, 24, 26, 23]) (cs := [2, 1, 3, 1, 0, 4, 5, 6, 0, 1, 0, 7, 1, 8, 9, 10, 1, 1, 11, 12, 13, 1, 14, 17, 15, 0, 16, 1, 1, 1]) (bs := [15, 1]) (W := 13256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3517_1 : P.sumLeaves 24 3601536 64 = 13256 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56274) rows (by decide) (by decide)).symm.trans contract3517_1

theorem c3517_2 : P.sumLeaves 24 3601600 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3517) (lo := 192) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover3517 (by decide)
  decide +kernel

theorem contract3517_3 : P.leaf 30 56279 = 97364 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 56279) (ss := [(27, 1, 473), (29, 1, 473), (11, 1, 872), (6, 1, 459), (10, 1, 809), (12, 1, 817), (14, 1, 923), (30, 1, 1251), (31, 1, 1209), (19, 1, 1272), (18, 1, 1308), (16, 1, 1265)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 13, 15, 18, 19, 20, 22, 24, 26, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 1, 10, 1, 11, 1, 1, 12, 13, 14, 18, 15, 19, 16, 1, 17, 1, 1, 1]) (bs := [16, 2]) (W := 97364) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3517_3 : P.sumLeaves 24 3601856 64 = 97364 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56279) rows (by decide) (by decide)).symm.trans contract3517_3

theorem contract3517_4 : P.leaf 30 56280 = 10632 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 56280) (ss := [(5, 1, 524), (27, 0, 865), (11, 1, 872), (30, 1, 1251), (31, 1, 1251), (29, 1, 1258), (6, 0, 473), (10, 0, 459), (12, 0, 459), (23, 1, 810), (8, 1, 1266), (16, 1, 1272), (18, 1, 1265)]) (ids := [0, 1, 2, 5, 7, 11, 12, 13, 15, 17, 18, 19, 20, 22, 23, 24, 26]) (cs := [2, 3, 4, 1, 0, 5, 1, 6, 0, 1, 0, 7, 8, 9, 1, 10, 1, 11, 12, 13, 14, 1, 15, 16, 17, 0, 18, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3517_4 : P.sumLeaves 24 3601920 64 = 10632 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56280) rows (by decide) (by decide)).symm.trans contract3517_4

theorem c3517_5 : P.sumLeaves 24 3601984 448 = 802374 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3517) (lo := 576) (len := 448) (W := 802374) check rows elimOK (by decide) (by decide) cover3517 (by decide)
  decide +kernel

theorem h3517 : P.leaf 34 3517 = 923626 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 13256), (256, 0), (64, 97364), (64, 10632), (448, 802374)]) (.cons c3517_0 (.cons c3517_1 (.cons c3517_2 (.cons c3517_3 (.cons c3517_4 (.cons c3517_5 (.nil))))))) (by decide) (by decide))

theorem cover3518 : P.CoversSplit 24 10 3518 0xf0f5000000000000f0f5000000000000a0a0000000000000a0a0000000000000f0f0000000000000f000000000000000a0a0000000000000a000000000000000f0f5000000000000f0f500000000000000000000000000000000000000000000f0f0000000000000f00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 1209, 1210, 1251, 1308]) (by decide +kernel)

theorem c3518_0 : P.sumLeaves 24 3602432 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3518) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3518 (by decide)
  decide +kernel

theorem contract3518_1 : P.leaf 30 56290 = 43392 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 56290) (ss := [(2, 1, 466), (5, 3, 524), (3, 1, 529), (10, 1, 865), (29, 1, 865), (19, 1, 866), (18, 1, 867), (11, 1, 872), (30, 1, 1251), (28, 1, 858), (31, 1, 1251)]) (ids := [2, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 18, 19, 22, 23, 24, 25, 20, 21]) (cs := [1, 1, 2, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 1, 1, 13, 14, 19, 20, 15, 16, 17, 18, 1, 1, 1, 1]) (bs := [17, 2]) (W := 43392) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3518_1 : P.sumLeaves 24 3602560 64 = 43392 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 56290) rows (by decide) (by decide)).symm.trans contract3518_1

theorem c3518_2 : P.sumLeaves 24 3602624 832 = 6772396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3518) (lo := 192) (len := 832) (W := 6772396) check rows elimOK (by decide) (by decide) cover3518 (by decide)
  decide +kernel

theorem h3518 : P.leaf 34 3518 = 6815788 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 43392), (832, 6772396)]) (.cons c3518_0 (.cons c3518_1 (.cons c3518_2 (.nil)))) (by decide) (by decide))

theorem cover3519 : P.CoversSplit 24 10 3519 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000fff8000000000000ff00000000000000fff8000000000000ff00000000000000fffa000000000000fffa00000000000000000000000000000000000000000000fff8000000000000ff0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1209, 1210, 1251, 1258, 1308]) (by decide +kernel)

theorem c3519_0 : P.sumLeaves 24 3603456 823 = 10456675 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3519) (lo := 0) (len := 823) (W := 10456675) check rows elimOK (by decide) (by decide) cover3519 (by decide)
  decide +kernel

theorem c3519_1 : P.sumLeaves 24 3604279 201 = 18724408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3519) (lo := 823) (len := 201) (W := 18724408) check rows elimOK (by decide) (by decide) cover3519 (by decide)
  decide +kernel

theorem h3519 : P.leaf 34 3519 = 29181083 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(823, 10456675), (201, 18724408)]) (.cons c3519_0 (.cons c3519_1 (.nil))) (by decide) (by decide))

theorem cover3564 : P.CoversSplit 24 10 3564 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3564_0 : P.sumLeaves 24 3649536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3564) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3564 (by decide)
  decide +kernel

theorem h3564 : P.leaf 34 3564 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3564_0 (.nil)) (by decide) (by decide))

theorem cover3565 : P.CoversSplit 24 10 3565 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000220000001100000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 915, 1209, 1217, 1266, 1609]) (by decide +kernel)

theorem c3565_0 : P.sumLeaves 24 3650560 640 = 49656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3565) (lo := 0) (len := 640) (W := 49656) check rows elimOK (by decide) (by decide) cover3565 (by decide)
  decide +kernel

theorem contract3565_1 : P.leaf 30 57050 = 10840 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 57050) (ss := [(3, 1, 417), (30, 1, 417), (11, 1, 472), (27, 0, 522), (29, 0, 522), (2, 1, 410), (25, 1, 572), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273)]) (ids := [2, 3, 4, 5, 6, 7, 8, 10, 16, 17, 18, 19, 20, 21, 22, 24, 26, 29]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 9, 1, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 16, 1, 17, 0, 18, 0, 1, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3565_1 : P.sumLeaves 24 3651200 64 = 10840 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 57050) rows (by decide) (by decide)).symm.trans contract3565_1

theorem c3565_2 : P.sumLeaves 24 3651264 320 = 254840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3565) (lo := 704) (len := 320) (W := 254840) check rows elimOK (by decide) (by decide) cover3565 (by decide)
  decide +kernel

theorem h3565 : P.leaf 34 3565 = 315336 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 49656), (64, 10840), (320, 254840)]) (.cons c3565_0 (.cons c3565_1 (.cons c3565_2 (.nil)))) (by decide) (by decide))

theorem cover3566 : P.CoversSplit 24 10 3566 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c3566_0 : P.sumLeaves 24 3651584 1024 = 1218256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3566) (lo := 0) (len := 1024) (W := 1218256) check rows elimOK (by decide) (by decide) cover3566 (by decide)
  decide +kernel

theorem h3566 : P.leaf 34 3566 = 1218256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1218256)]) (.cons c3566_0 (.nil)) (by decide) (by decide))

theorem cover3567 : P.CoversSplit 24 10 3567 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 866, 915, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c3567_0 : P.sumLeaves 24 3652608 1024 = 3880317 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3567) (lo := 0) (len := 1024) (W := 3880317) check rows elimOK (by decide) (by decide) cover3567 (by decide)
  decide +kernel

theorem h3567 : P.leaf 34 3567 = 3880317 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3880317)]) (.cons c3567_0 (.nil)) (by decide) (by decide))

theorem cover3582 : P.CoversSplit 24 10 3582 0xf0f55555f0f50000f0f55555f0f50000f0f55555f0f50000f0f55555f0f50000f0f05550a0800000f0005500a0000000f0f05550a0800000f0005500a0000000f0f55555f0f50000f0f55555f0f50000f0f55555f0f00000f0f55555f0f00000f0f05550a0800000f0005500a0000000f0c05540a0800000f0005500a0000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1209, 1217, 1258, 1609]) (by decide +kernel)

theorem c3582_0 : P.sumLeaves 24 3667968 373 = 2535508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3582) (lo := 0) (len := 373) (W := 2535508) check rows elimOK (by decide) (by decide) cover3582 (by decide)
  decide +kernel

theorem c3582_1 : P.sumLeaves 24 3668341 327 = 7309890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3582) (lo := 373) (len := 327) (W := 7309890) check rows elimOK (by decide) (by decide) cover3582 (by decide)
  decide +kernel

theorem c3582_2 : P.sumLeaves 24 3668668 246 = 14480048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3582) (lo := 700) (len := 246) (W := 14480048) check rows elimOK (by decide) (by decide) cover3582 (by decide)
  decide +kernel

theorem c3582_3 : P.sumLeaves 24 3668914 78 = 14437963 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3582) (lo := 946) (len := 78) (W := 14437963) check rows elimOK (by decide) (by decide) cover3582 (by decide)
  decide +kernel

theorem h3582 : P.leaf 34 3582 = 38763409 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(373, 2535508), (327, 7309890), (246, 14480048), (78, 14437963)]) (.cons c3582_0 (.cons c3582_1 (.cons c3582_2 (.cons c3582_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3485, 24), (3486, 24), (3487, 24), (3492, 24), (3493, 24), (3494, 48), (3495, 48), (3496, 24), (3497, 24), (3498, 48), (3499, 48), (3500, 48), (3501, 48), (3502, 48), (3503, 48), (3510, 24), (3511, 24), (3514, 24), (3515, 24), (3516, 48), (3517, 48), (3518, 48), (3519, 48), (3564, 12), (3565, 12), (3566, 24), (3567, 24), (3582, 12)]

theorem segOK : checkSeg 16 perms 3485 3583 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3485 3583 924 3561406860 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3561406860)
    (SegSum.cons (w := 24) h3485 (SegSum.cons (w := 24) h3486 (SegSum.cons (w := 24) h3487 (SegSum.cons (w := 24) h3492 (SegSum.cons (w := 24) h3493 (SegSum.cons (w := 48) h3494 (SegSum.cons (w := 48) h3495 (SegSum.cons (w := 24) h3496 (SegSum.cons (w := 24) h3497 (SegSum.cons (w := 48) h3498 (SegSum.cons (w := 48) h3499 (SegSum.cons (w := 48) h3500 (SegSum.cons (w := 48) h3501 (SegSum.cons (w := 48) h3502 (SegSum.cons (w := 48) h3503 (SegSum.cons (w := 24) h3510 (SegSum.cons (w := 24) h3511 (SegSum.cons (w := 24) h3514 (SegSum.cons (w := 24) h3515 (SegSum.cons (w := 48) h3516 (SegSum.cons (w := 48) h3517 (SegSum.cons (w := 48) h3518 (SegSum.cons (w := 48) h3519 (SegSum.cons (w := 12) h3564 (SegSum.cons (w := 12) h3565 (SegSum.cons (w := 24) h3566 (SegSum.cons (w := 24) h3567 (SegSum.cons (w := 12) h3582 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S20
