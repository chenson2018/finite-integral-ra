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

namespace RACert.S4N1.C0.S41

open RACert RACert.Problem

theorem cover6500 : P.CoversSplit 24 10 6500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6500_0 : P.sumLeaves 24 6656000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6500) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6500 (by decide)
  decide +kernel

theorem h6500 : P.leaf 34 6500 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6500_0 (.nil)) (by decide) (by decide))

theorem cover6501 : P.CoversSplit 24 10 6501 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c6501_0 : P.sumLeaves 24 6657024 1024 = 42568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6501) (lo := 0) (len := 1024) (W := 42568) check rows elimOK (by decide) (by decide) cover6501 (by decide)
  decide +kernel

theorem h6501 : P.leaf 34 6501 = 42568 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42568)]) (.cons c6501_0 (.nil)) (by decide) (by decide))

theorem cover6502 : P.CoversSplit 24 10 6502 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6502_0 : P.sumLeaves 24 6658048 1024 = 150344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6502) (lo := 0) (len := 1024) (W := 150344) check rows elimOK (by decide) (by decide) cover6502 (by decide)
  decide +kernel

theorem h6502 : P.leaf 34 6502 = 150344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 150344)]) (.cons c6502_0 (.nil)) (by decide) (by decide))

theorem cover6503 : P.CoversSplit 24 10 6503 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c6503_0 : P.sumLeaves 24 6659072 1024 = 729952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6503) (lo := 0) (len := 1024) (W := 729952) check rows elimOK (by decide) (by decide) cover6503 (by decide)
  decide +kernel

theorem h6503 : P.leaf 34 6503 = 729952 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 729952)]) (.cons c6503_0 (.nil)) (by decide) (by decide))

theorem cover6504 : P.CoversSplit 24 10 6504 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6504_0 : P.sumLeaves 24 6660096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6504) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6504 (by decide)
  decide +kernel

theorem h6504 : P.leaf 34 6504 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6504_0 (.nil)) (by decide) (by decide))

theorem cover6505 : P.CoversSplit 24 10 6505 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c6505_0 : P.sumLeaves 24 6661120 1024 = 29814 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6505) (lo := 0) (len := 1024) (W := 29814) check rows elimOK (by decide) (by decide) cover6505 (by decide)
  decide +kernel

theorem h6505 : P.leaf 34 6505 = 29814 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 29814)]) (.cons c6505_0 (.nil)) (by decide) (by decide))

theorem cover6506 : P.CoversSplit 24 10 6506 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6506_0 : P.sumLeaves 24 6662144 1024 = 40888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6506) (lo := 0) (len := 1024) (W := 40888) check rows elimOK (by decide) (by decide) cover6506 (by decide)
  decide +kernel

theorem h6506 : P.leaf 34 6506 = 40888 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 40888)]) (.cons c6506_0 (.nil)) (by decide) (by decide))

theorem cover6507 : P.CoversSplit 24 10 6507 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c6507_0 : P.sumLeaves 24 6663168 1024 = 419724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6507) (lo := 0) (len := 1024) (W := 419724) check rows elimOK (by decide) (by decide) cover6507 (by decide)
  decide +kernel

theorem h6507 : P.leaf 34 6507 = 419724 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 419724)]) (.cons c6507_0 (.nil)) (by decide) (by decide))

theorem cover6508 : P.CoversSplit 24 10 6508 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6508_0 : P.sumLeaves 24 6664192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6508) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6508 (by decide)
  decide +kernel

theorem h6508 : P.leaf 34 6508 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6508_0 (.nil)) (by decide) (by decide))

theorem cover6509 : P.CoversSplit 24 10 6509 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c6509_0 : P.sumLeaves 24 6665216 1024 = 216196 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6509) (lo := 0) (len := 1024) (W := 216196) check rows elimOK (by decide) (by decide) cover6509 (by decide)
  decide +kernel

theorem h6509 : P.leaf 34 6509 = 216196 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 216196)]) (.cons c6509_0 (.nil)) (by decide) (by decide))

theorem cover6510 : P.CoversSplit 24 10 6510 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6510_0 : P.sumLeaves 24 6666240 1024 = 284434 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6510) (lo := 0) (len := 1024) (W := 284434) check rows elimOK (by decide) (by decide) cover6510 (by decide)
  decide +kernel

theorem h6510 : P.leaf 34 6510 = 284434 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 284434)]) (.cons c6510_0 (.nil)) (by decide) (by decide))

theorem cover6511 : P.CoversSplit 24 10 6511 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c6511_0 : P.sumLeaves 24 6667264 1024 = 1335620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6511) (lo := 0) (len := 1024) (W := 1335620) check rows elimOK (by decide) (by decide) cover6511 (by decide)
  decide +kernel

theorem h6511 : P.leaf 34 6511 = 1335620 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1335620)]) (.cons c6511_0 (.nil)) (by decide) (by decide))

theorem h6513 : P.leaf 34 6513 = 74016 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 6513) (ss := [(7, 6, 474), (6, 1, 478), (12, 1, 478), (11, 1, 459), (2, 1, 487), (8, 1, 558), (10, 1, 809), (32, 1, 866), (27, 1, 473), (29, 1, 473), (30, 1, 867), (33, 1, 879), (17, 1, 908), (34, 1, 1258)]) (ids := [1, 2, 3, 7, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22, 24, 26, 29, 33, 21, 23]) (cs := [1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 1, 6, 7, 8, 9, 1, 10, 11, 12, 13, 14, 20, 15, 21, 16, 1, 17, 1, 1, 18, 1, 1, 1, 19]) (bs := [18, 2]) (W := 74016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover6514 : P.CoversSplit 24 10 6514 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 859, 865, 866, 879, 909, 1202, 1258, 1259]) (by decide +kernel)

theorem c6514_0 : P.sumLeaves 24 6670336 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6514) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover6514 (by decide)
  decide +kernel

theorem contract6514_1 : P.leaf 30 104237 = 30200 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 104237) (ss := [(2, 1, 453), (5, 1, 453), (6, 1, 478), (12, 1, 460), (10, 1, 458), (11, 1, 809), (30, 18, 867), (18, 1, 909), (28, 1, 859), (31, 1, 859), (17, 1, 1308), (19, 1, 1273)]) (ids := [1, 2, 5, 6, 7, 11, 12, 13, 14, 18, 19, 20, 22, 23, 24, 25, 27, 21]) (cs := [1, 2, 3, 1, 1, 4, 5, 6, 1, 1, 1, 7, 8, 9, 10, 1, 1, 1, 11, 12, 13, 19, 14, 15, 16, 17, 1, 18, 1, 1]) (bs := [17, 1]) (W := 30200) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6514_1 : P.sumLeaves 24 6671168 64 = 30200 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 104237) rows (by decide) (by decide)).symm.trans contract6514_1

theorem c6514_2 : P.sumLeaves 24 6671232 128 = 127944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6514) (lo := 896) (len := 128) (W := 127944) check rows elimOK (by decide) (by decide) cover6514 (by decide)
  decide +kernel

theorem h6514 : P.leaf 34 6514 = 158144 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 30200), (128, 127944)]) (.cons c6514_0 (.cons c6514_1 (.cons c6514_2 (.nil)))) (by decide) (by decide))

theorem cover6515 : P.CoversSplit 24 10 6515 0xffff0000afaa00000000000000000000ffff0000afaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000afaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 859, 865, 866, 867, 908, 1202, 1209, 1217, 1258, 1259, 1308]) (by decide +kernel)

theorem c6515_0 : P.sumLeaves 24 6671360 1024 = 4025932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6515) (lo := 0) (len := 1024) (W := 4025932) check rows elimOK (by decide) (by decide) cover6515 (by decide)
  decide +kernel

theorem h6515 : P.leaf 34 6515 = 4025932 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4025932)]) (.cons c6515_0 (.nil)) (by decide) (by decide))

theorem cover6516 : P.CoversSplit 24 10 6516 0xc000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 858, 859, 865, 866, 879, 916, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem c6516_0 : P.sumLeaves 24 6672384 1024 = 52736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6516) (lo := 0) (len := 1024) (W := 52736) check rows elimOK (by decide) (by decide) cover6516 (by decide)
  decide +kernel

theorem h6516 : P.leaf 34 6516 = 52736 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 52736)]) (.cons c6516_0 (.nil)) (by decide) (by decide))

theorem cover6517 : P.CoversSplit 24 10 6517 0xcc00cc008c0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 865, 866, 879, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem c6517_0 : P.sumLeaves 24 6673408 1024 = 669472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6517) (lo := 0) (len := 1024) (W := 669472) check rows elimOK (by decide) (by decide) cover6517 (by decide)
  decide +kernel

theorem h6517 : P.leaf 34 6517 = 669472 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 669472)]) (.cons c6517_0 (.nil)) (by decide) (by decide))

theorem cover6518 : P.CoversSplit 24 10 6518 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 859, 865, 866, 879, 1202, 1258, 1259]) (by decide +kernel)

theorem c6518_0 : P.sumLeaves 24 6674432 1024 = 1513312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6518) (lo := 0) (len := 1024) (W := 1513312) check rows elimOK (by decide) (by decide) cover6518 (by decide)
  decide +kernel

theorem h6518 : P.leaf 34 6518 = 1513312 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1513312)]) (.cons c6518_0 (.nil)) (by decide) (by decide))

theorem cover6519 : P.CoversSplit 24 10 6519 0xffffffffafaaa0a00000000000000000ffffffffafaaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffafaaa0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 859, 865, 866, 908, 1202, 1209, 1217, 1258, 1259, 1308]) (by decide +kernel)

theorem c6519_0 : P.sumLeaves 24 6675456 977 = 5159274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6519) (lo := 0) (len := 977) (W := 5159274) check rows elimOK (by decide) (by decide) cover6519 (by decide)
  decide +kernel

theorem c6519_1 : P.sumLeaves 24 6676433 47 = 12947476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6519) (lo := 977) (len := 47) (W := 12947476) check rows elimOK (by decide) (by decide) cover6519 (by decide)
  decide +kernel

theorem h6519 : P.leaf 34 6519 = 18106750 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(977, 5159274), (47, 12947476)]) (.cons c6519_0 (.cons c6519_1 (.nil))) (by decide) (by decide))

theorem h6520 : P.leaf 34 6520 = 30400 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 6520) (ss := [(2, 1, 466), (28, 1, 508), (8, 1, 558), (30, 18, 867), (35, 33, 879), (17, 1, 908), (32, 1, 1264), (29, 1, 865), (34, 1, 1258), (27, 1, 473), (33, 1, 1308), (7, 1, 474), (18, 1, 909)]) (ids := [1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 24, 29, 23]) (cs := [1, 2, 3, 4, 5, 1, 1, 6, 7, 8, 9, 10, 11, 12, 13, 1, 1, 14, 15, 16, 17, 18, 19, 22, 20, 1, 1, 1, 1, 21, 1, 1, 1, 1]) (bs := [20, 1]) (W := 30400) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover6521 : P.CoversSplit 24 10 6521 0xcc0000008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc0000008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 865, 867, 879, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem c6521_0 : P.sumLeaves 24 6677504 1024 = 245772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6521) (lo := 0) (len := 1024) (W := 245772) check rows elimOK (by decide) (by decide) cover6521 (by decide)
  decide +kernel

theorem h6521 : P.leaf 34 6521 = 245772 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 245772)]) (.cons c6521_0 (.nil)) (by decide) (by decide))

theorem cover6522 : P.CoversSplit 24 10 6522 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 859, 865, 879, 909, 1202, 1258, 1259, 1264]) (by decide +kernel)

theorem c6522_0 : P.sumLeaves 24 6678528 1024 = 563730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6522) (lo := 0) (len := 1024) (W := 563730) check rows elimOK (by decide) (by decide) cover6522 (by decide)
  decide +kernel

theorem h6522 : P.leaf 34 6522 = 563730 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 563730)]) (.cons c6522_0 (.nil)) (by decide) (by decide))

theorem cover6523 : P.CoversSplit 24 10 6523 0xffff0000afaa00000000000000000000ffff0000afaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000afaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 867, 916, 1202, 1209, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c6523_0 : P.sumLeaves 24 6679552 1024 = 8470106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6523) (lo := 0) (len := 1024) (W := 8470106) check rows elimOK (by decide) (by decide) cover6523 (by decide)
  decide +kernel

theorem h6523 : P.leaf 34 6523 = 8470106 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8470106)]) (.cons c6523_0 (.nil)) (by decide) (by decide))

theorem cover6524 : P.CoversSplit 24 10 6524 0xc000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 858, 859, 865, 879, 916, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem c6524_0 : P.sumLeaves 24 6680576 1024 = 271340 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6524) (lo := 0) (len := 1024) (W := 271340) check rows elimOK (by decide) (by decide) cover6524 (by decide)
  decide +kernel

theorem h6524 : P.leaf 34 6524 = 271340 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 271340)]) (.cons c6524_0 (.nil)) (by decide) (by decide))

theorem cover6525 : P.CoversSplit 24 10 6525 0xcc00cc008c0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 865, 879, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem c6525_0 : P.sumLeaves 24 6681600 1024 = 2200460 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6525) (lo := 0) (len := 1024) (W := 2200460) check rows elimOK (by decide) (by decide) cover6525 (by decide)
  decide +kernel

theorem h6525 : P.leaf 34 6525 = 2200460 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2200460)]) (.cons c6525_0 (.nil)) (by decide) (by decide))

theorem cover6526 : P.CoversSplit 24 10 6526 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 859, 865, 879, 1202, 1258, 1259, 1264]) (by decide +kernel)

theorem c6526_0 : P.sumLeaves 24 6682624 1024 = 3347258 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6526) (lo := 0) (len := 1024) (W := 3347258) check rows elimOK (by decide) (by decide) cover6526 (by decide)
  decide +kernel

theorem h6526 : P.leaf 34 6526 = 3347258 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3347258)]) (.cons c6526_0 (.nil)) (by decide) (by decide))

theorem cover6527 : P.CoversSplit 24 10 6527 0xffffffffafaaa0a00000000000000000ffffffffafaaa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffafaaa0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 1202, 1209, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c6527_0 : P.sumLeaves 24 6683648 977 = 13669322 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6527) (lo := 0) (len := 977) (W := 13669322) check rows elimOK (by decide) (by decide) cover6527 (by decide)
  decide +kernel

theorem c6527_1 : P.sumLeaves 24 6684625 47 = 31072498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6527) (lo := 977) (len := 47) (W := 31072498) check rows elimOK (by decide) (by decide) cover6527 (by decide)
  decide +kernel

theorem h6527 : P.leaf 34 6527 = 44741820 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(977, 13669322), (47, 31072498)]) (.cons c6527_0 (.cons c6527_1 (.nil))) (by decide) (by decide))

theorem cover6624 : P.CoversSplit 24 10 6624 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6624_0 : P.sumLeaves 24 6782976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6624) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6624 (by decide)
  decide +kernel

theorem h6624 : P.leaf 34 6624 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6624_0 (.nil)) (by decide) (by decide))

theorem cover6625 : P.CoversSplit 24 10 6625 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 879, 916, 1209, 1258]) (by decide +kernel)

theorem c6625_0 : P.sumLeaves 24 6784000 1024 = 42024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6625) (lo := 0) (len := 1024) (W := 42024) check rows elimOK (by decide) (by decide) cover6625 (by decide)
  decide +kernel

theorem h6625 : P.leaf 34 6625 = 42024 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42024)]) (.cons c6625_0 (.nil)) (by decide) (by decide))

theorem cover6627 : P.CoversSplit 24 10 6627 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 859, 865, 866, 1209, 1217, 1258, 1266]) (by decide +kernel)

noncomputable def f6627 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6786048 + i)

theorem c6627_0 : rowSum f6627 0 1024 = 816324 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6627) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6627 (by decide)
  decide +kernel

theorem sum6627 : rowSum f6627 0 1024 = 816324 :=
  c6627_0

theorem h6627 : P.leaf 34 6627 = 816324 :=
  leaf_weighted (k := 24) (d := 10) (H := 6627) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6627) (by decide) (by decide +kernel)) sum6627

theorem cover6628 : P.CoversSplit 24 10 6628 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6628_0 : P.sumLeaves 24 6787072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6628) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6628 (by decide)
  decide +kernel

theorem h6628 : P.leaf 34 6628 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6628_0 (.nil)) (by decide) (by decide))

theorem cover6629 : P.CoversSplit 24 10 6629 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 879, 916, 1209, 1258]) (by decide +kernel)

theorem c6629_0 : P.sumLeaves 24 6788096 1024 = 143184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6629) (lo := 0) (len := 1024) (W := 143184) check rows elimOK (by decide) (by decide) cover6629 (by decide)
  decide +kernel

theorem h6629 : P.leaf 34 6629 = 143184 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 143184)]) (.cons c6629_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6500, 48), (6501, 48), (6502, 48), (6503, 48), (6504, 48), (6505, 48), (6506, 48), (6507, 48), (6508, 48), (6509, 48), (6510, 48), (6511, 48), (6513, 24), (6514, 48), (6515, 48), (6516, 48), (6517, 48), (6518, 48), (6519, 48), (6520, 48), (6521, 48), (6522, 48), (6523, 48), (6524, 48), (6525, 48), (6526, 48), (6527, 48), (6624, 24), (6625, 48), (6627, 24), (6628, 48), (6629, 48)]

theorem segOK : checkSeg 16 perms 6500 6630 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6500 6630 1464 4237303200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4237303200)
    (SegSum.cons (w := 48) h6500 (SegSum.cons (w := 48) h6501 (SegSum.cons (w := 48) h6502 (SegSum.cons (w := 48) h6503 (SegSum.cons (w := 48) h6504 (SegSum.cons (w := 48) h6505 (SegSum.cons (w := 48) h6506 (SegSum.cons (w := 48) h6507 (SegSum.cons (w := 48) h6508 (SegSum.cons (w := 48) h6509 (SegSum.cons (w := 48) h6510 (SegSum.cons (w := 48) h6511 (SegSum.cons (w := 24) h6513 (SegSum.cons (w := 48) h6514 (SegSum.cons (w := 48) h6515 (SegSum.cons (w := 48) h6516 (SegSum.cons (w := 48) h6517 (SegSum.cons (w := 48) h6518 (SegSum.cons (w := 48) h6519 (SegSum.cons (w := 48) h6520 (SegSum.cons (w := 48) h6521 (SegSum.cons (w := 48) h6522 (SegSum.cons (w := 48) h6523 (SegSum.cons (w := 48) h6524 (SegSum.cons (w := 48) h6525 (SegSum.cons (w := 48) h6526 (SegSum.cons (w := 48) h6527 (SegSum.cons (w := 24) h6624 (SegSum.cons (w := 48) h6625 (SegSum.cons (w := 24) h6627 (SegSum.cons (w := 48) h6628 (SegSum.cons (w := 48) h6629 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S41
