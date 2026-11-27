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

namespace RACert.S4N1.C0.S40

open RACert RACert.Problem

theorem cover6391 : P.CoversSplit 24 10 6391 0xffffffffafaa00000000000000000000ffffffffafaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 859, 865, 866, 879, 1202, 1209, 1210, 1259]) (by decide +kernel)

theorem c6391_0 : P.sumLeaves 24 6544384 1024 = 8969224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6391) (lo := 0) (len := 1024) (W := 8969224) check rows elimOK (by decide) (by decide) cover6391 (by decide)
  decide +kernel

theorem h6391 : P.leaf 34 6391 = 8969224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8969224)]) (.cons c6391_0 (.nil)) (by decide) (by decide))

theorem cover6392 : P.CoversSplit 24 10 6392 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 487, 858, 859, 865, 879, 909, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c6392_0 : P.sumLeaves 24 6545408 1024 = 87768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6392) (lo := 0) (len := 1024) (W := 87768) check rows elimOK (by decide) (by decide) cover6392 (by decide)
  decide +kernel

theorem h6392 : P.leaf 34 6392 = 87768 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 87768)]) (.cons c6392_0 (.nil)) (by decide) (by decide))

theorem cover6393 : P.CoversSplit 24 10 6393 0xff000000af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 487, 858, 865, 879, 909, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6393_0 : P.sumLeaves 24 6546432 1024 = 793910 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6393) (lo := 0) (len := 1024) (W := 793910) check rows elimOK (by decide) (by decide) cover6393 (by decide)
  decide +kernel

theorem h6393 : P.leaf 34 6393 = 793910 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 793910)]) (.cons c6393_0 (.nil)) (by decide) (by decide))

theorem cover6394 : P.CoversSplit 24 10 6394 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 487, 573, 858, 859, 865, 879, 909, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c6394_0 : P.sumLeaves 24 6547456 1024 = 889110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6394) (lo := 0) (len := 1024) (W := 889110) check rows elimOK (by decide) (by decide) cover6394 (by decide)
  decide +kernel

theorem h6394 : P.leaf 34 6394 = 889110 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 889110)]) (.cons c6394_0 (.nil)) (by decide) (by decide))

theorem cover6395 : P.CoversSplit 24 10 6395 0xffff0000afaa00000000000000000000ffff0000afaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 573, 858, 865, 879, 909, 916, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6395_0 : P.sumLeaves 24 6548480 1024 = 7402392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6395) (lo := 0) (len := 1024) (W := 7402392) check rows elimOK (by decide) (by decide) cover6395 (by decide)
  decide +kernel

theorem h6395 : P.leaf 34 6395 = 7402392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7402392)]) (.cons c6395_0 (.nil)) (by decide) (by decide))

theorem cover6396 : P.CoversSplit 24 10 6396 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 859, 865, 879, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c6396_0 : P.sumLeaves 24 6549504 1024 = 289850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6396) (lo := 0) (len := 1024) (W := 289850) check rows elimOK (by decide) (by decide) cover6396 (by decide)
  decide +kernel

theorem h6396 : P.leaf 34 6396 = 289850 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 289850)]) (.cons c6396_0 (.nil)) (by decide) (by decide))

theorem cover6397 : P.CoversSplit 24 10 6397 0xff00ff00af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 865, 879, 1202, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c6397_0 : P.sumLeaves 24 6550528 1024 = 1388372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6397) (lo := 0) (len := 1024) (W := 1388372) check rows elimOK (by decide) (by decide) cover6397 (by decide)
  decide +kernel

theorem h6397 : P.leaf 34 6397 = 1388372 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1388372)]) (.cons c6397_0 (.nil)) (by decide) (by decide))

theorem cover6398 : P.CoversSplit 24 10 6398 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 859, 865, 879, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c6398_0 : P.sumLeaves 24 6551552 1024 = 2941200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6398) (lo := 0) (len := 1024) (W := 2941200) check rows elimOK (by decide) (by decide) cover6398 (by decide)
  decide +kernel

theorem h6398 : P.leaf 34 6398 = 2941200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2941200)]) (.cons c6398_0 (.nil)) (by decide) (by decide))

theorem cover6399 : P.CoversSplit 24 10 6399 0xffffffffafaa00000000000000000000ffffffffafaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 865, 879, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6399_0 : P.sumLeaves 24 6552576 1024 = 24646665 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6399) (lo := 0) (len := 1024) (W := 24646665) check rows elimOK (by decide) (by decide) cover6399 (by decide)
  decide +kernel

theorem h6399 : P.leaf 34 6399 = 24646665 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24646665)]) (.cons c6399_0 (.nil)) (by decide) (by decide))

theorem cover6432 : P.CoversSplit 24 10 6432 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6432_0 : P.sumLeaves 24 6586368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6432) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6432 (by decide)
  decide +kernel

theorem h6432 : P.leaf 34 6432 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6432_0 (.nil)) (by decide) (by decide))

theorem cover6433 : P.CoversSplit 24 10 6433 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 524, 529, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem c6433_0 : P.sumLeaves 24 6587392 1024 = 1360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6433) (lo := 0) (len := 1024) (W := 1360) check rows elimOK (by decide) (by decide) cover6433 (by decide)
  decide +kernel

theorem h6433 : P.leaf 34 6433 = 1360 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1360)]) (.cons c6433_0 (.nil)) (by decide) (by decide))

theorem cover6435 : P.CoversSplit 24 10 6435 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 523, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

noncomputable def f6435 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6589440 + i)

theorem c6435_0 : rowSum f6435 0 1024 = 88300 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6435) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6435 (by decide)
  decide +kernel

theorem sum6435 : rowSum f6435 0 1024 = 88300 :=
  c6435_0

theorem h6435 : P.leaf 34 6435 = 88300 :=
  leaf_weighted (k := 24) (d := 10) (H := 6435) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6435) (by decide) (by decide +kernel)) sum6435

theorem cover6436 : P.CoversSplit 24 10 6436 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6436_0 : P.sumLeaves 24 6590464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6436) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6436 (by decide)
  decide +kernel

theorem h6436 : P.leaf 34 6436 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6436_0 (.nil)) (by decide) (by decide))

theorem cover6437 : P.CoversSplit 24 10 6437 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 524, 529, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem c6437_0 : P.sumLeaves 24 6591488 1024 = 10432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6437) (lo := 0) (len := 1024) (W := 10432) check rows elimOK (by decide) (by decide) cover6437 (by decide)
  decide +kernel

theorem h6437 : P.leaf 34 6437 = 10432 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10432)]) (.cons c6437_0 (.nil)) (by decide) (by decide))

theorem cover6438 : P.CoversSplit 24 10 6438 0x8000000000000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 517, 522, 529, 565, 858, 865, 1209, 1258, 1259]) (by decide +kernel)

theorem c6438_0 : P.sumLeaves 24 6592512 1024 = 10978 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6438) (lo := 0) (len := 1024) (W := 10978) check rows elimOK (by decide) (by decide) cover6438 (by decide)
  decide +kernel

theorem h6438 : P.leaf 34 6438 = 10978 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10978)]) (.cons c6438_0 (.nil)) (by decide) (by decide))

theorem cover6439 : P.CoversSplit 24 10 6439 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 523, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c6439_0 : P.sumLeaves 24 6593536 1024 = 264758 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6439) (lo := 0) (len := 1024) (W := 264758) check rows elimOK (by decide) (by decide) cover6439 (by decide)
  decide +kernel

theorem h6439 : P.leaf 34 6439 = 264758 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 264758)]) (.cons c6439_0 (.nil)) (by decide) (by decide))

theorem cover6444 : P.CoversSplit 24 10 6444 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6444_0 : P.sumLeaves 24 6598656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6444) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6444 (by decide)
  decide +kernel

theorem h6444 : P.leaf 34 6444 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6444_0 (.nil)) (by decide) (by decide))

theorem cover6445 : P.CoversSplit 24 10 6445 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 524, 529, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem c6445_0 : P.sumLeaves 24 6599680 1024 = 78780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6445) (lo := 0) (len := 1024) (W := 78780) check rows elimOK (by decide) (by decide) cover6445 (by decide)
  decide +kernel

theorem h6445 : P.leaf 34 6445 = 78780 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 78780)]) (.cons c6445_0 (.nil)) (by decide) (by decide))

theorem cover6447 : P.CoversSplit 24 10 6447 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 523, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

noncomputable def f6447 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6601728 + i)

theorem c6447_0 : rowSum f6447 0 1024 = 671819 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6447) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6447 (by decide)
  decide +kernel

theorem sum6447 : rowSum f6447 0 1024 = 671819 :=
  c6447_0

theorem h6447 : P.leaf 34 6447 = 671819 :=
  leaf_weighted (k := 24) (d := 10) (H := 6447) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6447) (by decide) (by decide +kernel)) sum6447

theorem h6449 : P.leaf 34 6449 = 21120 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 6449) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 474), (6, 1, 478), (12, 1, 461), (11, 1, 459), (8, 1, 558), (10, 1, 809), (32, 1, 866), (27, 1, 473), (29, 1, 473), (30, 1, 867), (33, 1, 879), (17, 1, 908), (31, 1, 1251), (34, 1, 1258)]) (ids := [1, 2, 7, 11, 12, 13, 14, 16, 17, 18, 19, 20, 22, 24, 26, 33, 21, 23]) (cs := [1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 18, 14, 19, 15, 1, 16, 1, 1, 1, 1, 1, 1, 17]) (bs := [16, 2]) (W := 21120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover6451 : P.CoversSplit 24 10 6451 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 859, 865, 866, 867, 908, 1202, 1209, 1210, 1258]) (by decide +kernel)

noncomputable def f6451 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6605824 + i)

theorem c6451_0 : rowSum f6451 0 1024 = 1523532 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6451) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6451 (by decide)
  decide +kernel

theorem sum6451 : rowSum f6451 0 1024 = 1523532 :=
  c6451_0

theorem h6451 : P.leaf 34 6451 = 1523532 :=
  leaf_weighted (k := 24) (d := 10) (H := 6451) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6451) (by decide) (by decide +kernel)) sum6451

theorem h6452 : P.leaf 34 6452 = 9080 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 6452) (ss := [(2, 1, 466), (29, 28, 508), (8, 1, 510), (18, 1, 867), (35, 33, 879), (32, 17, 908), (30, 1, 1251), (31, 1, 1251), (26, 1, 465), (28, 1, 465), (17, 1, 1258), (34, 1, 1258), (27, 1, 473)]) (ids := [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 23, 31, 22]) (cs := [1, 2, 3, 4, 5, 6, 1, 7, 8, 9, 10, 11, 12, 13, 14, 1, 1, 15, 16, 17, 18, 19, 22, 20, 1, 1, 1, 1, 1, 1, 1, 21, 1, 21]) (bs := [20, 1]) (W := 9080) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover6453 : P.CoversSplit 24 10 6453 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 865, 866, 879, 1202, 1209, 1210, 1251, 1258, 1259]) (by decide +kernel)

theorem c6453_0 : P.sumLeaves 24 6607872 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6453) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover6453 (by decide)
  decide +kernel

theorem contract6453_1 : P.leaf 30 103255 = 17392 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 103255) (ss := [(27, 1, 473), (29, 1, 473), (2, 1, 475), (6, 1, 480), (10, 1, 809), (11, 1, 459), (17, 1, 908), (30, 1, 1251), (31, 1, 1209), (19, 1, 1273), (18, 1, 1308), (16, 1, 1265)]) (ids := [1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 18, 19, 20, 22, 23, 24, 26, 21]) (cs := [1, 2, 3, 4, 1, 5, 6, 7, 1, 1, 8, 9, 10, 11, 1, 1, 1, 1, 12, 13, 14, 19, 15, 16, 17, 1, 18, 1, 1, 1]) (bs := [17, 1]) (W := 17392) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6453_1 : P.sumLeaves 24 6608320 64 = 17392 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 103255) rows (by decide) (by decide)).symm.trans contract6453_1

theorem c6453_2 : P.sumLeaves 24 6608384 512 = 147600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6453) (lo := 512) (len := 512) (W := 147600) check rows elimOK (by decide) (by decide) cover6453 (by decide)
  decide +kernel

theorem h6453 : P.leaf 34 6453 = 164992 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 17392), (512, 147600)]) (.cons c6453_0 (.cons c6453_1 (.cons c6453_2 (.nil)))) (by decide) (by decide))

theorem cover6454 : P.CoversSplit 24 10 6454 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 858, 865, 866, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c6454_0 : P.sumLeaves 24 6608896 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6454) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover6454 (by decide)
  decide +kernel

theorem contract6454_1 : P.leaf 30 103277 = 17480 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 103277) (ss := [(9, 6, 468), (2, 1, 479), (8, 1, 510), (16, 1, 531), (18, 1, 867), (11, 1, 909), (10, 1, 809), (30, 1, 1251), (26, 1, 465), (28, 1, 465), (31, 1, 517), (17, 1, 1308), (19, 1, 1273)]) (ids := [1, 2, 3, 4, 5, 10, 11, 12, 13, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 4, 5, 6, 1, 5, 1, 1, 7, 8, 9, 10, 1, 1, 1, 1, 11, 12, 13, 17, 18, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 17480) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6454_1 : P.sumLeaves 24 6609728 64 = 17480 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 103277) rows (by decide) (by decide)).symm.trans contract6454_1

theorem c6454_2 : P.sumLeaves 24 6609792 128 = 121196 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6454) (lo := 896) (len := 128) (W := 121196) check rows elimOK (by decide) (by decide) cover6454 (by decide)
  decide +kernel

theorem h6454 : P.leaf 34 6454 = 138676 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 17480), (128, 121196)]) (.cons c6454_0 (.cons c6454_1 (.cons c6454_2 (.nil)))) (by decide) (by decide))

theorem cover6455 : P.CoversSplit 24 10 6455 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 859, 865, 866, 908, 1202, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem c6455_0 : P.sumLeaves 24 6609920 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6455) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover6455 (by decide)
  decide +kernel

theorem contract6455_1 : P.leaf 30 103285 = 106908 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 103285) (ss := [(10, 1, 866), (11, 1, 909), (30, 1, 1251), (31, 1, 1209), (8, 1, 1266), (14, 1, 880), (16, 1, 531), (17, 1, 880), (18, 1, 1265), (19, 1, 1273)]) (ids := [0, 1, 2, 3, 4, 5, 7, 10, 11, 13, 18, 19, 20, 21, 24, 25, 26, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 1, 1, 9, 10, 1, 11, 1, 1, 1, 1, 12, 13, 14, 15, 20, 21, 16, 17, 18, 19, 1, 1]) (bs := [18, 2]) (W := 106908) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6455_1 : P.sumLeaves 24 6610240 64 = 106908 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 103285) rows (by decide) (by decide)).symm.trans contract6455_1

theorem c6455_2 : P.sumLeaves 24 6610304 640 = 3840140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6455) (lo := 384) (len := 640) (W := 3840140) check rows elimOK (by decide) (by decide) cover6455 (by decide)
  decide +kernel

theorem h6455 : P.leaf 34 6455 = 3947048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 106908), (640, 3840140)]) (.cons c6455_0 (.cons c6455_1 (.cons c6455_2 (.nil)))) (by decide) (by decide))

theorem h6460 : P.leaf 34 6460 = 109448 := by
  exact leaf_contract_factors (k := 34) (b := 22) (H := 6460) (ss := [(2, 1, 466), (29, 28, 508), (18, 1, 867), (35, 33, 879), (17, 1, 908), (30, 1, 1251), (31, 1, 1251), (26, 1, 465), (28, 1, 465), (32, 1, 1258), (34, 1, 1258), (27, 1, 473)]) (ids := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 31, 22, 23]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1, 1, 16, 17, 18, 19, 20, 22, 23, 1, 1, 1, 1, 1, 1, 1, 21, 1, 21]) (bs := [20, 2]) (W := 109448) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover6461 : P.CoversSplit 24 10 6461 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 865, 879, 1202, 1209, 1210, 1251, 1258, 1259]) (by decide +kernel)

theorem c6461_0 : P.sumLeaves 24 6616064 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6461) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover6461 (by decide)
  decide +kernel

theorem contract6461_1 : P.leaf 30 103383 = 104272 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 103383) (ss := [(27, 1, 473), (29, 1, 473), (10, 1, 866), (17, 1, 908), (30, 1, 1251), (11, 1, 809), (31, 1, 1209), (19, 1, 1273), (18, 1, 1308), (16, 1, 1265)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 18, 19, 20, 22, 24, 26, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 10, 11, 12, 13, 1, 1, 1, 1, 14, 15, 16, 20, 17, 21, 18, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 104272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6461_1 : P.sumLeaves 24 6616512 64 = 104272 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 103383) rows (by decide) (by decide)).symm.trans contract6461_1

theorem c6461_2 : P.sumLeaves 24 6616576 512 = 842248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6461) (lo := 512) (len := 512) (W := 842248) check rows elimOK (by decide) (by decide) cover6461 (by decide)
  decide +kernel

theorem h6461 : P.leaf 34 6461 = 946520 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 104272), (512, 842248)]) (.cons c6461_0 (.cons c6461_1 (.cons c6461_2 (.nil)))) (by decide) (by decide))

theorem cover6463 : P.CoversSplit 24 10 6463 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 865, 1202, 1209, 1210, 1251, 1258, 1264]) (by decide +kernel)

noncomputable def f6463 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6618112 + i)

theorem c6463_0 : rowSum f6463 0 1024 = 10226272 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6463) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6463 (by decide)
  decide +kernel

theorem sum6463 : rowSum f6463 0 1024 = 10226272 :=
  c6463_0

theorem h6463 : P.leaf 34 6463 = 10226272 :=
  leaf_weighted (k := 24) (d := 10) (H := 6463) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6463) (by decide) (by decide +kernel)) sum6463

theorem cover6496 : P.CoversSplit 24 10 6496 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6496_0 : P.sumLeaves 24 6651904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6496) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6496 (by decide)
  decide +kernel

theorem h6496 : P.leaf 34 6496 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6496_0 (.nil)) (by decide) (by decide))

theorem cover6497 : P.CoversSplit 24 10 6497 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c6497_0 : P.sumLeaves 24 6652928 1024 = 4700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6497) (lo := 0) (len := 1024) (W := 4700) check rows elimOK (by decide) (by decide) cover6497 (by decide)
  decide +kernel

theorem h6497 : P.leaf 34 6497 = 4700 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4700)]) (.cons c6497_0 (.nil)) (by decide) (by decide))

theorem cover6498 : P.CoversSplit 24 10 6498 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6498_0 : P.sumLeaves 24 6653952 1024 = 7680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6498) (lo := 0) (len := 1024) (W := 7680) check rows elimOK (by decide) (by decide) cover6498 (by decide)
  decide +kernel

theorem h6498 : P.leaf 34 6498 = 7680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7680)]) (.cons c6498_0 (.nil)) (by decide) (by decide))

theorem cover6499 : P.CoversSplit 24 10 6499 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c6499_0 : P.sumLeaves 24 6654976 1024 = 220029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6499) (lo := 0) (len := 1024) (W := 220029) check rows elimOK (by decide) (by decide) cover6499 (by decide)
  decide +kernel

theorem h6499 : P.leaf 34 6499 = 220029 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 220029)]) (.cons c6499_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6391, 48), (6392, 48), (6393, 48), (6394, 48), (6395, 48), (6396, 48), (6397, 48), (6398, 48), (6399, 48), (6432, 6), (6433, 24), (6435, 12), (6436, 24), (6437, 24), (6438, 24), (6439, 24), (6444, 12), (6445, 24), (6447, 12), (6449, 24), (6451, 24), (6452, 48), (6453, 48), (6454, 48), (6455, 48), (6460, 24), (6461, 48), (6463, 24), (6496, 24), (6497, 48), (6498, 48), (6499, 48)]

theorem segOK : checkSeg 16 perms 6391 6500 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6391 6500 1122 2839708116 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2839708116)
    (SegSum.cons (w := 48) h6391 (SegSum.cons (w := 48) h6392 (SegSum.cons (w := 48) h6393 (SegSum.cons (w := 48) h6394 (SegSum.cons (w := 48) h6395 (SegSum.cons (w := 48) h6396 (SegSum.cons (w := 48) h6397 (SegSum.cons (w := 48) h6398 (SegSum.cons (w := 48) h6399 (SegSum.cons (w := 6) h6432 (SegSum.cons (w := 24) h6433 (SegSum.cons (w := 12) h6435 (SegSum.cons (w := 24) h6436 (SegSum.cons (w := 24) h6437 (SegSum.cons (w := 24) h6438 (SegSum.cons (w := 24) h6439 (SegSum.cons (w := 12) h6444 (SegSum.cons (w := 24) h6445 (SegSum.cons (w := 12) h6447 (SegSum.cons (w := 24) h6449 (SegSum.cons (w := 24) h6451 (SegSum.cons (w := 48) h6452 (SegSum.cons (w := 48) h6453 (SegSum.cons (w := 48) h6454 (SegSum.cons (w := 48) h6455 (SegSum.cons (w := 24) h6460 (SegSum.cons (w := 48) h6461 (SegSum.cons (w := 24) h6463 (SegSum.cons (w := 24) h6496 (SegSum.cons (w := 48) h6497 (SegSum.cons (w := 48) h6498 (SegSum.cons (w := 48) h6499 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S40
