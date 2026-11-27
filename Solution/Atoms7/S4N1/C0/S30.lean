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

namespace RACert.S4N1.C0.S30

open RACert RACert.Problem

theorem cover5459 : P.CoversSplit 24 10 5459 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5459_0 : P.sumLeaves 24 5590016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5459) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5459 (by decide)
  decide +kernel

theorem h5459 : P.leaf 34 5459 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5459_0 (.nil)) (by decide) (by decide))

theorem h5460 : P.leaf 34 5460 = 7120 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 5460) (ss := [(28, 2, 466), (29, 2, 472), (35, 1, 867), (5, 1, 523), (2, 1, 409), (3, 1, 409), (4, 1, 410), (16, 1, 872), (33, 1, 909), (18, 1, 879), (30, 1, 1251), (31, 1, 1251), (26, 1, 465), (32, 1, 1264), (34, 1, 1258), (27, 1, 473)]) (ids := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 23]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 12, 1, 13, 14, 15, 16, 17, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [16, 2]) (W := 7120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5461 : P.CoversSplit 24 10 5461 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 865, 909, 1202, 1210, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem c5461_0 : P.sumLeaves 24 5592064 1024 = 215020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5461) (lo := 0) (len := 1024) (W := 215020) check rows elimOK (by decide) (by decide) cover5461 (by decide)
  decide +kernel

theorem h5461 : P.leaf 34 5461 = 215020 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 215020)]) (.cons c5461_0 (.nil)) (by decide) (by decide))

theorem cover5463 : P.CoversSplit 24 10 5463 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1251, 1258, 1264]) (by decide +kernel)

noncomputable def f5463 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5594112 + i)

theorem c5463_0 : rowSum f5463 0 1024 = 4684647 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5463) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5463 (by decide)
  decide +kernel

theorem sum5463 : rowSum f5463 0 1024 = 4684647 :=
  c5463_0

theorem h5463 : P.leaf 34 5463 = 4684647 :=
  leaf_weighted (k := 24) (d := 10) (H := 5463) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5463) (by decide) (by decide +kernel)) sum5463

theorem h5464 : P.leaf 34 5464 = 40 := by
  exact leaf_contract_factors (k := 34) (b := 8) (H := 5464) (ss := [(28, 2, 466), (29, 2, 472), (14, 8, 509), (35, 0, 867), (7, 6, 474), (15, 2, 487), (34, 5, 523), (16, 10, 872), (33, 0, 909), (31, 5, 565), (18, 11, 879), (5, 1, 1251), (2, 1, 465), (26, 1, 465), (27, 1, 473), (30, 1, 858), (32, 1, 865), (8, 0, 1266), (3, 1, 418), (4, 1, 425), (20, 1, 482), (21, 0, 488), (12, 1, 608), (9, 1, 678), (17, 1, 1364), (19, 1, 1707)]) (ids := [4, 8, 9, 11, 20, 21, 22, 23]) (cs := [1, 1, 1, 1, 2, 2, 0, 1, 3, 4, 1, 5, 0, 1, 3, 1, 4, 1, 1, 0, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0]) (bs := [6, 2]) (W := 40) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5465 : P.CoversSplit 24 10 5465 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5465_0 : P.sumLeaves 24 5596160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5465) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5465 (by decide)
  decide +kernel

theorem h5465 : P.leaf 34 5465 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5465_0 (.nil)) (by decide) (by decide))

theorem cover5467 : P.CoversSplit 24 10 5467 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5467_0 : P.sumLeaves 24 5598208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5467) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5467 (by decide)
  decide +kernel

theorem h5467 : P.leaf 34 5467 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5467_0 (.nil)) (by decide) (by decide))

theorem h5468 : P.leaf 34 5468 = 25168 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 5468) (ss := [(28, 2, 466), (29, 2, 472), (35, 1, 867), (5, 1, 523), (16, 1, 872), (33, 1, 909), (18, 1, 879), (30, 1, 1251), (31, 1, 1251), (2, 1, 465), (26, 1, 465), (32, 1, 1264), (34, 1, 1258), (27, 1, 473)]) (ids := [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 22, 23]) (cs := [1, 2, 3, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 1, 14, 1, 15, 16, 17, 18, 19, 20, 21, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 2]) (W := 25168) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5469 : P.CoversSplit 24 10 5469 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 865, 909, 1202, 1210, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem c5469_0 : P.sumLeaves 24 5600256 1024 = 583224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5469) (lo := 0) (len := 1024) (W := 583224) check rows elimOK (by decide) (by decide) cover5469 (by decide)
  decide +kernel

theorem h5469 : P.leaf 34 5469 = 583224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 583224)]) (.cons c5469_0 (.nil)) (by decide) (by decide))

theorem cover5471 : P.CoversSplit 24 10 5471 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1251, 1258, 1264]) (by decide +kernel)

noncomputable def f5471 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5602304 + i)

theorem c5471_0 : rowSum f5471 0 1024 = 6790475 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5471) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5471 (by decide)
  decide +kernel

theorem sum5471 : rowSum f5471 0 1024 = 6790475 :=
  c5471_0

theorem h5471 : P.leaf 34 5471 = 6790475 :=
  leaf_weighted (k := 24) (d := 10) (H := 5471) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5471) (by decide) (by decide +kernel)) sum5471

theorem cover5472 : P.CoversSplit 24 10 5472 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c5472_0 : P.sumLeaves 24 5603328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5472) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5472 (by decide)
  decide +kernel

theorem h5472 : P.leaf 34 5472 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5472_0 (.nil)) (by decide) (by decide))

theorem cover5473 : P.CoversSplit 24 10 5473 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5473_0 : P.sumLeaves 24 5604352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5473) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5473 (by decide)
  decide +kernel

theorem h5473 : P.leaf 34 5473 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5473_0 (.nil)) (by decide) (by decide))

theorem cover5474 : P.CoversSplit 24 10 5474 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5474_0 : P.sumLeaves 24 5605376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5474) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5474 (by decide)
  decide +kernel

theorem h5474 : P.leaf 34 5474 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5474_0 (.nil)) (by decide) (by decide))

theorem cover5475 : P.CoversSplit 24 10 5475 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5475_0 : P.sumLeaves 24 5606400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5475) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5475 (by decide)
  decide +kernel

theorem h5475 : P.leaf 34 5475 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5475_0 (.nil)) (by decide) (by decide))

theorem cover5476 : P.CoversSplit 24 10 5476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c5476_0 : P.sumLeaves 24 5607424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5476) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5476 (by decide)
  decide +kernel

theorem h5476 : P.leaf 34 5476 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5476_0 (.nil)) (by decide) (by decide))

theorem cover5477 : P.CoversSplit 24 10 5477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5477_0 : P.sumLeaves 24 5608448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5477) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5477 (by decide)
  decide +kernel

theorem h5477 : P.leaf 34 5477 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5477_0 (.nil)) (by decide) (by decide))

theorem cover5478 : P.CoversSplit 24 10 5478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5478_0 : P.sumLeaves 24 5609472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5478) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5478 (by decide)
  decide +kernel

theorem h5478 : P.leaf 34 5478 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5478_0 (.nil)) (by decide) (by decide))

theorem cover5479 : P.CoversSplit 24 10 5479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5479_0 : P.sumLeaves 24 5610496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5479) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5479 (by decide)
  decide +kernel

theorem h5479 : P.leaf 34 5479 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5479_0 (.nil)) (by decide) (by decide))

theorem cover5480 : P.CoversSplit 24 10 5480 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c5480_0 : P.sumLeaves 24 5611520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5480) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5480 (by decide)
  decide +kernel

theorem h5480 : P.leaf 34 5480 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5480_0 (.nil)) (by decide) (by decide))

theorem cover5481 : P.CoversSplit 24 10 5481 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5481_0 : P.sumLeaves 24 5612544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5481) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5481 (by decide)
  decide +kernel

theorem h5481 : P.leaf 34 5481 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5481_0 (.nil)) (by decide) (by decide))

theorem cover5482 : P.CoversSplit 24 10 5482 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5482_0 : P.sumLeaves 24 5613568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5482) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5482 (by decide)
  decide +kernel

theorem h5482 : P.leaf 34 5482 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5482_0 (.nil)) (by decide) (by decide))

theorem cover5483 : P.CoversSplit 24 10 5483 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5483_0 : P.sumLeaves 24 5614592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5483) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5483 (by decide)
  decide +kernel

theorem h5483 : P.leaf 34 5483 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5483_0 (.nil)) (by decide) (by decide))

theorem cover5484 : P.CoversSplit 24 10 5484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c5484_0 : P.sumLeaves 24 5615616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5484) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5484 (by decide)
  decide +kernel

theorem h5484 : P.leaf 34 5484 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5484_0 (.nil)) (by decide) (by decide))

theorem cover5485 : P.CoversSplit 24 10 5485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5485_0 : P.sumLeaves 24 5616640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5485) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5485 (by decide)
  decide +kernel

theorem h5485 : P.leaf 34 5485 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5485_0 (.nil)) (by decide) (by decide))

theorem cover5486 : P.CoversSplit 24 10 5486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5486_0 : P.sumLeaves 24 5617664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5486) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5486 (by decide)
  decide +kernel

theorem h5486 : P.leaf 34 5486 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5486_0 (.nil)) (by decide) (by decide))

theorem cover5487 : P.CoversSplit 24 10 5487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5487_0 : P.sumLeaves 24 5618688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5487) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5487 (by decide)
  decide +kernel

theorem h5487 : P.leaf 34 5487 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5487_0 (.nil)) (by decide) (by decide))

theorem h5488 : P.leaf 34 5488 = 0 := by
  exact leaf_contract_zero (ss := [(28, 2, 466), (2, 1, 465), (7, 6, 474), (6, 1, 480), (15, 1, 487), (14, 8, 558), (8, 1, 482), (35, 0, 867), (16, 10, 872), (33, 0, 909), (18, 11, 879), (32, 1, 1264), (27, 1, 572), (29, 1, 473), (34, 1, 572)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5489 : P.CoversSplit 24 10 5489 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5489_0 : P.sumLeaves 24 5620736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5489) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5489 (by decide)
  decide +kernel

theorem h5489 : P.leaf 34 5489 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5489_0 (.nil)) (by decide) (by decide))

theorem cover5490 : P.CoversSplit 24 10 5490 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5490_0 : P.sumLeaves 24 5621760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5490) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5490 (by decide)
  decide +kernel

theorem h5490 : P.leaf 34 5490 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5490_0 (.nil)) (by decide) (by decide))

theorem cover5491 : P.CoversSplit 24 10 5491 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c5491_0 : P.sumLeaves 24 5622784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5491) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5491 (by decide)
  decide +kernel

theorem h5491 : P.leaf 34 5491 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5491_0 (.nil)) (by decide) (by decide))

theorem cover5492 : P.CoversSplit 24 10 5492 0xc000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 860, 865, 867, 909, 916, 1202, 1209, 1258, 1264]) (by decide +kernel)

theorem c5492_0 : P.sumLeaves 24 5623808 1024 = 49920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5492) (lo := 0) (len := 1024) (W := 49920) check rows elimOK (by decide) (by decide) cover5492 (by decide)
  decide +kernel

theorem h5492 : P.leaf 34 5492 = 49920 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49920)]) (.cons c5492_0 (.nil)) (by decide) (by decide))

theorem cover5493 : P.CoversSplit 24 10 5493 0xcc00cc00880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 860, 865, 909, 1202, 1209, 1258, 1259, 1264]) (by decide +kernel)

theorem c5493_0 : P.sumLeaves 24 5624832 1024 = 838544 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5493) (lo := 0) (len := 1024) (W := 838544) check rows elimOK (by decide) (by decide) cover5493 (by decide)
  decide +kernel

theorem h5493 : P.leaf 34 5493 = 838544 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 838544)]) (.cons c5493_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5459, 24), (5460, 24), (5461, 48), (5463, 24), (5464, 24), (5465, 48), (5467, 24), (5468, 24), (5469, 48), (5471, 24), (5472, 48), (5473, 48), (5474, 48), (5475, 48), (5476, 48), (5477, 48), (5478, 48), (5479, 48), (5480, 48), (5481, 48), (5482, 48), (5483, 48), (5484, 48), (5485, 48), (5486, 48), (5487, 48), (5488, 48), (5489, 48), (5490, 48), (5491, 48), (5492, 48), (5493, 48)]

theorem segOK : checkSeg 16 perms 5459 5494 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5459 5494 1368 357140784 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 357140784)
    (SegSum.cons (w := 24) h5459 (SegSum.cons (w := 24) h5460 (SegSum.cons (w := 48) h5461 (SegSum.cons (w := 24) h5463 (SegSum.cons (w := 24) h5464 (SegSum.cons (w := 48) h5465 (SegSum.cons (w := 24) h5467 (SegSum.cons (w := 24) h5468 (SegSum.cons (w := 48) h5469 (SegSum.cons (w := 24) h5471 (SegSum.cons (w := 48) h5472 (SegSum.cons (w := 48) h5473 (SegSum.cons (w := 48) h5474 (SegSum.cons (w := 48) h5475 (SegSum.cons (w := 48) h5476 (SegSum.cons (w := 48) h5477 (SegSum.cons (w := 48) h5478 (SegSum.cons (w := 48) h5479 (SegSum.cons (w := 48) h5480 (SegSum.cons (w := 48) h5481 (SegSum.cons (w := 48) h5482 (SegSum.cons (w := 48) h5483 (SegSum.cons (w := 48) h5484 (SegSum.cons (w := 48) h5485 (SegSum.cons (w := 48) h5486 (SegSum.cons (w := 48) h5487 (SegSum.cons (w := 48) h5488 (SegSum.cons (w := 48) h5489 (SegSum.cons (w := 48) h5490 (SegSum.cons (w := 48) h5491 (SegSum.cons (w := 48) h5492 (SegSum.cons (w := 48) h5493 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S30
