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

namespace RACert.S4N1.C0.S27

open RACert RACert.Problem

theorem cover5457 : P.CoversSplit 24 10 5457 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5457 : P.leaf 34 5457 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5457) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5457) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5457 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5459 : P.CoversSplit 24 10 5459 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5459 : P.leaf 34 5459 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5459) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5459) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5459 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5460 : P.CoversSplit 24 10 5460 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 516, 572, 858, 860, 865, 867, 909, 1202, 1210, 1258, 1264]) (by decide +kernel)

theorem h5460 : P.leaf 34 5460 = 7120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5460) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5460) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover5460 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5461 : P.CoversSplit 24 10 5461 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 865, 909, 1202, 1210, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem h5461 : P.leaf 34 5461 = 215020 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5461) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5461) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5461 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5463 : P.CoversSplit 24 10 5463 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1251, 1258, 1264]) (by decide +kernel)

noncomputable def f5463 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5594112 + i)

theorem c5463_0 : rowSum f5463 0 1024 = 4684647 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5463) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5463 (by decide)
  decide +kernel

theorem sum5463 : rowSum f5463 0 1024 = 4684647 :=
  c5463_0

theorem h5463 : P.leaf 34 5463 = 4684647 :=
  leaf_weighted (k := 24) (d := 10) (H := 5463) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 5463) (by decide) (by decide +kernel)) sum5463

theorem cover5464 : P.CoversSplit 24 10 5464 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 516, 572, 858, 860, 865, 867, 909, 1202, 1209, 1210, 1258, 1259, 1264]) (by decide +kernel)

theorem h5464 : P.leaf 34 5464 = 40 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5464) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5464) (weight := fun _ => 1) (xs := [383]) check rows elimOK (by decide) (by decide) cover5464 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5465 : P.CoversSplit 24 10 5465 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5465 : P.leaf 34 5465 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5465) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5465) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5465 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5467 : P.CoversSplit 24 10 5467 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5467 : P.leaf 34 5467 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5467) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5467) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5467 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5468 : P.CoversSplit 24 10 5468 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 516, 572, 858, 860, 865, 867, 909, 1202, 1210, 1258, 1264]) (by decide +kernel)

theorem h5468 : P.leaf 34 5468 = 25168 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5468) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5468) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover5468 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5469 : P.CoversSplit 24 10 5469 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 865, 909, 1202, 1210, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem h5469 : P.leaf 34 5469 = 583224 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5469) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5469) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5469 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5471 : P.CoversSplit 24 10 5471 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1251, 1258, 1264]) (by decide +kernel)

noncomputable def f5471 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5602304 + i)

theorem c5471_0 : rowSum f5471 0 1024 = 6790475 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5471) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5471 (by decide)
  decide +kernel

theorem sum5471 : rowSum f5471 0 1024 = 6790475 :=
  c5471_0

theorem h5471 : P.leaf 34 5471 = 6790475 :=
  leaf_weighted (k := 24) (d := 10) (H := 5471) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 5471) (by decide) (by decide +kernel)) sum5471

theorem cover5472 : P.CoversSplit 24 10 5472 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h5472 : P.leaf 34 5472 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5472) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5472) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5472 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5473 : P.CoversSplit 24 10 5473 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5473 : P.leaf 34 5473 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5473) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5473) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5473 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5474 : P.CoversSplit 24 10 5474 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5474 : P.leaf 34 5474 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5474) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5474) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5474 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5475 : P.CoversSplit 24 10 5475 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5475 : P.leaf 34 5475 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5475) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5475) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5475 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5476 : P.CoversSplit 24 10 5476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h5476 : P.leaf 34 5476 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5476) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5476) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5476 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5477 : P.CoversSplit 24 10 5477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5477 : P.leaf 34 5477 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5477) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5477) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5477 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5478 : P.CoversSplit 24 10 5478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5478 : P.leaf 34 5478 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5478) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5478) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5478 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5479 : P.CoversSplit 24 10 5479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5479 : P.leaf 34 5479 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5479) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5479) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5479 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5480 : P.CoversSplit 24 10 5480 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h5480 : P.leaf 34 5480 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5480) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5480) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5480 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5481 : P.CoversSplit 24 10 5481 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5481 : P.leaf 34 5481 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5481) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5481) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5481 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5482 : P.CoversSplit 24 10 5482 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5482 : P.leaf 34 5482 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5482) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5482) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5482 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5483 : P.CoversSplit 24 10 5483 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5483 : P.leaf 34 5483 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5483) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5483) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5483 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5484 : P.CoversSplit 24 10 5484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h5484 : P.leaf 34 5484 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5484) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5484) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5484 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5485 : P.CoversSplit 24 10 5485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5485 : P.leaf 34 5485 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5485) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5485) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5485 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5486 : P.CoversSplit 24 10 5486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5486 : P.leaf 34 5486 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5486) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5486) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5486 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5487 : P.CoversSplit 24 10 5487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5487 : P.leaf 34 5487 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5487) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5487) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5487 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5488 : P.leaf 34 5488 = 0 := by
  exact leaf_contract_zero (ss := [(28, 2, 466), (2, 1, 465), (7, 6, 474), (6, 1, 480), (15, 1, 487), (14, 8, 558), (8, 1, 482), (35, 0, 867), (16, 10, 872), (33, 0, 909), (18, 11, 879), (32, 1, 1264), (27, 1, 572), (29, 1, 473), (34, 1, 572)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5489 : P.CoversSplit 24 10 5489 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5489 : P.leaf 34 5489 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5489) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5489) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5489 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5490 : P.CoversSplit 24 10 5490 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5490 : P.leaf 34 5490 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5490) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5490) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5490 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5491 : P.CoversSplit 24 10 5491 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h5491 : P.leaf 34 5491 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5491) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5491) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5491 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover18734 : P.CoversSplit 24 10 18734 0x8000000080000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 859, 865, 879, 915, 921, 1202]) (by decide +kernel)

theorem h18734 : P.leaf 34 18734 = 49920 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18734) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18734) (weight := fun _ => 1) (xs := [895, 991, 1023]) check rows elimOK (by decide) (by decide) cover18734 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5492 : P.leaf 34 5492 = 49920 :=
  orient4 (v := 18734) (by decide) (by decide +kernel) h18734

def seg : List (ℕ × ℕ) := [(5457, 48), (5459, 24), (5460, 24), (5461, 48), (5463, 24), (5464, 24), (5465, 48), (5467, 24), (5468, 24), (5469, 48), (5471, 24), (5472, 48), (5473, 48), (5474, 48), (5475, 48), (5476, 48), (5477, 48), (5478, 48), (5479, 48), (5480, 48), (5481, 48), (5482, 48), (5483, 48), (5484, 48), (5485, 48), (5486, 48), (5487, 48), (5488, 48), (5489, 48), (5490, 48), (5491, 48), (5492, 48)]

theorem segOK : checkSeg 16 perms 5457 5493 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5457 5493 1368 316890672 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 316890672)
    (SegSum.cons (w := 48) h5457 (SegSum.cons (w := 24) h5459 (SegSum.cons (w := 24) h5460 (SegSum.cons (w := 48) h5461 (SegSum.cons (w := 24) h5463 (SegSum.cons (w := 24) h5464 (SegSum.cons (w := 48) h5465 (SegSum.cons (w := 24) h5467 (SegSum.cons (w := 24) h5468 (SegSum.cons (w := 48) h5469 (SegSum.cons (w := 24) h5471 (SegSum.cons (w := 48) h5472 (SegSum.cons (w := 48) h5473 (SegSum.cons (w := 48) h5474 (SegSum.cons (w := 48) h5475 (SegSum.cons (w := 48) h5476 (SegSum.cons (w := 48) h5477 (SegSum.cons (w := 48) h5478 (SegSum.cons (w := 48) h5479 (SegSum.cons (w := 48) h5480 (SegSum.cons (w := 48) h5481 (SegSum.cons (w := 48) h5482 (SegSum.cons (w := 48) h5483 (SegSum.cons (w := 48) h5484 (SegSum.cons (w := 48) h5485 (SegSum.cons (w := 48) h5486 (SegSum.cons (w := 48) h5487 (SegSum.cons (w := 48) h5488 (SegSum.cons (w := 48) h5489 (SegSum.cons (w := 48) h5490 (SegSum.cons (w := 48) h5491 (SegSum.cons (w := 48) h5492 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S27
