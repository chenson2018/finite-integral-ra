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

namespace RACert.S4N1.C0.S10

open RACert RACert.Problem

theorem cover1435 : P.CoversSplit 24 10 1435 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1435 : P.leaf 34 1435 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1435) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1435) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1435 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1436 : P.CoversSplit 24 10 1436 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1436 : P.leaf 34 1436 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1436) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1436) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1436 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1437 : P.CoversSplit 24 10 1437 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1437 : P.leaf 34 1437 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1437) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1437) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1437 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1438 : P.CoversSplit 24 10 1438 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1438 : P.leaf 34 1438 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1438) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1438) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1438 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1439 : P.CoversSplit 24 10 1439 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1439 : P.leaf 34 1439 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1439) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1439) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1439 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1444 : P.CoversSplit 24 10 1444 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1444 : P.leaf 34 1444 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1444) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1444) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1444 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1445 : P.CoversSplit 24 10 1445 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1445 : P.leaf 34 1445 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1445) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1445) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1445 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1446 : P.CoversSplit 24 10 1446 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 860, 865, 867, 1202, 1258, 1266]) (by decide +kernel)

theorem h1446 : P.leaf 34 1446 = 1824 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1446) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1446) (weight := fun _ => 1) (xs := [511]) check rows elimOK (by decide) (by decide) cover1446 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1447 : P.CoversSplit 24 10 1447 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1447 : P.leaf 34 1447 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1447) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1447) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1447 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1448 : P.CoversSplit 24 10 1448 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1448 : P.leaf 34 1448 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1448) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1448) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1448 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1449 : P.CoversSplit 24 10 1449 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1449 : P.leaf 34 1449 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1449) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1449) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1449 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1450 : P.CoversSplit 24 10 1450 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 860, 865, 867, 1202, 1258, 1266]) (by decide +kernel)

theorem h1450 : P.leaf 34 1450 = 4032 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1450) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1450) (weight := fun _ => 1) (xs := [511]) check rows elimOK (by decide) (by decide) cover1450 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1451 : P.CoversSplit 24 10 1451 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1451 : P.leaf 34 1451 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1451) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1451) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1451 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1452 : P.CoversSplit 24 10 1452 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1452 : P.leaf 34 1452 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1452) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1452) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1452 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1453 : P.CoversSplit 24 10 1453 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1453 : P.leaf 34 1453 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1453) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1453) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1453 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1454 : P.CoversSplit 24 10 1454 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 860, 865, 867, 1202, 1258, 1266]) (by decide +kernel)

theorem h1454 : P.leaf 34 1454 = 27868 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1454) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1454) (weight := fun _ => 1) (xs := [511]) check rows elimOK (by decide) (by decide) cover1454 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1455 : P.CoversSplit 24 10 1455 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1455 : P.leaf 34 1455 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1455) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1455) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1455 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1460 : P.CoversSplit 24 10 1460 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1460 : P.leaf 34 1460 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1460) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1460) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1460 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1461 : P.CoversSplit 24 10 1461 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1461 : P.leaf 34 1461 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1461) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1461) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1461 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1462 : P.CoversSplit 24 10 1462 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1462 : P.leaf 34 1462 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1462) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1462) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1462 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1463 : P.CoversSplit 24 10 1463 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1463 : P.leaf 34 1463 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1463) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1463) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1463 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16591 : P.CoversSplit 24 10 16591 0xf000500000000000300010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 858, 859, 860, 865, 871, 916, 921]) (ps := [(14, [958], [867])]) (by decide +kernel)

theorem h16591 : P.leaf 34 16591 = 87872 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16591) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16591) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16591) (weight := rowWeight keep1 twice1) (xs := [940, 956, 957, 1004, 1006, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover16591 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1466 : P.leaf 34 1466 = 87872 :=
  orient24 (v := 16591) (by decide) (by decide +kernel) h16591

theorem cover1467 : P.CoversSplit 24 10 1467 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1467 : P.leaf 34 1467 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1467) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1467) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1467 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1468 : P.CoversSplit 24 10 1468 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1468 : P.leaf 34 1468 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1468) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1468) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1468 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1469 : P.CoversSplit 24 10 1469 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1469 : P.leaf 34 1469 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1469) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1469) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1469 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1470 : P.CoversSplit 24 10 1470 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1470 : P.leaf 34 1470 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1470) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1470) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1470 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1471 : P.CoversSplit 24 10 1471 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1471 : P.leaf 34 1471 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1471) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1471) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1471 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1476 : P.CoversSplit 24 10 1476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1476 : P.leaf 34 1476 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1476) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1476) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1476 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1477 : P.CoversSplit 24 10 1477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1477 : P.leaf 34 1477 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1477) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1477) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1477 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1478 : P.CoversSplit 24 10 1478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1478 : P.leaf 34 1478 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1478) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1478) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1478 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1479 : P.CoversSplit 24 10 1479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h1479 : P.leaf 34 1479 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1479) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1479) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1479 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1484 : P.CoversSplit 24 10 1484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1484 : P.leaf 34 1484 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1484) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1484) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1484 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1435, 48), (1436, 48), (1437, 48), (1438, 48), (1439, 48), (1444, 48), (1445, 48), (1446, 48), (1447, 48), (1448, 24), (1449, 24), (1450, 48), (1451, 48), (1452, 48), (1453, 48), (1454, 48), (1455, 48), (1460, 48), (1461, 48), (1462, 48), (1463, 48), (1466, 24), (1467, 24), (1468, 48), (1469, 48), (1470, 48), (1471, 48), (1476, 24), (1477, 24), (1478, 48), (1479, 48), (1484, 48)]

theorem segOK : checkSeg 16 perms 1435 1485 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1435 1485 1392 3727680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3727680)
    (SegSum.cons (w := 48) h1435 (SegSum.cons (w := 48) h1436 (SegSum.cons (w := 48) h1437 (SegSum.cons (w := 48) h1438 (SegSum.cons (w := 48) h1439 (SegSum.cons (w := 48) h1444 (SegSum.cons (w := 48) h1445 (SegSum.cons (w := 48) h1446 (SegSum.cons (w := 48) h1447 (SegSum.cons (w := 24) h1448 (SegSum.cons (w := 24) h1449 (SegSum.cons (w := 48) h1450 (SegSum.cons (w := 48) h1451 (SegSum.cons (w := 48) h1452 (SegSum.cons (w := 48) h1453 (SegSum.cons (w := 48) h1454 (SegSum.cons (w := 48) h1455 (SegSum.cons (w := 48) h1460 (SegSum.cons (w := 48) h1461 (SegSum.cons (w := 48) h1462 (SegSum.cons (w := 48) h1463 (SegSum.cons (w := 24) h1466 (SegSum.cons (w := 24) h1467 (SegSum.cons (w := 48) h1468 (SegSum.cons (w := 48) h1469 (SegSum.cons (w := 48) h1470 (SegSum.cons (w := 48) h1471 (SegSum.cons (w := 24) h1476 (SegSum.cons (w := 24) h1477 (SegSum.cons (w := 48) h1478 (SegSum.cons (w := 48) h1479 (SegSum.cons (w := 48) h1484 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S10
