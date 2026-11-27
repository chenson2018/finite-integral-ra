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

theorem c1435_0 : P.sumLeaves 24 1469440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1435) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1435 (by decide)
  decide +kernel

theorem h1435 : P.leaf 34 1435 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1435_0 (.nil)) (by decide) (by decide))

theorem cover1436 : P.CoversSplit 24 10 1436 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1436_0 : P.sumLeaves 24 1470464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1436) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1436 (by decide)
  decide +kernel

theorem h1436 : P.leaf 34 1436 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1436_0 (.nil)) (by decide) (by decide))

theorem cover1437 : P.CoversSplit 24 10 1437 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1437_0 : P.sumLeaves 24 1471488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1437) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1437 (by decide)
  decide +kernel

theorem h1437 : P.leaf 34 1437 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1437_0 (.nil)) (by decide) (by decide))

theorem cover1438 : P.CoversSplit 24 10 1438 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1438_0 : P.sumLeaves 24 1472512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1438) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1438 (by decide)
  decide +kernel

theorem h1438 : P.leaf 34 1438 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1438_0 (.nil)) (by decide) (by decide))

theorem cover1439 : P.CoversSplit 24 10 1439 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1439_0 : P.sumLeaves 24 1473536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1439) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1439 (by decide)
  decide +kernel

theorem h1439 : P.leaf 34 1439 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1439_0 (.nil)) (by decide) (by decide))

theorem cover1444 : P.CoversSplit 24 10 1444 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1444_0 : P.sumLeaves 24 1478656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1444) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1444 (by decide)
  decide +kernel

theorem h1444 : P.leaf 34 1444 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1444_0 (.nil)) (by decide) (by decide))

theorem cover1445 : P.CoversSplit 24 10 1445 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1445_0 : P.sumLeaves 24 1479680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1445) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1445 (by decide)
  decide +kernel

theorem h1445 : P.leaf 34 1445 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1445_0 (.nil)) (by decide) (by decide))

theorem h1446 : P.leaf 34 1446 = 1824 := by
  exact leaf_contract_factors (k := 34) (b := 19) (H := 1446) (ss := [(32, 1, 466), (33, 8, 468), (3, 1, 472), (16, 1, 486), (30, 19, 866), (35, 0, 867), (18, 1, 879), (11, 1, 901), (10, 1, 809), (12, 1, 901), (6, 1, 458), (19, 1, 908), (14, 1, 965), (9, 1, 510), (8, 1, 1266)]) (ids := [0, 2, 3, 5, 11, 13, 15, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 32, 21]) (cs := [2, 1, 3, 4, 1, 5, 1, 1, 1, 1, 1, 6, 1, 7, 1, 8, 1, 1, 9, 10, 11, 20, 12, 13, 14, 15, 16, 17, 1, 18, 1, 1, 19, 0]) (bs := [18, 1]) (W := 1824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1447 : P.CoversSplit 24 10 1447 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1447_0 : P.sumLeaves 24 1481728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1447) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1447 (by decide)
  decide +kernel

theorem h1447 : P.leaf 34 1447 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1447_0 (.nil)) (by decide) (by decide))

theorem cover1448 : P.CoversSplit 24 10 1448 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1448_0 : P.sumLeaves 24 1482752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1448) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1448 (by decide)
  decide +kernel

theorem h1448 : P.leaf 34 1448 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1448_0 (.nil)) (by decide) (by decide))

theorem cover1449 : P.CoversSplit 24 10 1449 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1449_0 : P.sumLeaves 24 1483776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1449) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1449 (by decide)
  decide +kernel

theorem h1449 : P.leaf 34 1449 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1449_0 (.nil)) (by decide) (by decide))

theorem cover1450 : P.CoversSplit 24 10 1450 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 860, 865, 867, 1202, 1258, 1266]) (by decide +kernel)

theorem c1450_0 : P.sumLeaves 24 1484800 1024 = 4032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1450) (lo := 0) (len := 1024) (W := 4032) check rows elimOK (by decide) (by decide) cover1450 (by decide)
  decide +kernel

theorem h1450 : P.leaf 34 1450 = 4032 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4032)]) (.cons c1450_0 (.nil)) (by decide) (by decide))

theorem cover1451 : P.CoversSplit 24 10 1451 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1451_0 : P.sumLeaves 24 1485824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1451) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1451 (by decide)
  decide +kernel

theorem h1451 : P.leaf 34 1451 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1451_0 (.nil)) (by decide) (by decide))

theorem cover1452 : P.CoversSplit 24 10 1452 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1452_0 : P.sumLeaves 24 1486848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1452) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1452 (by decide)
  decide +kernel

theorem h1452 : P.leaf 34 1452 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1452_0 (.nil)) (by decide) (by decide))

theorem cover1453 : P.CoversSplit 24 10 1453 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1453_0 : P.sumLeaves 24 1487872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1453) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1453 (by decide)
  decide +kernel

theorem h1453 : P.leaf 34 1453 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1453_0 (.nil)) (by decide) (by decide))

theorem cover1454 : P.CoversSplit 24 10 1454 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 860, 865, 867, 1202, 1258, 1266]) (by decide +kernel)

theorem c1454_0 : P.sumLeaves 24 1488896 1024 = 27868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1454) (lo := 0) (len := 1024) (W := 27868) check rows elimOK (by decide) (by decide) cover1454 (by decide)
  decide +kernel

theorem h1454 : P.leaf 34 1454 = 27868 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27868)]) (.cons c1454_0 (.nil)) (by decide) (by decide))

theorem cover1455 : P.CoversSplit 24 10 1455 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1455_0 : P.sumLeaves 24 1489920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1455) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1455 (by decide)
  decide +kernel

theorem h1455 : P.leaf 34 1455 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1455_0 (.nil)) (by decide) (by decide))

theorem cover1460 : P.CoversSplit 24 10 1460 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1460_0 : P.sumLeaves 24 1495040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1460) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1460 (by decide)
  decide +kernel

theorem h1460 : P.leaf 34 1460 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1460_0 (.nil)) (by decide) (by decide))

theorem cover1461 : P.CoversSplit 24 10 1461 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1461_0 : P.sumLeaves 24 1496064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1461) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1461 (by decide)
  decide +kernel

theorem h1461 : P.leaf 34 1461 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1461_0 (.nil)) (by decide) (by decide))

theorem cover1462 : P.CoversSplit 24 10 1462 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1462_0 : P.sumLeaves 24 1497088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1462) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1462 (by decide)
  decide +kernel

theorem h1462 : P.leaf 34 1462 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1462_0 (.nil)) (by decide) (by decide))

theorem cover1463 : P.CoversSplit 24 10 1463 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1463_0 : P.sumLeaves 24 1498112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1463) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1463 (by decide)
  decide +kernel

theorem h1463 : P.leaf 34 1463 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1463_0 (.nil)) (by decide) (by decide))

theorem cover1466 : P.CoversSplit 24 10 1466 0xf0f5000000000000f0f500000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 860, 865, 867, 916, 1202, 1251, 1258, 1308]) (by decide +kernel)

theorem c1466_0 : P.sumLeaves 24 1501184 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1466) (lo := 0) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1466 (by decide)
  decide +kernel

theorem contract1466_1 : P.leaf 30 23459 = 9776 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 23459) (ss := [(14, 1, 486), (2, 1, 487), (3, 1, 524), (19, 1, 866), (18, 1, 879), (11, 1, 901), (10, 1, 809), (16, 1, 468), (12, 1, 803), (29, 1, 916), (15, 1, 930), (30, 1, 1251), (28, 1, 858), (31, 1, 1202)]) (ids := [3, 4, 5, 6, 7, 11, 15, 18, 19, 20, 23, 24, 25, 2, 21, 22]) (cs := [1, 1, 15, 2, 3, 4, 5, 6, 1, 1, 1, 7, 1, 1, 1, 8, 1, 1, 9, 10, 11, 16, 17, 12, 13, 14, 1, 1, 1, 1]) (bs := [13, 3]) (W := 9776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1466_1 : P.sumLeaves 24 1501376 64 = 9776 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 23459) rows (by decide) (by decide)).symm.trans contract1466_1

theorem c1466_2 : P.sumLeaves 24 1501440 768 = 78096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1466) (lo := 256) (len := 768) (W := 78096) check rows elimOK (by decide) (by decide) cover1466 (by decide)
  decide +kernel

theorem h1466 : P.leaf 34 1466 = 87872 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 0), (64, 9776), (768, 78096)]) (.cons c1466_0 (.cons c1466_1 (.cons c1466_2 (.nil)))) (by decide) (by decide))

theorem cover1467 : P.CoversSplit 24 10 1467 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1467_0 : P.sumLeaves 24 1502208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1467) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1467 (by decide)
  decide +kernel

theorem h1467 : P.leaf 34 1467 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1467_0 (.nil)) (by decide) (by decide))

theorem cover1468 : P.CoversSplit 24 10 1468 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1468_0 : P.sumLeaves 24 1503232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1468) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1468 (by decide)
  decide +kernel

theorem h1468 : P.leaf 34 1468 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1468_0 (.nil)) (by decide) (by decide))

theorem cover1469 : P.CoversSplit 24 10 1469 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1469_0 : P.sumLeaves 24 1504256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1469) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1469 (by decide)
  decide +kernel

theorem h1469 : P.leaf 34 1469 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1469_0 (.nil)) (by decide) (by decide))

theorem cover1470 : P.CoversSplit 24 10 1470 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1470_0 : P.sumLeaves 24 1505280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1470) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1470 (by decide)
  decide +kernel

theorem h1470 : P.leaf 34 1470 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1470_0 (.nil)) (by decide) (by decide))

theorem cover1471 : P.CoversSplit 24 10 1471 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1471_0 : P.sumLeaves 24 1506304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1471) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1471 (by decide)
  decide +kernel

theorem h1471 : P.leaf 34 1471 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1471_0 (.nil)) (by decide) (by decide))

theorem cover1476 : P.CoversSplit 24 10 1476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1476_0 : P.sumLeaves 24 1511424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1476) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1476 (by decide)
  decide +kernel

theorem h1476 : P.leaf 34 1476 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1476_0 (.nil)) (by decide) (by decide))

theorem cover1477 : P.CoversSplit 24 10 1477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1477_0 : P.sumLeaves 24 1512448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1477) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1477 (by decide)
  decide +kernel

theorem h1477 : P.leaf 34 1477 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1477_0 (.nil)) (by decide) (by decide))

theorem cover1478 : P.CoversSplit 24 10 1478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1478_0 : P.sumLeaves 24 1513472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1478) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1478 (by decide)
  decide +kernel

theorem h1478 : P.leaf 34 1478 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1478_0 (.nil)) (by decide) (by decide))

theorem cover1479 : P.CoversSplit 24 10 1479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1479_0 : P.sumLeaves 24 1514496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1479) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1479 (by decide)
  decide +kernel

theorem h1479 : P.leaf 34 1479 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1479_0 (.nil)) (by decide) (by decide))

theorem cover1484 : P.CoversSplit 24 10 1484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1484_0 : P.sumLeaves 24 1519616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1484) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1484 (by decide)
  decide +kernel

theorem h1484 : P.leaf 34 1484 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1484_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1435, 48), (1436, 48), (1437, 48), (1438, 48), (1439, 48), (1444, 48), (1445, 48), (1446, 48), (1447, 48), (1448, 24), (1449, 24), (1450, 48), (1451, 48), (1452, 48), (1453, 48), (1454, 48), (1455, 48), (1460, 48), (1461, 48), (1462, 48), (1463, 48), (1466, 24), (1467, 24), (1468, 48), (1469, 48), (1470, 48), (1471, 48), (1476, 24), (1477, 24), (1478, 48), (1479, 48), (1484, 48)]

theorem segOK : checkSeg 16 perms 1435 1485 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1435 1485 1392 3727680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3727680)
    (SegSum.cons (w := 48) h1435 (SegSum.cons (w := 48) h1436 (SegSum.cons (w := 48) h1437 (SegSum.cons (w := 48) h1438 (SegSum.cons (w := 48) h1439 (SegSum.cons (w := 48) h1444 (SegSum.cons (w := 48) h1445 (SegSum.cons (w := 48) h1446 (SegSum.cons (w := 48) h1447 (SegSum.cons (w := 24) h1448 (SegSum.cons (w := 24) h1449 (SegSum.cons (w := 48) h1450 (SegSum.cons (w := 48) h1451 (SegSum.cons (w := 48) h1452 (SegSum.cons (w := 48) h1453 (SegSum.cons (w := 48) h1454 (SegSum.cons (w := 48) h1455 (SegSum.cons (w := 48) h1460 (SegSum.cons (w := 48) h1461 (SegSum.cons (w := 48) h1462 (SegSum.cons (w := 48) h1463 (SegSum.cons (w := 24) h1466 (SegSum.cons (w := 24) h1467 (SegSum.cons (w := 48) h1468 (SegSum.cons (w := 48) h1469 (SegSum.cons (w := 48) h1470 (SegSum.cons (w := 48) h1471 (SegSum.cons (w := 24) h1476 (SegSum.cons (w := 24) h1477 (SegSum.cons (w := 48) h1478 (SegSum.cons (w := 48) h1479 (SegSum.cons (w := 48) h1484 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S10
