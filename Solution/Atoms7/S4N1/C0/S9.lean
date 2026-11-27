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

namespace RACert.S4N1.C0.S9

open RACert RACert.Problem

theorem cover1273 : P.CoversSplit 24 10 1273 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1273_0 : P.sumLeaves 24 1303552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1273) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1273 (by decide)
  decide +kernel

theorem h1273 : P.leaf 34 1273 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1273_0 (.nil)) (by decide) (by decide))

theorem cover1274 : P.CoversSplit 24 10 1274 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1274_0 : P.sumLeaves 24 1304576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1274) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1274 (by decide)
  decide +kernel

theorem h1274 : P.leaf 34 1274 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1274_0 (.nil)) (by decide) (by decide))

theorem cover1275 : P.CoversSplit 24 10 1275 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1275_0 : P.sumLeaves 24 1305600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1275) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1275 (by decide)
  decide +kernel

theorem h1275 : P.leaf 34 1275 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1275_0 (.nil)) (by decide) (by decide))

theorem cover1276 : P.CoversSplit 24 10 1276 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1276_0 : P.sumLeaves 24 1306624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1276) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1276 (by decide)
  decide +kernel

theorem h1276 : P.leaf 34 1276 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1276_0 (.nil)) (by decide) (by decide))

theorem cover1277 : P.CoversSplit 24 10 1277 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1277_0 : P.sumLeaves 24 1307648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1277) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1277 (by decide)
  decide +kernel

theorem h1277 : P.leaf 34 1277 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1277_0 (.nil)) (by decide) (by decide))

theorem cover1278 : P.CoversSplit 24 10 1278 0xf0005500a00000000000000000000000f0005500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 921, 1202, 1259]) (by decide +kernel)

theorem c1278_0 : P.sumLeaves 24 1308672 1024 = 728844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1278) (lo := 0) (len := 1024) (W := 728844) check rows elimOK (by decide) (by decide) cover1278 (by decide)
  decide +kernel

theorem h1278 : P.leaf 34 1278 = 728844 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 728844)]) (.cons c1278_0 (.nil)) (by decide) (by decide))

theorem cover1279 : P.CoversSplit 24 10 1279 0xff00fa00aa0000000000000000000000ff00fa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 867, 916, 921, 1202, 1210, 1259]) (by decide +kernel)

theorem c1279_0 : P.sumLeaves 24 1309696 1024 = 7018820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1279) (lo := 0) (len := 1024) (W := 7018820) check rows elimOK (by decide) (by decide) cover1279 (by decide)
  decide +kernel

theorem h1279 : P.leaf 34 1279 = 7018820 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7018820)]) (.cons c1279_0 (.nil)) (by decide) (by decide))

theorem cover1408 : P.CoversSplit 24 10 1408 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1408_0 : P.sumLeaves 24 1441792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1408) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1408 (by decide)
  decide +kernel

theorem h1408 : P.leaf 34 1408 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1408_0 (.nil)) (by decide) (by decide))

theorem cover1409 : P.CoversSplit 24 10 1409 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1409_0 : P.sumLeaves 24 1442816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1409) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1409 (by decide)
  decide +kernel

theorem h1409 : P.leaf 34 1409 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1409_0 (.nil)) (by decide) (by decide))

theorem cover1410 : P.CoversSplit 24 10 1410 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 858, 860, 865, 867, 916, 1258, 1259, 1301]) (by decide +kernel)

theorem c1410_0 : P.sumLeaves 24 1443840 1024 = 80 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1410) (lo := 0) (len := 1024) (W := 80) check rows elimOK (by decide) (by decide) cover1410 (by decide)
  decide +kernel

theorem h1410 : P.leaf 34 1410 = 80 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 80)]) (.cons c1410_0 (.nil)) (by decide) (by decide))

theorem cover1411 : P.CoversSplit 24 10 1411 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1411_0 : P.sumLeaves 24 1444864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1411) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1411 (by decide)
  decide +kernel

theorem h1411 : P.leaf 34 1411 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1411_0 (.nil)) (by decide) (by decide))

theorem cover1412 : P.CoversSplit 24 10 1412 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1412_0 : P.sumLeaves 24 1445888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1412) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1412 (by decide)
  decide +kernel

theorem h1412 : P.leaf 34 1412 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1412_0 (.nil)) (by decide) (by decide))

theorem cover1413 : P.CoversSplit 24 10 1413 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1413_0 : P.sumLeaves 24 1446912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1413) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1413 (by decide)
  decide +kernel

theorem h1413 : P.leaf 34 1413 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1413_0 (.nil)) (by decide) (by decide))

theorem h1414 : P.leaf 34 1414 = 256 := by
  exact leaf_contract_factors (k := 34) (b := 8) (H := 1414) (ss := [(32, 1, 466), (33, 8, 468), (3, 1, 472), (16, 1, 486), (26, 9, 510), (8, 1, 537), (9, 1, 479), (27, 1, 522), (28, 1, 858), (2, 1, 409), (5, 1, 418), (30, 1, 515), (4, 1, 417), (31, 1, 516), (29, 1, 865), (19, 1, 866), (35, 0, 867), (18, 11, 879), (11, 1, 901), (10, 1, 809), (6, 1, 458), (12, 1, 817), (13, 1, 922), (14, 1, 929), (34, 1, 1258), (17, 1, 1273)]) (ids := [5, 13, 18, 19, 20, 21, 22, 23]) (cs := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]) (bs := [0, 8]) (W := 256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1415 : P.CoversSplit 24 10 1415 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1415_0 : P.sumLeaves 24 1448960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1415) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1415 (by decide)
  decide +kernel

theorem h1415 : P.leaf 34 1415 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1415_0 (.nil)) (by decide) (by decide))

theorem cover1416 : P.CoversSplit 24 10 1416 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1416_0 : P.sumLeaves 24 1449984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1416) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1416 (by decide)
  decide +kernel

theorem h1416 : P.leaf 34 1416 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1416_0 (.nil)) (by decide) (by decide))

theorem cover1417 : P.CoversSplit 24 10 1417 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1417_0 : P.sumLeaves 24 1451008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1417) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1417 (by decide)
  decide +kernel

theorem h1417 : P.leaf 34 1417 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1417_0 (.nil)) (by decide) (by decide))

theorem h1418 : P.leaf 34 1418 = 0 := by
  exact leaf_contract_zero (ss := [(32, 1, 466), (3, 1, 472), (33, 0, 486), (7, 6, 467), (8, 0, 509), (16, 10, 468), (10, 1, 529)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1419 : P.CoversSplit 24 10 1419 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1419_0 : P.sumLeaves 24 1453056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1419) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1419 (by decide)
  decide +kernel

theorem h1419 : P.leaf 34 1419 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1419_0 (.nil)) (by decide) (by decide))

theorem cover1420 : P.CoversSplit 24 10 1420 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1420_0 : P.sumLeaves 24 1454080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1420) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1420 (by decide)
  decide +kernel

theorem h1420 : P.leaf 34 1420 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1420_0 (.nil)) (by decide) (by decide))

theorem cover1421 : P.CoversSplit 24 10 1421 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1421_0 : P.sumLeaves 24 1455104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1421) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1421 (by decide)
  decide +kernel

theorem h1421 : P.leaf 34 1421 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1421_0 (.nil)) (by decide) (by decide))

theorem cover1422 : P.CoversSplit 24 10 1422 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 858, 860, 865, 867, 916, 1258, 1259, 1301]) (by decide +kernel)

theorem c1422_0 : P.sumLeaves 24 1456128 1024 = 3632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1422) (lo := 0) (len := 1024) (W := 3632) check rows elimOK (by decide) (by decide) cover1422 (by decide)
  decide +kernel

theorem h1422 : P.leaf 34 1422 = 3632 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3632)]) (.cons c1422_0 (.nil)) (by decide) (by decide))

theorem cover1423 : P.CoversSplit 24 10 1423 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1423_0 : P.sumLeaves 24 1457152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1423) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1423 (by decide)
  decide +kernel

theorem h1423 : P.leaf 34 1423 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1423_0 (.nil)) (by decide) (by decide))

theorem cover1426 : P.CoversSplit 24 10 1426 0xa0a0555500000000a0a0555500000000a0a0555500000000a0a0555500000000a0005500000000000000000000000000a0005400000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 858, 860, 865, 867, 916, 1202, 1258, 1301]) (ps := [(14, [1609], [860])]) (by decide +kernel)

theorem c1426_0 : P.sumLeaves 24 1460224 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1426) (lo := 0) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1426 (by decide)
  decide +kernel

theorem contract1426_1 : P.leaf 30 22817 = 192 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 22817) (ss := [(7, 6, 467), (8, 0, 468), (26, 6, 479), (2, 1, 480), (9, 6, 510), (3, 1, 523), (30, 19, 866), (18, 11, 879), (19, 11, 908), (12, 1, 916), (29, 1, 916), (31, 1, 1258), (14, 1, 1609), (5, 1, 580), (28, 1, 860), (16, 1, 1315), (20, 1, 1314), (21, 1, 1315)]) (ids := [2, 4, 8, 9, 11, 13, 15, 20, 21, 23, 25, 22]) (cs := [1, 1, 2, 1, 3, 3, 0, 3, 4, 5, 1, 6, 1, 7, 1, 8, 5, 5, 1, 1, 9, 10, 13, 11, 3, 12, 1, 1, 5, 1]) (bs := [11, 1]) (W := 192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1426_1 : P.sumLeaves 24 1460288 64 = 192 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 22817) rows (by decide) (by decide)).symm.trans contract1426_1

theorem c1426_2 : P.sumLeaves 24 1460352 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1426) (lo := 128) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1426 (by decide)
  decide +kernel

theorem contract1426_3 : P.leaf 30 22819 = 1264 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 22819) (ss := [(7, 6, 467), (8, 0, 468), (26, 6, 479), (2, 1, 480), (9, 6, 510), (3, 1, 523), (5, 1, 580), (30, 19, 866), (18, 11, 879), (19, 11, 908), (12, 1, 916), (29, 1, 916), (31, 1, 1258)]) (ids := [2, 4, 8, 9, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23, 25, 26]) (cs := [1, 1, 2, 1, 3, 3, 0, 3, 4, 5, 1, 6, 7, 8, 9, 10, 5, 5, 11, 12, 13, 14, 15, 16, 3, 17, 18, 1, 5, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1426_3 : P.sumLeaves 24 1460416 64 = 1264 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 22819) rows (by decide) (by decide)).symm.trans contract1426_3

theorem contract1426_4 : P.leaf 30 22820 = 524 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 22820) (ss := [(2, 1, 466), (7, 6, 467), (8, 0, 468), (26, 6, 479), (9, 6, 510), (5, 1, 523), (30, 19, 866), (18, 11, 879), (19, 11, 908), (16, 1, 1258), (31, 1, 1301), (20, 1, 1314)]) (ids := [1, 2, 4, 8, 9, 10, 11, 12, 13, 15, 19, 20, 21, 22, 23, 25, 26, 27]) (cs := [1, 2, 3, 1, 4, 4, 0, 4, 5, 6, 7, 8, 9, 10, 1, 11, 6, 6, 1, 12, 13, 14, 15, 16, 4, 17, 18, 19, 6, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1426_4 : P.sumLeaves 24 1460480 64 = 524 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 22820) rows (by decide) (by decide)).symm.trans contract1426_4

theorem c1426_5 : P.sumLeaves 24 1460544 704 = 13562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1426) (lo := 320) (len := 704) (W := 13562) check rows elimOK (by decide) (by decide) cover1426 (by decide)
  decide +kernel

theorem h1426 : P.leaf 34 1426 = 15542 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 192), (64, 0), (64, 1264), (64, 524), (704, 13562)]) (.cons c1426_0 (.cons c1426_1 (.cons c1426_2 (.cons c1426_3 (.cons c1426_4 (.cons c1426_5 (.nil))))))) (by decide) (by decide))

theorem cover1427 : P.CoversSplit 24 10 1427 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1427_0 : P.sumLeaves 24 1461248 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1427) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1427 (by decide)
  decide +kernel

theorem h1427 : P.leaf 34 1427 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1427_0 (.nil)) (by decide) (by decide))

theorem cover1428 : P.CoversSplit 24 10 1428 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1428_0 : P.sumLeaves 24 1462272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1428) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1428 (by decide)
  decide +kernel

theorem h1428 : P.leaf 34 1428 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1428_0 (.nil)) (by decide) (by decide))

theorem cover1429 : P.CoversSplit 24 10 1429 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1429_0 : P.sumLeaves 24 1463296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1429) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1429 (by decide)
  decide +kernel

theorem h1429 : P.leaf 34 1429 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1429_0 (.nil)) (by decide) (by decide))

theorem cover1430 : P.CoversSplit 24 10 1430 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1430_0 : P.sumLeaves 24 1464320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1430) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1430 (by decide)
  decide +kernel

theorem h1430 : P.leaf 34 1430 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1430_0 (.nil)) (by decide) (by decide))

theorem cover1431 : P.CoversSplit 24 10 1431 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1431_0 : P.sumLeaves 24 1465344 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1431) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1431 (by decide)
  decide +kernel

theorem h1431 : P.leaf 34 1431 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1431_0 (.nil)) (by decide) (by decide))

theorem h1432 : P.leaf 34 1432 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (33, 0, 486), (7, 6, 467), (8, 0, 509), (16, 10, 468), (35, 0, 531)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover1433 : P.CoversSplit 24 10 1433 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1433_0 : P.sumLeaves 24 1467392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1433) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1433 (by decide)
  decide +kernel

theorem h1433 : P.leaf 34 1433 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1433_0 (.nil)) (by decide) (by decide))

theorem h1434 : P.leaf 34 1434 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 486), (7, 6, 467), (8, 0, 509), (16, 10, 468), (35, 0, 531)]) (q := 615) check rows (by decide) (by decide +kernel) (by decide +kernel)

def seg : List (ℕ × ℕ) := [(1273, 48), (1274, 48), (1275, 48), (1276, 48), (1277, 48), (1278, 48), (1279, 48), (1408, 12), (1409, 24), (1410, 24), (1411, 48), (1412, 48), (1413, 48), (1414, 48), (1415, 48), (1416, 48), (1417, 48), (1418, 48), (1419, 48), (1420, 48), (1421, 48), (1422, 48), (1423, 48), (1426, 12), (1427, 24), (1428, 48), (1429, 48), (1430, 48), (1431, 48), (1432, 48), (1433, 48), (1434, 48)]

theorem segOK : checkSeg 16 perms 1273 1435 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1273 1435 1392 372262920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 372262920)
    (SegSum.cons (w := 48) h1273 (SegSum.cons (w := 48) h1274 (SegSum.cons (w := 48) h1275 (SegSum.cons (w := 48) h1276 (SegSum.cons (w := 48) h1277 (SegSum.cons (w := 48) h1278 (SegSum.cons (w := 48) h1279 (SegSum.cons (w := 12) h1408 (SegSum.cons (w := 24) h1409 (SegSum.cons (w := 24) h1410 (SegSum.cons (w := 48) h1411 (SegSum.cons (w := 48) h1412 (SegSum.cons (w := 48) h1413 (SegSum.cons (w := 48) h1414 (SegSum.cons (w := 48) h1415 (SegSum.cons (w := 48) h1416 (SegSum.cons (w := 48) h1417 (SegSum.cons (w := 48) h1418 (SegSum.cons (w := 48) h1419 (SegSum.cons (w := 48) h1420 (SegSum.cons (w := 48) h1421 (SegSum.cons (w := 48) h1422 (SegSum.cons (w := 48) h1423 (SegSum.cons (w := 12) h1426 (SegSum.cons (w := 24) h1427 (SegSum.cons (w := 48) h1428 (SegSum.cons (w := 48) h1429 (SegSum.cons (w := 48) h1430 (SegSum.cons (w := 48) h1431 (SegSum.cons (w := 48) h1432 (SegSum.cons (w := 48) h1433 (SegSum.cons (w := 48) h1434 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S9
