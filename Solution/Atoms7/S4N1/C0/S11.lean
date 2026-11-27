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

namespace RACert.S4N1.C0.S11

open RACert RACert.Problem

theorem cover1485 : P.CoversSplit 24 10 1485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1485_0 : P.sumLeaves 24 1520640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1485) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1485 (by decide)
  decide +kernel

theorem h1485 : P.leaf 34 1485 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1485_0 (.nil)) (by decide) (by decide))

theorem cover1486 : P.CoversSplit 24 10 1486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1486_0 : P.sumLeaves 24 1521664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1486) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1486 (by decide)
  decide +kernel

theorem h1486 : P.leaf 34 1486 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1486_0 (.nil)) (by decide) (by decide))

theorem cover1487 : P.CoversSplit 24 10 1487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1487_0 : P.sumLeaves 24 1522688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1487) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1487 (by decide)
  decide +kernel

theorem h1487 : P.leaf 34 1487 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1487_0 (.nil)) (by decide) (by decide))

theorem cover1494 : P.CoversSplit 24 10 1494 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0800000000000008000000000000000a080000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 867, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c1494_0 : P.sumLeaves 24 1529856 768 = 80392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1494) (lo := 0) (len := 768) (W := 80392) check rows elimOK (by decide) (by decide) cover1494 (by decide)
  decide +kernel

theorem contract1494_1 : P.leaf 30 23916 = 8624 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 23916) (ss := [(2, 1, 466), (5, 1, 523), (30, 19, 866), (18, 11, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 817), (19, 1, 908), (26, 1, 465), (28, 1, 465), (31, 1, 516), (17, 8, 1266), (8, 1, 1272)]) (ids := [1, 2, 5, 7, 11, 12, 13, 14, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 1, 6, 7, 8, 9, 1, 1, 1, 10, 11, 12, 16, 17, 13, 1, 14, 1, 15, 1, 1]) (bs := [14, 2]) (W := 8624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1494_1 : P.sumLeaves 24 1530624 64 = 8624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 23916) rows (by decide) (by decide)).symm.trans contract1494_1

theorem contract1494_2 : P.leaf 30 23917 = 14304 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 23917) (ss := [(30, 19, 866), (18, 11, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 817), (19, 1, 908), (26, 1, 465), (28, 1, 465), (2, 1, 468), (31, 1, 516), (17, 1, 1266)]) (ids := [1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 4, 1, 5, 6, 7, 1, 1, 1, 8, 9, 10, 11, 1, 1, 1, 12, 13, 14, 18, 19, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 2]) (W := 14304) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1494_2 : P.sumLeaves 24 1530688 64 = 14304 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 23917) rows (by decide) (by decide)).symm.trans contract1494_2

theorem contract1494_3 : P.leaf 30 23918 = 32336 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 23918) (ss := [(2, 1, 466), (5, 1, 523), (30, 19, 866), (18, 11, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 817), (19, 1, 908), (26, 1, 465), (28, 1, 465), (31, 1, 1210)]) (ids := [1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [1, 2, 3, 1, 1, 4, 5, 6, 1, 1, 1, 7, 8, 9, 10, 11, 1, 1, 12, 13, 14, 18, 19, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 2]) (W := 32336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1494_3 : P.sumLeaves 24 1530752 64 = 32336 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 23918) rows (by decide) (by decide)).symm.trans contract1494_3

theorem contract1494_4 : P.leaf 30 23919 = 84480 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 23919) (ss := [(30, 19, 866), (18, 11, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 817), (19, 1, 908), (26, 1, 465), (28, 1, 465), (31, 1, 1210)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 15, 18, 19, 20, 23, 25, 27, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 10, 11, 12, 13, 1, 1, 14, 15, 16, 20, 21, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 84480) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1494_4 : P.sumLeaves 24 1530816 64 = 84480 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 23919) rows (by decide) (by decide)).symm.trans contract1494_4

theorem h1494 : P.leaf 34 1494 = 220136 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 80392), (64, 8624), (64, 14304), (64, 32336), (64, 84480)]) (.cons c1494_0 (.cons c1494_1 (.cons c1494_2 (.cons c1494_3 (.cons c1494_4 (.nil)))))) (by decide) (by decide))

theorem cover1495 : P.CoversSplit 24 10 1495 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000ffc8000000000000cc00000000000000ffc8000000000000cc00000000000000fffa000000000000fffa00000000000000000000000000000000000000000000ffc8000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 858, 860, 865, 866, 915, 916, 1202, 1210, 1258, 1308]) (by decide +kernel)

theorem c1495_0 : P.sumLeaves 24 1530880 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1495) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover1495 (by decide)
  decide +kernel

theorem contract1495_1 : P.leaf 30 23922 = 28768 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 23922) (ss := [(2, 1, 480), (5, 3, 523), (3, 1, 536), (30, 1, 866), (11, 1, 879), (12, 1, 901), (29, 1, 915), (14, 1, 965), (19, 1, 929), (18, 1, 965), (13, 1, 922), (31, 1, 1251), (27, 1, 1258)]) (ids := [4, 5, 6, 7, 8, 13, 14, 15, 18, 19, 21, 22, 24, 26, 2, 20, 23]) (cs := [1, 1, 16, 1, 2, 3, 4, 5, 6, 1, 1, 1, 1, 7, 8, 9, 1, 1, 10, 11, 17, 12, 13, 18, 14, 1, 15, 1, 1, 1]) (bs := [14, 3]) (W := 28768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1495_1 : P.sumLeaves 24 1531008 64 = 28768 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 23922) rows (by decide) (by decide)).symm.trans contract1495_1

theorem c1495_2 : P.sumLeaves 24 1531072 703 = 2531324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1495) (lo := 192) (len := 703) (W := 2531324) check rows elimOK (by decide) (by decide) cover1495 (by decide)
  decide +kernel

theorem c1495_3 : P.sumLeaves 24 1531775 129 = 2921000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1495) (lo := 895) (len := 129) (W := 2921000) check rows elimOK (by decide) (by decide) cover1495 (by decide)
  decide +kernel

theorem h1495 : P.leaf 34 1495 = 5481092 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 28768), (703, 2531324), (129, 2921000)]) (.cons c1495_0 (.cons c1495_1 (.cons c1495_2 (.cons c1495_3 (.nil))))) (by decide) (by decide))

theorem cover1500 : P.CoversSplit 24 10 1500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1500_0 : P.sumLeaves 24 1536000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1500) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1500 (by decide)
  decide +kernel

theorem h1500 : P.leaf 34 1500 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1500_0 (.nil)) (by decide) (by decide))

theorem cover1501 : P.CoversSplit 24 10 1501 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1501_0 : P.sumLeaves 24 1537024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1501) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1501 (by decide)
  decide +kernel

theorem h1501 : P.leaf 34 1501 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1501_0 (.nil)) (by decide) (by decide))

theorem cover1502 : P.CoversSplit 24 10 1502 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0800000000000008000000000000000a080000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 858, 865, 867, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c1502_0 : P.sumLeaves 24 1538048 768 = 221580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1502) (lo := 0) (len := 768) (W := 221580) check rows elimOK (by decide) (by decide) cover1502 (by decide)
  decide +kernel

theorem contract1502_1 : P.leaf 30 24044 = 22800 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 24044) (ss := [(2, 1, 466), (5, 1, 523), (19, 1, 866), (18, 11, 879), (11, 1, 908), (30, 1, 1251), (26, 1, 465), (28, 1, 465), (31, 1, 516), (17, 8, 1266), (8, 1, 1272)]) (ids := [1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 18, 19, 20, 21, 23, 25, 27, 22]) (cs := [1, 2, 3, 1, 4, 5, 1, 6, 7, 1, 8, 9, 10, 11, 12, 1, 1, 1, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 1]) (W := 22800) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1502_1 : P.sumLeaves 24 1538816 64 = 22800 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 24044) rows (by decide) (by decide)).symm.trans contract1502_1

theorem c1502_2 : P.sumLeaves 24 1538880 192 = 439936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1502) (lo := 832) (len := 192) (W := 439936) check rows elimOK (by decide) (by decide) cover1502 (by decide)
  decide +kernel

theorem h1502 : P.leaf 34 1502 = 684316 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 221580), (64, 22800), (192, 439936)]) (.cons c1502_0 (.cons c1502_1 (.cons c1502_2 (.nil)))) (by decide) (by decide))

theorem cover1503 : P.CoversSplit 24 10 1503 0xfffa000000000000fffa000000000000fffa000000000000fffa000000000000ffc8000000000000cc00000000000000ffc8000000000000cc00000000000000fffa000000000000fffa00000000000000000000000000000000000000000000ffc8000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 858, 860, 865, 916, 1202, 1210, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1503_0 : P.sumLeaves 24 1539072 891 = 6273640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1503) (lo := 0) (len := 891) (W := 6273640) check rows elimOK (by decide) (by decide) cover1503 (by decide)
  decide +kernel

theorem c1503_1 : P.sumLeaves 24 1539963 133 = 7337702 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1503) (lo := 891) (len := 133) (W := 7337702) check rows elimOK (by decide) (by decide) cover1503 (by decide)
  decide +kernel

theorem h1503 : P.leaf 34 1503 = 13611342 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(891, 6273640), (133, 7337702)]) (.cons c1503_0 (.cons c1503_1 (.nil))) (by decide) (by decide))

theorem cover1516 : P.CoversSplit 24 10 1516 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1516_0 : P.sumLeaves 24 1552384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1516) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1516 (by decide)
  decide +kernel

theorem h1516 : P.leaf 34 1516 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1516_0 (.nil)) (by decide) (by decide))

theorem cover1517 : P.CoversSplit 24 10 1517 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1517_0 : P.sumLeaves 24 1553408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1517) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1517 (by decide)
  decide +kernel

theorem h1517 : P.leaf 34 1517 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1517_0 (.nil)) (by decide) (by decide))

theorem cover1518 : P.CoversSplit 24 10 1518 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1518_0 : P.sumLeaves 24 1554432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1518) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1518 (by decide)
  decide +kernel

theorem h1518 : P.leaf 34 1518 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1518_0 (.nil)) (by decide) (by decide))

theorem cover1519 : P.CoversSplit 24 10 1519 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c1519_0 : P.sumLeaves 24 1555456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1519) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1519 (by decide)
  decide +kernel

theorem h1519 : P.leaf 34 1519 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1519_0 (.nil)) (by decide) (by decide))

theorem cover1534 : P.CoversSplit 24 10 1534 0xf0f55555a0a00000f0f55555a0a00000f0f5555500050000f0f5555500050000f0c0554080800000c000440080000000f0c0554000000000c00044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 860, 865, 867, 916, 1202, 1258]) (by decide +kernel)

theorem c1534_0 : P.sumLeaves 24 1570816 983 = 1822779 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1534) (lo := 0) (len := 983) (W := 1822779) check rows elimOK (by decide) (by decide) cover1534 (by decide)
  decide +kernel

theorem c1534_1 : P.sumLeaves 24 1571799 41 = 1308790 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1534) (lo := 983) (len := 41) (W := 1308790) check rows elimOK (by decide) (by decide) cover1534 (by decide)
  decide +kernel

theorem h1534 : P.leaf 34 1534 = 3131569 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(983, 1822779), (41, 1308790)]) (.cons c1534_0 (.cons c1534_1 (.nil))) (by decide) (by decide))

theorem cover1535 : P.CoversSplit 24 10 1535 0xfffafafaaaaaaaaafffafafaaaaaaaaafffafafaaaaaaaaafffafafaaaaaaaaaffc8fac888888888ccc8c8c888888888ffc8fac888888888ccc8c8c888888888fffafafaaaaaaaaafffafafaaaaaaaaafffafafaaaaaaaaafffafafaaaaaaaaaffc8fac888888888ccc8c8c888888888ffc8fac888888888ccc8c8c888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 860, 865, 916, 1202, 1258]) (by decide +kernel)

theorem c1535_0 : P.sumLeaves 24 1571840 254 = 11384108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1535) (lo := 0) (len := 254) (W := 11384108) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem c1535_1 : P.sumLeaves 24 1572094 151 = 16454771 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1535) (lo := 254) (len := 151) (W := 16454771) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem c1535_2 : P.sumLeaves 24 1572245 178 = 31116046 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1535) (lo := 405) (len := 178) (W := 31116046) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem c1535_3 : P.sumLeaves 24 1572423 223 = 38264120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1535) (lo := 583) (len := 223) (W := 38264120) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem c1535_4 : P.sumLeaves 24 1572646 144 = 28641778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1535) (lo := 806) (len := 144) (W := 28641778) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem c1535_5 : P.sumLeaves 24 1572790 74 = 43467120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1535) (lo := 950) (len := 74) (W := 43467120) check rows elimOK (by decide) (by decide) cover1535 (by decide)
  decide +kernel

theorem h1535 : P.leaf 34 1535 = 169327943 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(254, 11384108), (151, 16454771), (178, 31116046), (223, 38264120), (144, 28641778), (74, 43467120)]) (.cons c1535_0 (.cons c1535_1 (.cons c1535_2 (.cons c1535_3 (.cons c1535_4 (.cons c1535_5 (.nil))))))) (by decide) (by decide))

theorem cover1590 : P.CoversSplit 24 10 1590 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000000000000000cc000000000000000000000000000000c40000000000000000110000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 480, 517, 529, 572, 860, 915, 916, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [468]), (9, [510], [573])]) (by decide +kernel)

theorem c1590_0 : P.sumLeaves 24 1628160 448 = 76 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1590) (lo := 0) (len := 448) (W := 76) check rows elimOK (by decide) (by decide) cover1590 (by decide)
  decide +kernel

theorem contract1590_1 : P.leaf 30 25447 = 3208 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 25447) (ss := [(8, 1, 468), (5, 1, 475), (31, 1, 529), (4, 1, 551), (27, 1, 572), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 486), (15, 1, 930), (30, 1, 1209), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 4, 8, 9, 10, 19, 21, 24, 26, 20, 22, 23]) (cs := [2, 3, 1, 1, 4, 1, 1, 1, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 8, 12, 9, 13, 14, 10, 1, 11, 1, 1, 1]) (bs := [10, 3]) (W := 3208) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1590_1 : P.sumLeaves 24 1628608 64 = 3208 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25447) rows (by decide) (by decide)).symm.trans contract1590_1

theorem c1590_2 : P.sumLeaves 24 1628672 512 = 44233 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1590) (lo := 512) (len := 512) (W := 44233) check rows elimOK (by decide) (by decide) cover1590 (by decide)
  decide +kernel

theorem h1590 : P.leaf 34 1590 = 47517 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 76), (64, 3208), (512, 44233)]) (.cons c1590_0 (.cons c1590_1 (.cons c1590_2 (.nil)))) (by decide) (by decide))

theorem cover1591 : P.CoversSplit 24 10 1591 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000c40000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [480, 517, 529, 572, 860, 915, 916, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (16, [528], [1258])]) (by decide +kernel)

theorem c1591_0 : P.sumLeaves 24 1629184 448 = 216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1591) (lo := 0) (len := 448) (W := 216) check rows elimOK (by decide) (by decide) cover1591 (by decide)
  decide +kernel

theorem contract1591_1 : P.leaf 30 25463 = 4352 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 25463) (ss := [(5, 1, 475), (31, 1, 529), (4, 1, 551), (27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [1, 4, 8, 9, 10, 21, 24, 0, 19, 20, 22, 23, 26]) (cs := [9, 2, 1, 1, 3, 1, 1, 1, 4, 5, 6, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 7, 12, 13, 8, 1, 14, 1, 1, 1]) (bs := [7, 6]) (W := 4352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1591_1 : P.sumLeaves 24 1629632 64 = 4352 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25463) rows (by decide) (by decide)).symm.trans contract1591_1

theorem c1591_2 : P.sumLeaves 24 1629696 512 = 148043 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1591) (lo := 512) (len := 512) (W := 148043) check rows elimOK (by decide) (by decide) cover1591 (by decide)
  decide +kernel

theorem h1591 : P.leaf 34 1591 = 152611 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 216), (64, 4352), (512, 148043)]) (.cons c1591_0 (.cons c1591_1 (.cons c1591_2 (.nil)))) (by decide) (by decide))

theorem cover1596 : P.CoversSplit 24 10 1596 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000840000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572])]) (by decide +kernel)

theorem c1596_0 : P.sumLeaves 24 1634304 448 = 18 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1596) (lo := 0) (len := 448) (W := 18) check rows elimOK (by decide) (by decide) cover1596 (by decide)
  decide +kernel

theorem contract1596_1 : P.leaf 30 25543 = 400 := by
  exact leaf_contract_factors (k := 30) (b := 9) (H := 25543) (ss := [(19, 1, 474), (18, 11, 475), (11, 4, 487), (31, 1, 529), (4, 1, 551), (5, 1, 426), (27, 1, 572), (6, 1, 459), (7, 1, 579), (8, 1, 580), (9, 1, 587), (12, 1, 818), (29, 1, 915), (2, 1, 410), (13, 1, 922), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [1, 8, 19, 24, 26, 20, 21, 22, 23]) (cs := [1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 8, 9, 10, 5, 1, 6, 1, 1, 1]) (bs := [5, 4]) (W := 400) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1596_1 : P.sumLeaves 24 1634752 64 = 400 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25543) rows (by decide) (by decide)).symm.trans contract1596_1

theorem c1596_2 : P.sumLeaves 24 1634816 448 = 448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1596) (lo := 512) (len := 448) (W := 448) check rows elimOK (by decide) (by decide) cover1596 (by decide)
  decide +kernel

theorem contract1596_3 : P.leaf 30 25551 = 13504 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 25551) (ss := [(11, 1, 475), (4, 1, 487), (5, 1, 426), (31, 1, 529), (27, 1, 572), (6, 1, 459), (12, 1, 818), (29, 1, 915), (2, 1, 410), (30, 1, 1209)]) (ids := [1, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 24, 26, 20, 21, 23]) (cs := [1, 2, 1, 1, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 19, 20, 16, 21, 17, 1, 18, 1, 1, 1]) (bs := [17, 3]) (W := 13504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1596_3 : P.sumLeaves 24 1635264 64 = 13504 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25551) rows (by decide) (by decide)).symm.trans contract1596_3

theorem h1596 : P.leaf 34 1596 = 14370 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 18), (64, 400), (448, 448), (64, 13504)]) (.cons c1596_0 (.cons c1596_1 (.cons c1596_2 (.cons c1596_3 (.nil))))) (by decide) (by decide))

theorem cover1597 : P.CoversSplit 24 10 1597 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000840000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (16, [528], [1258])]) (by decide +kernel)

theorem c1597_0 : P.sumLeaves 24 1635328 448 = 272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1597) (lo := 0) (len := 448) (W := 272) check rows elimOK (by decide) (by decide) cover1597 (by decide)
  decide +kernel

theorem contract1597_1 : P.leaf 30 25559 = 2048 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 25559) (ss := [(19, 1, 474), (18, 11, 475), (11, 4, 487), (31, 1, 529), (4, 1, 551), (5, 1, 426), (27, 1, 572), (7, 1, 579), (8, 1, 580), (9, 1, 587), (12, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 4, 8, 19, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 9, 10, 11, 1, 12, 1, 1, 1]) (bs := [0, 11]) (W := 2048) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1597_1 : P.sumLeaves 24 1635776 64 = 2048 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25559) rows (by decide) (by decide)).symm.trans contract1597_1

theorem c1597_2 : P.sumLeaves 24 1635840 512 = 154112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1597) (lo := 512) (len := 512) (W := 154112) check rows elimOK (by decide) (by decide) cover1597 (by decide)
  decide +kernel

theorem h1597 : P.leaf 34 1597 = 156432 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 272), (64, 2048), (512, 154112)]) (.cons c1597_0 (.cons c1597_1 (.cons c1597_2 (.nil)))) (by decide) (by decide))

theorem cover1598 : P.CoversSplit 24 10 1598 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000840000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572])]) (by decide +kernel)

noncomputable def f1598 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (1636352 + i)

theorem c1598_0 : rowSum f1598 0 1024 = 257421 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1598) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover1598 (by decide)
  decide +kernel

theorem sum1598 : rowSum f1598 0 1024 = 257421 :=
  c1598_0

theorem h1598 : P.leaf 34 1598 = 257421 :=
  leaf_weighted (k := 24) (d := 10) (H := 1598) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1598) (by decide) (by decide +kernel)) sum1598

theorem cover1599 : P.CoversSplit 24 10 1599 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000840000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 529, 572, 860, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (16, [528], [1258])]) (by decide +kernel)

noncomputable def f1599 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (1637376 + i)

theorem c1599_0 : rowSum f1599 0 1024 = 664929 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1599) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover1599 (by decide)
  decide +kernel

theorem sum1599 : rowSum f1599 0 1024 = 664929 :=
  c1599_0

theorem h1599 : P.leaf 34 1599 = 664929 :=
  leaf_weighted (k := 24) (d := 10) (H := 1599) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1599) (by decide) (by decide +kernel)) sum1599

theorem cover1622 : P.CoversSplit 24 10 1622 0xcc00cc00800000000000000000000000840084000000000000210021000000000000000000000000003300330000000000000000000000000021002100000000cc00cc00800000000000000000000000840084000400000000210021000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 516, 572, 573, 860, 915, 916, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c1622_0 : P.sumLeaves 24 1660928 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1622) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1622 (by decide)
  decide +kernel

theorem contract1622_1 : P.leaf 30 25956 = 164 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 25956) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (28, 2, 468), (21, 1, 537), (29, 0, 572), (9, 0, 573), (13, 0, 579), (26, 2, 510), (14, 0, 580), (6, 2, 479), (10, 3, 509), (15, 0, 587), (3, 2, 486), (17, 0, 587), (12, 5, 608), (20, 5, 488), (31, 5, 615), (19, 18, 1658)]) (ids := [0, 2, 3, 9, 16, 20, 21, 22, 28, 23]) (cs := [2, 2, 3, 4, 2, 0, 0, 0, 2, 5, 4, 0, 0, 0, 0, 0, 6, 6, 4, 1, 7, 8, 9, 11, 2, 0, 2, 0, 10, 4]) (bs := [9, 1]) (W := 164) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1622_1 : P.sumLeaves 24 1661184 64 = 164 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25956) rows (by decide) (by decide)).symm.trans contract1622_1

theorem contract1622_2 : P.leaf 30 25957 = 148 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 25957) (ss := [(27, 1, 573), (29, 1, 915), (8, 0, 1266), (28, 2, 468), (21, 1, 537), (14, 0, 580), (26, 6, 479), (10, 3, 509), (12, 5, 608), (20, 5, 488), (31, 5, 615), (9, 7, 629), (15, 13, 972), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 9, 11, 14, 16, 20, 21, 22, 28, 23]) (cs := [2, 3, 4, 5, 6, 7, 0, 7, 3, 8, 5, 9, 0, 9, 10, 10, 11, 11, 5, 1, 12, 13, 14, 16, 6, 1, 2, 1, 15, 5]) (bs := [14, 1]) (W := 148) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1622_2 : P.sumLeaves 24 1661248 64 = 148 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25957) rows (by decide) (by decide)).symm.trans contract1622_2

theorem c1622_3 : P.sumLeaves 24 1661312 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1622) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1622 (by decide)
  decide +kernel

theorem contract1622_4 : P.leaf 30 25959 = 9842 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 25959) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 19, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 12, 13, 18, 14, 1, 15, 1, 16, 17]) (bs := [16, 1]) (W := 9842) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1622_4 : P.sumLeaves 24 1661376 64 = 9842 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25959) rows (by decide) (by decide)).symm.trans contract1622_4

theorem c1622_5 : P.sumLeaves 24 1661440 256 = 23594 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1622) (lo := 512) (len := 256) (W := 23594) check rows elimOK (by decide) (by decide) cover1622 (by decide)
  decide +kernel

theorem contract1622_6 : P.leaf 30 25964 = 1305 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 25964) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (28, 2, 468), (29, 0, 572), (9, 0, 573), (13, 0, 579), (26, 2, 510), (14, 0, 580), (6, 2, 479), (10, 3, 509), (15, 0, 587), (3, 2, 486), (17, 0, 587), (12, 5, 608), (5, 1, 488), (31, 1, 615)]) (ids := [0, 20, 21, 22, 2, 9, 16, 17, 18, 19, 23, 28]) (cs := [2, 2, 6, 1, 2, 0, 0, 0, 2, 7, 1, 0, 0, 0, 0, 0, 8, 9, 10, 11, 3, 4, 5, 12, 2, 0, 2, 0, 13, 1]) (bs := [4, 8]) (W := 1305) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1622_6 : P.sumLeaves 24 1661696 64 = 1305 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25964) rows (by decide) (by decide)).symm.trans contract1622_6

theorem c1622_7 : P.sumLeaves 24 1661760 192 = 193076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1622) (lo := 832) (len := 192) (W := 193076) check rows elimOK (by decide) (by decide) cover1622 (by decide)
  decide +kernel

theorem h1622 : P.leaf 34 1622 = 228129 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 164), (64, 148), (64, 0), (64, 9842), (256, 23594), (64, 1305), (192, 193076)]) (.cons c1622_0 (.cons c1622_1 (.cons c1622_2 (.cons c1622_3 (.cons c1622_4 (.cons c1622_5 (.cons c1622_6 (.cons c1622_7 (.nil))))))))) (by decide) (by decide))

theorem cover1623 : P.CoversSplit 24 10 1623 0xcc00cc00800000000000000000000000cc00cc000000000000330033000000000000000000000000003300330000000000000000000000000033003300000000cc00cc00800000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 516, 572, 573, 915, 916, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c1623_0 : P.sumLeaves 24 1661952 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1623) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1623 (by decide)
  decide +kernel

theorem contract1623_1 : P.leaf 30 25972 = 938 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 25972) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (21, 1, 482), (15, 0, 587), (17, 0, 587), (12, 5, 608), (20, 5, 488), (31, 5, 615), (19, 18, 1658)]) (ids := [0, 1, 2, 3, 4, 8, 9, 16, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 5, 6, 0, 0, 0, 7, 8, 5, 0, 0, 0, 0, 0, 9, 9, 5, 1, 10, 11, 12, 16, 13, 0, 14, 0, 15, 5]) (bs := [14, 1]) (W := 938) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1623_1 : P.sumLeaves 24 1662208 64 = 938 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25972) rows (by decide) (by decide)).symm.trans contract1623_1

theorem contract1623_2 : P.leaf 30 25973 = 2814 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 25973) (ss := [(27, 1, 573), (29, 1, 915), (8, 0, 1266), (14, 0, 580), (21, 1, 482), (12, 5, 608), (20, 5, 488), (31, 5, 615), (9, 7, 629), (15, 13, 972), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 8, 9, 11, 14, 16, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 5, 6, 7, 0, 7, 8, 9, 5, 10, 0, 10, 11, 11, 12, 12, 5, 1, 13, 14, 15, 19, 16, 1, 17, 1, 18, 5]) (bs := [17, 1]) (W := 2814) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1623_2 : P.sumLeaves 24 1662272 64 = 2814 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25973) rows (by decide) (by decide)).symm.trans contract1623_2

theorem c1623_3 : P.sumLeaves 24 1662336 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1623) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1623 (by decide)
  decide +kernel

theorem contract1623_4 : P.leaf 30 25975 = 13016 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 25975) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 17, 10, 11, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 13016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1623_4 : P.sumLeaves 24 1662400 64 = 13016 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25975) rows (by decide) (by decide)).symm.trans contract1623_4

theorem c1623_5 : P.sumLeaves 24 1662464 256 = 209246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1623) (lo := 512) (len := 256) (W := 209246) check rows elimOK (by decide) (by decide) cover1623 (by decide)
  decide +kernel

theorem contract1623_6 : P.leaf 30 25980 = 7540 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 25980) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (12, 5, 608), (5, 1, 488), (31, 1, 615)]) (ids := [0, 1, 2, 4, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 17, 0, 18, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1623_6 : P.sumLeaves 24 1662720 64 = 7540 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 25980) rows (by decide) (by decide)).symm.trans contract1623_6

theorem c1623_7 : P.sumLeaves 24 1662784 192 = 1112396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1623) (lo := 832) (len := 192) (W := 1112396) check rows elimOK (by decide) (by decide) cover1623 (by decide)
  decide +kernel

theorem h1623 : P.leaf 34 1623 = 1345950 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 938), (64, 2814), (64, 0), (64, 13016), (256, 209246), (64, 7540), (192, 1112396)]) (.cons c1623_0 (.cons c1623_1 (.cons c1623_2 (.cons c1623_3 (.cons c1623_4 (.cons c1623_5 (.cons c1623_6 (.cons c1623_7 (.nil))))))))) (by decide) (by decide))

theorem cover1628 : P.CoversSplit 24 10 1628 0xcc00cc00000000000000000000000000840084000000000000210021000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000840084000000000000210021000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 523, 536, 572, 573, 860, 915, 1258]) (by decide +kernel)

theorem c1628_0 : P.sumLeaves 24 1667072 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1628) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1628 (by decide)
  decide +kernel

theorem contract1628_1 : P.leaf 30 26052 = 36 := by
  exact leaf_contract_factors (k := 30) (b := 6) (H := 26052) (ss := [(19, 11, 474), (18, 1, 475), (11, 1, 480), (4, 1, 487), (5, 1, 425), (31, 1, 536), (12, 1, 818), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (20, 1, 531), (21, 1, 537), (29, 0, 572), (28, 26, 508), (9, 0, 573), (17, 0, 587), (10, 6, 467), (14, 13, 628), (15, 13, 636), (13, 0, 915), (3, 2, 486), (6, 2, 509), (26, 2, 466)]) (ids := [0, 20, 21, 22, 23, 28]) (cs := [2, 2, 1, 1, 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 3, 4, 5, 6, 2, 0, 2, 0, 7, 1]) (bs := [4, 2]) (W := 36) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1628_1 : P.sumLeaves 24 1667328 64 = 36 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26052) rows (by decide) (by decide)).symm.trans contract1628_1

theorem contract1628_2 : P.leaf 30 26053 = 32 := by
  exact leaf_contract_factors (k := 30) (b := 5) (H := 26053) (ss := [(19, 11, 474), (18, 1, 475), (11, 1, 480), (4, 1, 487), (5, 1, 425), (31, 1, 536), (27, 1, 573), (6, 1, 459), (7, 1, 579), (26, 1, 516), (9, 1, 587), (12, 1, 818), (28, 1, 860), (29, 1, 915), (2, 1, 410), (13, 1, 922), (15, 1, 930), (16, 1, 1265), (8, 0, 1266), (3, 1, 418), (10, 1, 509), (20, 1, 531), (21, 1, 537), (14, 0, 1266), (17, 1, 1273)]) (ids := [20, 21, 22, 23, 28]) (cs := [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 1, 1, 1, 6, 1]) (bs := [0, 5]) (W := 32) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1628_2 : P.sumLeaves 24 1667392 64 = 32 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26053) rows (by decide) (by decide)).symm.trans contract1628_2

theorem c1628_3 : P.sumLeaves 24 1667456 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1628) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1628 (by decide)
  decide +kernel

theorem contract1628_4 : P.leaf 30 26055 = 664 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 26055) (ss := [(19, 11, 474), (18, 1, 475), (11, 1, 480), (4, 1, 487), (5, 1, 425), (31, 1, 536), (27, 1, 573), (6, 1, 459), (7, 1, 579), (8, 1, 580), (9, 1, 587), (12, 1, 818), (29, 1, 915), (2, 1, 410), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [1, 8, 19, 22, 24, 26, 28, 20, 21, 23]) (cs := [1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9, 10, 5, 11, 6, 1, 7, 1, 8, 1]) (bs := [7, 3]) (W := 664) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1628_4 : P.sumLeaves 24 1667520 64 = 664 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26055) rows (by decide) (by decide)).symm.trans contract1628_4

theorem c1628_5 : P.sumLeaves 24 1667584 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1628) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1628 (by decide)
  decide +kernel

theorem contract1628_6 : P.leaf 30 26060 = 288 := by
  exact leaf_contract_factors (k := 30) (b := 9) (H := 26060) (ss := [(11, 1, 474), (4, 1, 487), (5, 1, 425), (31, 1, 536), (12, 1, 818), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (28, 26, 508), (9, 0, 573), (17, 0, 587), (10, 6, 467), (14, 13, 628), (15, 13, 636), (13, 0, 915), (20, 1, 481), (3, 2, 486), (6, 2, 509), (26, 2, 466)]) (ids := [0, 20, 21, 22, 16, 17, 19, 23, 28]) (cs := [2, 2, 1, 1, 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 6, 7, 1, 8, 3, 4, 5, 9, 2, 0, 2, 0, 10, 1]) (bs := [4, 5]) (W := 288) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1628_6 : P.sumLeaves 24 1667840 64 = 288 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26060) rows (by decide) (by decide)).symm.trans contract1628_6

theorem contract1628_7 : P.leaf 30 26061 = 3456 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 26061) (ss := [(11, 1, 474), (4, 1, 487), (5, 1, 425), (31, 1, 536), (27, 1, 573), (6, 1, 459), (12, 1, 818), (29, 1, 915), (2, 1, 410), (17, 1, 1266), (16, 1, 1272)]) (ids := [1, 5, 6, 7, 8, 11, 12, 13, 16, 17, 18, 19, 22, 23, 24, 26, 28, 20, 21]) (cs := [1, 2, 1, 1, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 1, 1, 10, 11, 12, 13, 19, 20, 14, 15, 16, 1, 17, 1, 18, 1]) (bs := [17, 2]) (W := 3456) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1628_7 : P.sumLeaves 24 1667904 64 = 3456 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26061) rows (by decide) (by decide)).symm.trans contract1628_7

theorem c1628_8 : P.sumLeaves 24 1667968 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1628) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1628 (by decide)
  decide +kernel

theorem contract1628_9 : P.leaf 30 26063 = 27016 := by
  exact leaf_contract_factors (k := 30) (b := 21) (H := 26063) (ss := [(11, 1, 474), (4, 1, 487), (5, 1, 425), (31, 1, 536), (27, 1, 573), (6, 1, 459), (12, 1, 818), (29, 1, 915), (2, 1, 410)]) (ids := [1, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 24, 26, 28, 20, 21, 23]) (cs := [1, 2, 1, 1, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 16, 22, 17, 1, 18, 1, 19, 1]) (bs := [18, 3]) (W := 27016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1628_9 : P.sumLeaves 24 1668032 64 = 27016 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26063) rows (by decide) (by decide)).symm.trans contract1628_9

theorem h1628 : P.leaf 34 1628 = 31492 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 36), (64, 32), (64, 0), (64, 664), (256, 0), (64, 288), (64, 3456), (64, 0), (64, 27016)]) (.cons c1628_0 (.cons c1628_1 (.cons c1628_2 (.cons c1628_3 (.cons c1628_4 (.cons c1628_5 (.cons c1628_6 (.cons c1628_7 (.cons c1628_8 (.cons c1628_9 (.nil))))))))))) (by decide) (by decide))

theorem cover1629 : P.CoversSplit 24 10 1629 0xcc00cc00000000000000000000000000cc00cc000000000000330033000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000cc00cc000000000000330033000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 523, 536, 572, 573, 915, 1258]) (by decide +kernel)

theorem c1629_0 : P.sumLeaves 24 1668096 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1629) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1629 (by decide)
  decide +kernel

theorem contract1629_1 : P.leaf 30 26068 = 208 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 26068) (ss := [(19, 11, 474), (18, 1, 475), (11, 1, 480), (4, 1, 487), (5, 1, 425), (31, 1, 536), (12, 1, 818), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (17, 0, 587), (14, 13, 628), (15, 13, 636), (13, 0, 915), (20, 1, 481), (21, 1, 537)]) (ids := [0, 1, 4, 8, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 1, 1, 4, 0, 0, 0, 5, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 6, 7, 8, 12, 9, 0, 10, 0, 11, 1]) (bs := [10, 1]) (W := 208) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1629_1 : P.sumLeaves 24 1668352 64 = 208 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26068) rows (by decide) (by decide)).symm.trans contract1629_1

theorem contract1629_2 : P.leaf 30 26069 = 888 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 26069) (ss := [(19, 11, 474), (18, 1, 475), (11, 1, 480), (4, 1, 487), (5, 1, 425), (31, 1, 536), (27, 1, 573), (7, 1, 579), (9, 1, 587), (12, 1, 818), (29, 1, 915), (13, 1, 922), (15, 1, 930), (16, 1, 1265), (8, 0, 1266), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (17, 1, 1273)]) (ids := [0, 1, 4, 8, 22, 24, 26, 28, 20, 21, 23]) (cs := [2, 3, 1, 1, 4, 1, 0, 1, 5, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 10, 11, 6, 12, 7, 1, 8, 1, 9, 1]) (bs := [8, 3]) (W := 888) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1629_2 : P.sumLeaves 24 1668416 64 = 888 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26069) rows (by decide) (by decide)).symm.trans contract1629_2

theorem c1629_3 : P.sumLeaves 24 1668480 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1629) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1629 (by decide)
  decide +kernel

theorem contract1629_4 : P.leaf 30 26071 = 3008 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 26071) (ss := [(19, 11, 474), (18, 1, 475), (11, 1, 480), (4, 1, 487), (5, 1, 425), (31, 1, 536), (27, 1, 573), (7, 1, 579), (8, 1, 580), (9, 1, 587), (12, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 4, 22, 24, 26, 28, 1, 8, 19, 20, 21, 23]) (cs := [2, 8, 1, 1, 3, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 12, 4, 13, 5, 1, 6, 1, 7, 1]) (bs := [6, 6]) (W := 3008) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1629_4 : P.sumLeaves 24 1668544 64 = 3008 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26071) rows (by decide) (by decide)).symm.trans contract1629_4

theorem c1629_5 : P.sumLeaves 24 1668608 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1629) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1629 (by decide)
  decide +kernel

theorem contract1629_6 : P.leaf 30 26076 = 1664 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 26076) (ss := [(11, 1, 474), (4, 1, 487), (5, 1, 425), (31, 1, 536), (12, 1, 818), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (17, 0, 587), (14, 13, 628), (15, 13, 636), (13, 0, 915), (20, 1, 481)]) (ids := [0, 1, 4, 8, 20, 21, 22, 24, 26, 28, 16, 17, 19, 23]) (cs := [2, 3, 1, 1, 4, 0, 0, 0, 5, 1, 1, 0, 0, 0, 0, 0, 12, 13, 1, 14, 6, 7, 8, 15, 9, 0, 10, 0, 11, 1]) (bs := [10, 4]) (W := 1664) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1629_6 : P.sumLeaves 24 1668864 64 = 1664 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26076) rows (by decide) (by decide)).symm.trans contract1629_6

theorem c1629_7 : P.sumLeaves 24 1668928 192 = 373872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1629) (lo := 832) (len := 192) (W := 373872) check rows elimOK (by decide) (by decide) cover1629 (by decide)
  decide +kernel

theorem h1629 : P.leaf 34 1629 = 379640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 208), (64, 888), (64, 0), (64, 3008), (256, 0), (64, 1664), (192, 373872)]) (.cons c1629_0 (.cons c1629_1 (.cons c1629_2 (.cons c1629_3 (.cons c1629_4 (.cons c1629_5 (.cons c1629_6 (.cons c1629_7 (.nil))))))))) (by decide) (by decide))

theorem cover1630 : P.CoversSplit 24 10 1630 0xcc00cc00800000000000000000000000840084000000000000210021000000000000000000000000003300330000000000000000000000000021002100000000cc00cc00800000000000000000000000840084000400000000210021000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 523, 572, 573, 860, 915, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c1630_0 : P.sumLeaves 24 1669120 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1630) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1630 (by decide)
  decide +kernel

theorem contract1630_1 : P.leaf 30 26084 = 166 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 26084) (ss := [(16, 0, 1258), (5, 1, 615), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (20, 1, 531), (21, 1, 537), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (10, 3, 509), (15, 0, 587), (3, 2, 486), (17, 0, 587), (6, 2, 467), (12, 1, 825), (19, 18, 1658)]) (ids := [0, 2, 9, 16, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 2, 3, 1, 2, 0, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 5, 5, 1, 1, 6, 7, 8, 13, 9, 0, 10, 0, 11, 12]) (bs := [11, 1]) (W := 166) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1630_1 : P.sumLeaves 24 1669376 64 = 166 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26084) rows (by decide) (by decide)).symm.trans contract1630_1

theorem contract1630_2 : P.leaf 30 26085 = 504 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26085) (ss := [(27, 1, 573), (29, 1, 915), (8, 0, 1266), (21, 1, 537), (14, 0, 580), (5, 1, 433), (10, 3, 509), (20, 1, 531), (9, 7, 629), (12, 1, 825), (15, 13, 972), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 2, 4, 5, 9, 11, 14, 16, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 1, 5, 6, 0, 6, 3, 7, 1, 8, 0, 8, 9, 9, 10, 10, 1, 1, 11, 12, 13, 18, 14, 1, 15, 1, 16, 17]) (bs := [16, 1]) (W := 504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1630_2 : P.sumLeaves 24 1669440 64 = 504 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26085) rows (by decide) (by decide)).symm.trans contract1630_2

theorem c1630_3 : P.sumLeaves 24 1669504 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1630) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1630 (by decide)
  decide +kernel

theorem contract1630_4 : P.leaf 30 26087 = 12522 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26087) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 19, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 12, 13, 18, 14, 1, 15, 1, 16, 17]) (bs := [16, 1]) (W := 12522) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1630_4 : P.sumLeaves 24 1669568 64 = 12522 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26087) rows (by decide) (by decide)).symm.trans contract1630_4

theorem c1630_5 : P.sumLeaves 24 1669632 256 = 42872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1630) (lo := 512) (len := 256) (W := 42872) check rows elimOK (by decide) (by decide) cover1630 (by decide)
  decide +kernel

theorem contract1630_6 : P.leaf 30 26092 = 1305 := by
  apply (leaf_contract (k := 30) (b := 15) (H := 26092) (ss := [(16, 0, 1258), (5, 1, 615), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (10, 3, 509), (15, 0, 587), (3, 2, 486), (17, 0, 587), (6, 2, 467), (12, 1, 958)]) (ids := [0, 2, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 29]) (cs := [2, 2, 3, 1, 2, 0, 0, 0, 2, 4, 1, 0, 0, 0, 0, 0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 14, 0, 15, 16]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1630_6 : P.sumLeaves 24 1669888 64 = 1305 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26092) rows (by decide) (by decide)).symm.trans contract1630_6

theorem c1630_7 : P.sumLeaves 24 1669952 192 = 505006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1630) (lo := 832) (len := 192) (W := 505006) check rows elimOK (by decide) (by decide) cover1630 (by decide)
  decide +kernel

theorem h1630 : P.leaf 34 1630 = 562375 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 166), (64, 504), (64, 0), (64, 12522), (256, 42872), (64, 1305), (192, 505006)]) (.cons c1630_0 (.cons c1630_1 (.cons c1630_2 (.cons c1630_3 (.cons c1630_4 (.cons c1630_5 (.cons c1630_6 (.cons c1630_7 (.nil))))))))) (by decide) (by decide))

theorem cover1631 : P.CoversSplit 24 10 1631 0xcc00cc00800000000000000000000000cc00cc000000000000330033000000000000000000000000003300330000000000000000000000000033003300000000cc00cc00800000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 523, 572, 573, 915, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c1631_0 : P.sumLeaves 24 1670144 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1631) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1631 (by decide)
  decide +kernel

theorem contract1631_1 : P.leaf 30 26100 = 944 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 26100) (ss := [(16, 0, 1258), (5, 1, 615), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (20, 1, 531), (21, 1, 537), (15, 0, 587), (17, 0, 587), (12, 1, 825), (19, 18, 1658)]) (ids := [0, 1, 2, 4, 8, 9, 16, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 8, 8, 1, 1, 9, 10, 11, 16, 12, 0, 13, 0, 14, 15]) (bs := [14, 1]) (W := 944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1631_1 : P.sumLeaves 24 1670400 64 = 944 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26100) rows (by decide) (by decide)).symm.trans contract1631_1

theorem contract1631_2 : P.leaf 30 26101 = 3646 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 26101) (ss := [(27, 1, 573), (29, 1, 915), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 2, 4, 5, 8, 9, 11, 14, 16, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 1, 5, 6, 0, 6, 7, 8, 1, 9, 0, 9, 10, 10, 11, 11, 1, 1, 12, 13, 14, 19, 15, 1, 16, 1, 17, 18]) (bs := [17, 1]) (W := 3646) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1631_2 : P.sumLeaves 24 1670464 64 = 3646 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26101) rows (by decide) (by decide)).symm.trans contract1631_2

theorem c1631_3 : P.sumLeaves 24 1670528 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1631) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1631 (by decide)
  decide +kernel

theorem contract1631_4 : P.leaf 30 26103 = 15300 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26103) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 17, 10, 11, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 15300) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1631_4 : P.sumLeaves 24 1670592 64 = 15300 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26103) rows (by decide) (by decide)).symm.trans contract1631_4

theorem c1631_5 : P.sumLeaves 24 1670656 256 = 255430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1631) (lo := 512) (len := 256) (W := 255430) check rows elimOK (by decide) (by decide) cover1631 (by decide)
  decide +kernel

theorem contract1631_6 : P.leaf 30 26108 = 7540 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 26108) (ss := [(16, 0, 1258), (5, 1, 615), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (12, 1, 958)]) (ids := [0, 1, 2, 4, 8, 9, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 29]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0, 17, 0, 18, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1631_6 : P.sumLeaves 24 1670912 64 = 7540 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26108) rows (by decide) (by decide)).symm.trans contract1631_6

theorem c1631_7 : P.sumLeaves 24 1670976 192 = 1685672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1631) (lo := 832) (len := 192) (W := 1685672) check rows elimOK (by decide) (by decide) cover1631 (by decide)
  decide +kernel

theorem h1631 : P.leaf 34 1631 = 1968532 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 944), (64, 3646), (64, 0), (64, 15300), (256, 255430), (64, 7540), (192, 1685672)]) (.cons c1631_0 (.cons c1631_1 (.cons c1631_2 (.cons c1631_3 (.cons c1631_4 (.cons c1631_5 (.cons c1631_6 (.cons c1631_7 (.nil))))))))) (by decide) (by decide))

theorem cover1644 : P.CoversSplit 24 10 1644 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000110000000000000000000000000000001100000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 522, 572, 860, 872, 915, 1202, 1209, 1251]) (by decide +kernel)

theorem c1644_0 : P.sumLeaves 24 1683456 1024 = 13898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1644) (lo := 0) (len := 1024) (W := 13898) check rows elimOK (by decide) (by decide) cover1644 (by decide)
  decide +kernel

theorem h1644 : P.leaf 34 1644 = 13898 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13898)]) (.cons c1644_0 (.nil)) (by decide) (by decide))

theorem cover1645 : P.CoversSplit 24 10 1645 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000002200000000000000000000000000000022000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 860, 872, 915, 1209, 1210, 1251]) (by decide +kernel)

theorem c1645_0 : P.sumLeaves 24 1684480 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1645) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_1 : P.leaf 30 26325 = 768 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 26325) (ss := [(27, 1, 473), (29, 1, 473), (19, 1, 474), (18, 1, 475), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (7, 1, 579), (9, 1, 587), (12, 1, 867), (11, 1, 818), (31, 1, 872), (13, 1, 922), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (14, 0, 1266), (17, 1, 1273), (20, 1, 1657)]) (ids := [6, 19, 4, 8, 20, 21, 22, 23, 24, 26]) (cs := [1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 3, 6, 7, 8, 9, 10, 1, 11, 1, 1, 1]) (bs := [2, 8]) (W := 768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1645_1 : P.sumLeaves 24 1684800 64 = 768 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26325) rows (by decide) (by decide)).symm.trans contract1645_1

theorem c1645_2 : P.sumLeaves 24 1684864 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1645) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_3 : P.leaf 30 26327 = 960 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 26327) (ss := [(27, 1, 473), (29, 1, 473), (19, 1, 474), (18, 1, 475), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (7, 1, 579), (9, 1, 587), (12, 1, 867), (11, 1, 818), (31, 1, 872), (13, 1, 922), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [6, 8, 19, 26, 4, 20, 21, 22, 23, 24]) (cs := [1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 8, 9, 10, 11, 1, 5, 1, 1, 1]) (bs := [4, 6]) (W := 960) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1645_3 : P.sumLeaves 24 1684928 64 = 960 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26327) rows (by decide) (by decide)).symm.trans contract1645_3

theorem c1645_4 : P.sumLeaves 24 1684992 320 = 5079 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1645) (lo := 512) (len := 320) (W := 5079) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_5 : P.leaf 30 26333 = 18432 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 26333) (ss := [(27, 1, 473), (29, 1, 473), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (12, 1, 867), (11, 1, 818), (31, 1, 872), (30, 1, 1209), (17, 1, 1266), (16, 1, 1272), (18, 1, 1265), (19, 1, 1273)]) (ids := [4, 5, 6, 7, 8, 11, 12, 13, 18, 19, 21, 22, 23, 24, 26, 20]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 7, 8, 9, 1, 1, 1, 1, 10, 11, 17, 12, 13, 14, 15, 1, 16, 1, 1, 1]) (bs := [15, 1]) (W := 18432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1645_5 : P.sumLeaves 24 1685312 64 = 18432 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26333) rows (by decide) (by decide)).symm.trans contract1645_5

theorem c1645_6 : P.sumLeaves 24 1685376 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1645) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_7 : P.leaf 30 26335 = 77312 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 26335) (ss := [(27, 1, 473), (29, 1, 473), (4, 1, 480), (2, 1, 410), (3, 1, 417), (5, 1, 425), (12, 1, 867), (11, 1, 818), (31, 1, 872), (30, 1, 1209)]) (ids := [4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 24, 26, 20, 23]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 16, 17, 21, 18, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 77312) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1645_7 : P.sumLeaves 24 1685440 64 = 77312 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26335) rows (by decide) (by decide)).symm.trans contract1645_7

theorem h1645 : P.leaf 34 1645 = 102551 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 768), (64, 0), (64, 960), (320, 5079), (64, 18432), (64, 0), (64, 77312)]) (.cons c1645_0 (.cons c1645_1 (.cons c1645_2 (.cons c1645_3 (.cons c1645_4 (.cons c1645_5 (.cons c1645_6 (.cons c1645_7 (.nil))))))))) (by decide) (by decide))

theorem cover1646 : P.CoversSplit 24 10 1646 0x8800000000000000000000000000000080000000000000000021000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 860, 872, 915, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem c1646_0 : P.sumLeaves 24 1685504 1024 = 130896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1646) (lo := 0) (len := 1024) (W := 130896) check rows elimOK (by decide) (by decide) cover1646 (by decide)
  decide +kernel

theorem h1646 : P.leaf 34 1646 = 130896 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 130896)]) (.cons c1646_0 (.nil)) (by decide) (by decide))

theorem cover1647 : P.CoversSplit 24 10 1647 0xcc000000000000000000000000000000cc0000000000000000320000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000320000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 860, 872, 915, 1202, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem c1647_0 : P.sumLeaves 24 1686528 320 = 252 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1647) (lo := 0) (len := 320) (W := 252) check rows elimOK (by decide) (by decide) cover1647 (by decide)
  decide +kernel

theorem contract1647_1 : P.leaf 30 26357 = 1504 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 26357) (ss := [(19, 1, 523), (18, 1, 524), (4, 1, 529), (27, 1, 572), (7, 1, 579), (9, 1, 587), (12, 1, 867), (29, 1, 915), (13, 1, 922), (15, 1, 930), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (14, 0, 1266), (8, 0, 923), (5, 1, 433), (20, 1, 628), (21, 1, 874), (17, 1, 1273)]) (ids := [1, 4, 8, 9, 21, 24, 0, 20, 22, 23, 26]) (cs := [8, 2, 1, 1, 3, 1, 0, 1, 4, 5, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 9, 6, 10, 11, 7, 1, 12, 1, 1, 1]) (bs := [6, 5]) (W := 1504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1647_1 : P.sumLeaves 24 1686848 64 = 1504 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26357) rows (by decide) (by decide)).symm.trans contract1647_1

theorem c1647_2 : P.sumLeaves 24 1686912 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1647) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1647 (by decide)
  decide +kernel

theorem contract1647_3 : P.leaf 30 26359 = 4928 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 26359) (ss := [(19, 1, 523), (18, 1, 524), (4, 1, 529), (27, 1, 572), (7, 1, 579), (9, 1, 587), (12, 1, 867), (29, 1, 915), (13, 1, 922), (14, 1, 923), (8, 1, 580), (15, 1, 930), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 3, 4, 8, 9, 20, 21, 24, 19, 22, 23, 26]) (cs := [2, 3, 1, 4, 5, 1, 1, 1, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 8, 9, 12, 13, 10, 1, 14, 1, 1, 1]) (bs := [9, 4]) (W := 4928) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1647_3 : P.sumLeaves 24 1686976 64 = 4928 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26359) rows (by decide) (by decide)).symm.trans contract1647_3

theorem c1647_4 : P.sumLeaves 24 1687040 512 = 789888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1647) (lo := 512) (len := 512) (W := 789888) check rows elimOK (by decide) (by decide) cover1647 (by decide)
  decide +kernel

theorem h1647 : P.leaf 34 1647 = 796572 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 252), (64, 1504), (64, 0), (64, 4928), (512, 789888)]) (.cons c1647_0 (.cons c1647_1 (.cons c1647_2 (.cons c1647_3 (.cons c1647_4 (.nil)))))) (by decide) (by decide))

theorem cover1662 : P.CoversSplit 24 10 1662 0xcc00cc00880000000000000000000000c400c4000400000000310031000100000000000000000000003300330000000000000000000000000031003100000000cc00cc00880000000000000000000000c400c4000000000000310031000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 860, 867, 915, 1202, 1209, 1217, 1258]) (by decide +kernel)

theorem c1662_0 : P.sumLeaves 24 1701888 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1662) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1662 (by decide)
  decide +kernel

theorem contract1662_1 : P.leaf 30 26596 = 262 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 26596) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (5, 1, 433), (15, 0, 587), (3, 2, 486), (17, 0, 587), (12, 1, 825), (21, 1, 874), (20, 1, 880), (31, 1, 1217), (19, 18, 1658)]) (ids := [0, 2, 4, 8, 9, 16, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 2, 3, 1, 4, 0, 0, 0, 5, 6, 1, 0, 0, 0, 0, 0, 7, 7, 1, 1, 8, 9, 10, 14, 11, 0, 12, 0, 13, 1]) (bs := [12, 1]) (W := 262) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1662_1 : P.sumLeaves 24 1702144 64 = 262 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26596) rows (by decide) (by decide)).symm.trans contract1662_1

theorem contract1662_2 : P.leaf 30 26597 = 1648 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26597) (ss := [(27, 1, 572), (29, 1, 915), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (12, 1, 825), (21, 1, 874), (9, 7, 629), (20, 1, 880), (15, 13, 972), (31, 1, 1217), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 2, 4, 5, 8, 9, 11, 14, 16, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 1, 5, 6, 0, 6, 7, 8, 1, 9, 0, 9, 10, 10, 11, 11, 1, 1, 12, 13, 14, 18, 15, 1, 16, 1, 17, 1]) (bs := [16, 1]) (W := 1648) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1662_2 : P.sumLeaves 24 1702208 64 = 1648 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26597) rows (by decide) (by decide)).symm.trans contract1662_2

theorem c1662_3 : P.sumLeaves 24 1702272 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1662) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1662 (by decide)
  decide +kernel

theorem contract1662_4 : P.leaf 30 26599 = 19194 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26599) (ss := [(27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 19, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 12, 13, 18, 14, 1, 15, 1, 16, 17]) (bs := [16, 1]) (W := 19194) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1662_4 : P.sumLeaves 24 1702336 64 = 19194 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26599) rows (by decide) (by decide)).symm.trans contract1662_4

theorem c1662_5 : P.sumLeaves 24 1702400 512 = 1733029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1662) (lo := 512) (len := 512) (W := 1733029) check rows elimOK (by decide) (by decide) cover1662 (by decide)
  decide +kernel

theorem h1662 : P.leaf 34 1662 = 1754133 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 262), (64, 1648), (64, 0), (64, 19194), (512, 1733029)]) (.cons c1662_0 (.cons c1662_1 (.cons c1662_2 (.cons c1662_3 (.cons c1662_4 (.cons c1662_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1485, 48), (1486, 48), (1487, 48), (1494, 24), (1495, 24), (1500, 48), (1501, 48), (1502, 48), (1503, 48), (1516, 24), (1517, 24), (1518, 48), (1519, 48), (1534, 24), (1535, 24), (1590, 24), (1591, 24), (1596, 24), (1597, 24), (1598, 24), (1599, 24), (1622, 8), (1623, 8), (1628, 24), (1629, 24), (1630, 24), (1631, 24), (1644, 24), (1645, 24), (1646, 48), (1647, 48), (1662, 24)]

theorem segOK : checkSeg 16 perms 1485 1663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1485 1663 1000 5165702064 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5165702064)
    (SegSum.cons (w := 48) h1485 (SegSum.cons (w := 48) h1486 (SegSum.cons (w := 48) h1487 (SegSum.cons (w := 24) h1494 (SegSum.cons (w := 24) h1495 (SegSum.cons (w := 48) h1500 (SegSum.cons (w := 48) h1501 (SegSum.cons (w := 48) h1502 (SegSum.cons (w := 48) h1503 (SegSum.cons (w := 24) h1516 (SegSum.cons (w := 24) h1517 (SegSum.cons (w := 48) h1518 (SegSum.cons (w := 48) h1519 (SegSum.cons (w := 24) h1534 (SegSum.cons (w := 24) h1535 (SegSum.cons (w := 24) h1590 (SegSum.cons (w := 24) h1591 (SegSum.cons (w := 24) h1596 (SegSum.cons (w := 24) h1597 (SegSum.cons (w := 24) h1598 (SegSum.cons (w := 24) h1599 (SegSum.cons (w := 8) h1622 (SegSum.cons (w := 8) h1623 (SegSum.cons (w := 24) h1628 (SegSum.cons (w := 24) h1629 (SegSum.cons (w := 24) h1630 (SegSum.cons (w := 24) h1631 (SegSum.cons (w := 24) h1644 (SegSum.cons (w := 24) h1645 (SegSum.cons (w := 48) h1646 (SegSum.cons (w := 48) h1647 (SegSum.cons (w := 24) h1662 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S11
