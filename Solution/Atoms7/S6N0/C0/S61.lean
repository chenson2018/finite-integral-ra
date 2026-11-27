/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S61

open RACert RACert.Problem

theorem cover81919 : P.CoversSplit 26 10 81919 0xfffffffafffffafafffffffafffffafafffffffafffcfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafafffcfac8aaaaaaaaaa88aa88fffffffafffffafafffffffafffffafafffffffaffccfac8aaaaaaaaaa88aa88fffffafafffffafaaaaaaaaaaaaaaaaafffffafaffccfac8aaaaaaaaaa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81919_0 : P.sumLeaves 26 83885056 167 = 8002064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 0) (len := 167) (W := 8002064) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_1 : P.sumLeaves 26 83885223 152 = 74796937 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 167) (len := 152) (W := 74796937) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_2 : P.sumLeaves 26 83885375 115 = 316473816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 319) (len := 115) (W := 316473816) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_3 : P.sumLeaves 26 83885490 135 = 485507092 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 434) (len := 135) (W := 485507092) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_4 : P.sumLeaves 26 83885625 148 = 473502008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 569) (len := 148) (W := 473502008) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_5 : P.sumLeaves 26 83885773 145 = 572367184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 717) (len := 145) (W := 572367184) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_6 : P.sumLeaves 26 83885918 107 = 847654898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 862) (len := 107) (W := 847654898) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem c81919_7 : P.sumLeaves 26 83886025 55 = 653226024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81919) (lo := 969) (len := 55) (W := 653226024) check rows elimOK (by decide) (by decide) cover81919 (by decide)
  decide +kernel

theorem h81919 : P.leaf 36 81919 = 3431530023 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(167, 8002064), (152, 74796937), (115, 316473816), (135, 485507092), (148, 473502008), (145, 572367184), (107, 847654898), (55, 653226024)]) (.cons c81919_0 (.cons c81919_1 (.cons c81919_2 (.cons c81919_3 (.cons c81919_4 (.cons c81919_5 (.cons c81919_6 (.cons c81919_7 (.nil))))))))) (by decide) (by decide))

theorem cover88517 : P.CoversSplit 26 10 88517 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88517_0 : P.sumLeaves 26 90641408 1024 = 34448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88517) (lo := 0) (len := 1024) (W := 34448) check rows elimOK (by decide) (by decide) cover88517 (by decide)
  decide +kernel

theorem h88517 : P.leaf 36 88517 = 34448 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34448)]) (.cons c88517_0 (.nil)) (by decide) (by decide))

theorem cover88519 : P.CoversSplit 26 10 88519 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88519_0 : P.sumLeaves 26 90643456 1024 = 343632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88519) (lo := 0) (len := 1024) (W := 343632) check rows elimOK (by decide) (by decide) cover88519 (by decide)
  decide +kernel

theorem h88519 : P.leaf 36 88519 = 343632 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 343632)]) (.cons c88519_0 (.nil)) (by decide) (by decide))

theorem cover88525 : P.CoversSplit 26 10 88525 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88525_0 : P.sumLeaves 26 90649600 1024 = 70088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88525) (lo := 0) (len := 1024) (W := 70088) check rows elimOK (by decide) (by decide) cover88525 (by decide)
  decide +kernel

theorem h88525 : P.leaf 36 88525 = 70088 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 70088)]) (.cons c88525_0 (.nil)) (by decide) (by decide))

theorem cover88527 : P.CoversSplit 26 10 88527 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88527_0 : P.sumLeaves 26 90651648 1024 = 377552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88527) (lo := 0) (len := 1024) (W := 377552) check rows elimOK (by decide) (by decide) cover88527 (by decide)
  decide +kernel

theorem h88527 : P.leaf 36 88527 = 377552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 377552)]) (.cons c88527_0 (.nil)) (by decide) (by decide))

theorem cover88534 : P.CoversSplit 26 10 88534 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88534_0 : P.sumLeaves 26 90658816 1024 = 3278990 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88534) (lo := 0) (len := 1024) (W := 3278990) check rows elimOK (by decide) (by decide) cover88534 (by decide)
  decide +kernel

theorem h88534 : P.leaf 36 88534 = 3278990 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3278990)]) (.cons c88534_0 (.nil)) (by decide) (by decide))

theorem cover88535 : P.CoversSplit 26 10 88535 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88535_0 : P.sumLeaves 26 90659840 1024 = 3978058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88535) (lo := 0) (len := 1024) (W := 3978058) check rows elimOK (by decide) (by decide) cover88535 (by decide)
  decide +kernel

theorem h88535 : P.leaf 36 88535 = 3978058 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3978058)]) (.cons c88535_0 (.nil)) (by decide) (by decide))

theorem cover88540 : P.CoversSplit 26 10 88540 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88540_0 : P.sumLeaves 26 90664960 1024 = 500960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88540) (lo := 0) (len := 1024) (W := 500960) check rows elimOK (by decide) (by decide) cover88540 (by decide)
  decide +kernel

theorem h88540 : P.leaf 36 88540 = 500960 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 500960)]) (.cons c88540_0 (.nil)) (by decide) (by decide))

theorem cover88541 : P.CoversSplit 26 10 88541 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88541_0 : P.sumLeaves 26 90665984 1024 = 667612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88541) (lo := 0) (len := 1024) (W := 667612) check rows elimOK (by decide) (by decide) cover88541 (by decide)
  decide +kernel

theorem h88541 : P.leaf 36 88541 = 667612 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 667612)]) (.cons c88541_0 (.nil)) (by decide) (by decide))

theorem cover88542 : P.CoversSplit 26 10 88542 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88542_0 : P.sumLeaves 26 90667008 1024 = 4881826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88542) (lo := 0) (len := 1024) (W := 4881826) check rows elimOK (by decide) (by decide) cover88542 (by decide)
  decide +kernel

theorem h88542 : P.leaf 36 88542 = 4881826 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4881826)]) (.cons c88542_0 (.nil)) (by decide) (by decide))

theorem cover88543 : P.CoversSplit 26 10 88543 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88543_0 : P.sumLeaves 26 90668032 1024 = 5697700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88543) (lo := 0) (len := 1024) (W := 5697700) check rows elimOK (by decide) (by decide) cover88543 (by decide)
  decide +kernel

theorem h88543 : P.leaf 36 88543 = 5697700 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5697700)]) (.cons c88543_0 (.nil)) (by decide) (by decide))

theorem cover88557 : P.CoversSplit 26 10 88557 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88557_0 : P.sumLeaves 26 90682368 1024 = 139936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88557) (lo := 0) (len := 1024) (W := 139936) check rows elimOK (by decide) (by decide) cover88557 (by decide)
  decide +kernel

theorem h88557 : P.leaf 36 88557 = 139936 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 139936)]) (.cons c88557_0 (.nil)) (by decide) (by decide))

theorem cover88558 : P.CoversSplit 26 10 88558 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88558_0 : P.sumLeaves 26 90683392 1024 = 691008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88558) (lo := 0) (len := 1024) (W := 691008) check rows elimOK (by decide) (by decide) cover88558 (by decide)
  decide +kernel

theorem h88558 : P.leaf 36 88558 = 691008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 691008)]) (.cons c88558_0 (.nil)) (by decide) (by decide))

theorem cover88559 : P.CoversSplit 26 10 88559 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88559_0 : P.sumLeaves 26 90684416 1024 = 737336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88559) (lo := 0) (len := 1024) (W := 737336) check rows elimOK (by decide) (by decide) cover88559 (by decide)
  decide +kernel

theorem h88559 : P.leaf 36 88559 = 737336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 737336)]) (.cons c88559_0 (.nil)) (by decide) (by decide))

theorem cover88574 : P.CoversSplit 26 10 88574 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88574_0 : P.sumLeaves 26 90699776 1024 = 8794202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88574) (lo := 0) (len := 1024) (W := 8794202) check rows elimOK (by decide) (by decide) cover88574 (by decide)
  decide +kernel

theorem h88574 : P.leaf 36 88574 = 8794202 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8794202)]) (.cons c88574_0 (.nil)) (by decide) (by decide))

theorem cover88575 : P.CoversSplit 26 10 88575 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88575_0 : P.sumLeaves 26 90700800 1024 = 9370534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88575) (lo := 0) (len := 1024) (W := 9370534) check rows elimOK (by decide) (by decide) cover88575 (by decide)
  decide +kernel

theorem h88575 : P.leaf 36 88575 = 9370534 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9370534)]) (.cons c88575_0 (.nil)) (by decide) (by decide))

theorem cover88662 : P.CoversSplit 26 10 88662 0x8800000088020401000000000000000000000000000000000000000000000000000004000000040100000000000000000000000000000000000000000000000000000000002200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88662_0 : P.sumLeaves 26 90789888 1024 = 519156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88662) (lo := 0) (len := 1024) (W := 519156) check rows elimOK (by decide) (by decide) cover88662 (by decide)
  decide +kernel

theorem h88662 : P.leaf 36 88662 = 519156 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 519156)]) (.cons c88662_0 (.nil)) (by decide) (by decide))

theorem cover88663 : P.CoversSplit 26 10 88663 0x8800000088020401000000000000000000000000000000000000000000000000000004000000040100000000000000000000000000000000000000000000000000000000002200010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88663_0 : P.sumLeaves 26 90790912 1024 = 1106101 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88663) (lo := 0) (len := 1024) (W := 1106101) check rows elimOK (by decide) (by decide) cover88663 (by decide)
  decide +kernel

theorem h88663 : P.leaf 36 88663 = 1106101 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1106101)]) (.cons c88663_0 (.nil)) (by decide) (by decide))

theorem cover88670 : P.CoversSplit 26 10 88670 0xaaaa0000aaa80504000000000000000000000000000000000000000000000500000005050000050400000000000000000000000000000000000000000000000000000000aa8805040000000000000000000000008800040000000000000004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88670_0 : P.sumLeaves 26 90798080 1024 = 1626096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88670) (lo := 0) (len := 1024) (W := 1626096) check rows elimOK (by decide) (by decide) cover88670 (by decide)
  decide +kernel

theorem h88670 : P.leaf 36 88670 = 1626096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1626096)]) (.cons c88670_0 (.nil)) (by decide) (by decide))

theorem cover88671 : P.CoversSplit 26 10 88671 0xaaaa0000aaa80504000000000000000000000000000000000000000000000500000005050000050400000000000000000000000000000000000000000000000000000000aa8805040000000000000000000000008800040000000000000004000000000000000504000000000000000000000000000004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88671_0 : P.sumLeaves 26 90799104 1024 = 3458642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88671) (lo := 0) (len := 1024) (W := 3458642) check rows elimOK (by decide) (by decide) cover88671 (by decide)
  decide +kernel

theorem h88671 : P.leaf 36 88671 = 3458642 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3458642)]) (.cons c88671_0 (.nil)) (by decide) (by decide))

theorem cover88702 : P.CoversSplit 26 10 88702 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080a0a0a0a0a080a080000000000000000000000000a080a0800000000ffccfac8000000000000000000000000ccccc8c8000000000c0c08080000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 874, 922, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c88702_0 : P.sumLeaves 26 90830848 969 = 1767998 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88702) (lo := 0) (len := 969) (W := 1767998) check rows elimOK (by decide) (by decide) cover88702 (by decide)
  decide +kernel

theorem c88702_1 : P.sumLeaves 26 90831817 55 = 5016886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88702) (lo := 969) (len := 55) (W := 5016886) check rows elimOK (by decide) (by decide) cover88702 (by decide)
  decide +kernel

theorem h88702 : P.leaf 36 88702 = 6784884 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(969, 1767998), (55, 5016886)]) (.cons c88702_0 (.cons c88702_1 (.nil))) (by decide) (by decide))

theorem cover88703 : P.CoversSplit 26 10 88703 0xfffffffffffcfaf800000000000000000000000000000000000000000f0c0a080f0f0a0a0f0c0a080a0a0a0a0a080a080000000000000000000000000a080a0800000000ffccfac8000000000000000000000000ccccc8c8000000000c0c0808000000000f0c0a08000000000a080a08000000000c0c08080000000008080808 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 922, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c88703_0 : P.sumLeaves 26 90831872 739 = 2199396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88703) (lo := 0) (len := 739) (W := 2199396) check rows elimOK (by decide) (by decide) cover88703 (by decide)
  decide +kernel

theorem c88703_1 : P.sumLeaves 26 90832611 285 = 12015900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88703) (lo := 739) (len := 285) (W := 12015900) check rows elimOK (by decide) (by decide) cover88703 (by decide)
  decide +kernel

theorem h88703 : P.leaf 36 88703 = 14215296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(739, 2199396), (285, 12015900)]) (.cons c88703_0 (.cons c88703_1 (.nil))) (by decide) (by decide))

theorem cover88770 : P.CoversSplit 26 10 88770 0x8000000080000000c0000000c000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 524, 530, 587, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c88770_0 : P.sumLeaves 26 90900480 1024 = 2401 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88770) (lo := 0) (len := 1024) (W := 2401) check rows elimOK (by decide) (by decide) cover88770 (by decide)
  decide +kernel

theorem h88770 : P.leaf 36 88770 = 2401 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2401)]) (.cons c88770_0 (.nil)) (by decide) (by decide))

theorem cover88771 : P.CoversSplit 26 10 88771 0x8000000080000000800000008000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000200001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c88771_0 : P.sumLeaves 26 90901504 1024 = 98125 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88771) (lo := 0) (len := 1024) (W := 98125) check rows elimOK (by decide) (by decide) cover88771 (by decide)
  decide +kernel

theorem h88771 : P.leaf 36 88771 = 98125 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 98125)]) (.cons c88771_0 (.nil)) (by decide) (by decide))

theorem cover88775 : P.CoversSplit 26 10 88775 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 922, 972, 979, 1266, 1315]) (by decide +kernel)

theorem c88775_0 : P.sumLeaves 26 90905600 1024 = 1334330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88775) (lo := 0) (len := 1024) (W := 1334330) check rows elimOK (by decide) (by decide) cover88775 (by decide)
  decide +kernel

theorem h88775 : P.leaf 36 88775 = 1334330 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1334330)]) (.cons c88775_0 (.nil)) (by decide) (by decide))

theorem cover88778 : P.CoversSplit 26 10 88778 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 530, 874, 922, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c88778_0 : P.sumLeaves 26 90908672 1024 = 56868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88778) (lo := 0) (len := 1024) (W := 56868) check rows elimOK (by decide) (by decide) cover88778 (by decide)
  decide +kernel

theorem h88778 : P.leaf 36 88778 = 56868 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 56868)]) (.cons c88778_0 (.nil)) (by decide) (by decide))

theorem cover88779 : P.CoversSplit 26 10 88779 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000020200000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 972, 979, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c88779_0 : P.sumLeaves 26 90909696 1024 = 678592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88779) (lo := 0) (len := 1024) (W := 678592) check rows elimOK (by decide) (by decide) cover88779 (by decide)
  decide +kernel

theorem h88779 : P.leaf 36 88779 = 678592 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 678592)]) (.cons c88779_0 (.nil)) (by decide) (by decide))

theorem cover88782 : P.CoversSplit 26 10 88782 0xffff0000fffc0504ffff0000fffc050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330001000000000033000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 530, 874, 922, 972, 979, 1266, 1315, 1665]) (by decide +kernel)

theorem c88782_0 : P.sumLeaves 26 90912768 1024 = 614326 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88782) (lo := 0) (len := 1024) (W := 614326) check rows elimOK (by decide) (by decide) cover88782 (by decide)
  decide +kernel

theorem h88782 : P.leaf 36 88782 = 614326 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 614326)]) (.cons c88782_0 (.nil)) (by decide) (by decide))

theorem cover88783 : P.CoversSplit 26 10 88783 0xffff0000fffc0504ffff0000fffc050000000000000000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000330001000000000033000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c88783_0 : P.sumLeaves 26 90913792 1024 = 5398116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88783) (lo := 0) (len := 1024) (W := 5398116) check rows elimOK (by decide) (by decide) cover88783 (by decide)
  decide +kernel

theorem h88783 : P.leaf 36 88783 = 5398116 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5398116)]) (.cons c88783_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(81919, 180), (88517, 360), (88519, 360), (88525, 720), (88527, 360), (88534, 180), (88535, 360), (88540, 720), (88541, 720), (88542, 720), (88543, 720), (88557, 360), (88558, 720), (88559, 720), (88574, 360), (88575, 360), (88662, 120), (88663, 120), (88670, 360), (88671, 360), (88702, 360), (88703, 360), (88770, 120), (88771, 720), (88775, 720), (88778, 720), (88779, 720), (88782, 720), (88783, 720)]

theorem segOK : checkSeg 20 perms 81919 88788 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81919 88788 14040 651572680740 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 651572680740)
    (SegSum.cons (w := 180) h81919 (SegSum.cons (w := 360) h88517 (SegSum.cons (w := 360) h88519 (SegSum.cons (w := 720) h88525 (SegSum.cons (w := 360) h88527 (SegSum.cons (w := 180) h88534 (SegSum.cons (w := 360) h88535 (SegSum.cons (w := 720) h88540 (SegSum.cons (w := 720) h88541 (SegSum.cons (w := 720) h88542 (SegSum.cons (w := 720) h88543 (SegSum.cons (w := 360) h88557 (SegSum.cons (w := 720) h88558 (SegSum.cons (w := 720) h88559 (SegSum.cons (w := 360) h88574 (SegSum.cons (w := 360) h88575 (SegSum.cons (w := 120) h88662 (SegSum.cons (w := 120) h88663 (SegSum.cons (w := 360) h88670 (SegSum.cons (w := 360) h88671 (SegSum.cons (w := 360) h88702 (SegSum.cons (w := 360) h88703 (SegSum.cons (w := 120) h88770 (SegSum.cons (w := 720) h88771 (SegSum.cons (w := 720) h88775 (SegSum.cons (w := 720) h88778 (SegSum.cons (w := 720) h88779 (SegSum.cons (w := 720) h88782 (SegSum.cons (w := 720) h88783 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S61
