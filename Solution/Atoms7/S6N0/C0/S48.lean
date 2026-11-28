/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S48

open RACert RACert.Problem

theorem cover101755 : P.CoversSplit 26 10 101755 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101755 : P.leaf 36 101755 = 6425864 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 101755) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 101755) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101755) (weight := rowWeight keep12 twice12) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101755 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79774 : P.leaf 36 79774 = 6425864 :=
  orient72 (v := 101755) (by decide) (by decide +kernel) h101755

theorem cover101759 : P.CoversSplit 26 10 101759 0xffffffff00000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 629, 636, 922, 930, 965, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c101759_0 : P.sumLeaves 26 104201216 1024 = 19969964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 101759) (lo := 0) (len := 1024) (W := 19969964) check rows elimOK (by decide) (by decide) cover101759 (by decide)
  decide +kernel

theorem h101759 : P.leaf 36 101759 = 19969964 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19969964)]) (.cons c101759_0 (.nil)) (by decide) (by decide))

theorem h79775 : P.leaf 36 79775 = 19969964 :=
  orient72 (v := 101759) (by decide) (by decide +kernel) h101759

theorem cover80787 : P.CoversSplit 26 10 80787 0xc000000000000000c0000000000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 608, 930, 972, 979, 1315]) (by decide +kernel)

theorem h80787 : P.leaf 36 80787 = 998592 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80787) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80787) (weight := fun _ => 1) (xs := [683, 746, 747, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80787 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79781 : P.leaf 36 79781 = 998592 :=
  orient4 (v := 80787) (by decide) (by decide +kernel) h80787

theorem cover101843 : P.CoversSplit 26 10 101843 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 608, 629, 636, 881, 930, 965, 1273, 1322]) (by decide +kernel)

theorem h101843 : P.leaf 36 101843 = 452608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101843) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101843) (weight := fun _ => 1) (xs := [1007, 1023]) check rows elimOK (by decide) (by decide) cover101843 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79782 : P.leaf 36 79782 = 452608 :=
  orient72 (v := 101843) (by decide) (by decide +kernel) h101843

theorem cover101847 : P.CoversSplit 26 10 101847 0xcc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 881, 922, 930, 965, 1273, 1315, 1658]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h101847 : P.leaf 36 101847 = 3238208 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101847) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101847) (weight := fun _ => 1) (xs := [1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover101847 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79783 : P.leaf 36 79783 = 3238208 :=
  orient72 (v := 101847) (by decide) (by decide +kernel) h101847

theorem cover563411 : P.CoversSplit 26 10 563411 0x8080000000000000000000000000000000000000000000000000000000000000808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 587, 636, 965, 1265, 1273]) (by decide +kernel)

theorem h563411 : P.leaf 36 563411 = 110080 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 563411) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 563411) (weight := fun _ => 1) (xs := [759, 767, 1015, 1023]) check rows elimOK (by decide) (by decide) cover563411 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79784 : P.leaf 36 79784 = 110080 :=
  orient324 (v := 563411) (by decide) (by decide +kernel) h563411

theorem cover80793 : P.CoversSplit 26 10 80793 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem h80793 : P.leaf 36 80793 = 1756768 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80793) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80793) (weight := fun _ => 1) (xs := [948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80793 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79785 : P.leaf 36 79785 = 1756768 :=
  orient4 (v := 80793) (by decide) (by decide +kernel) h80793

theorem cover101849 : P.CoversSplit 26 10 101849 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 580, 629, 636, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101849 : P.leaf 36 101849 = 1082752 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101849) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101849) (weight := fun _ => 1) (xs := [997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101849 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79786 : P.leaf 36 79786 = 1082752 :=
  orient72 (v := 101849) (by decide) (by decide +kernel) h101849

theorem cover80797 : P.CoversSplit 26 10 80797 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem h80797 : P.leaf 36 80797 = 6799904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80797) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80797) (weight := fun _ => 1) (xs := [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80797 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79787 : P.leaf 36 79787 = 6799904 :=
  orient4 (v := 80797) (by decide) (by decide +kernel) h80797

theorem cover101850 : P.CoversSplit 26 10 101850 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 531, 629, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101850 : P.leaf 36 101850 = 1338368 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101850) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101850) (weight := fun _ => 1) (xs := [997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101850 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79788 : P.leaf 36 79788 = 1338368 :=
  orient72 (v := 101850) (by decide) (by decide +kernel) h101850

theorem cover80795 : P.CoversSplit 26 10 80795 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem h80795 : P.leaf 36 80795 = 6660816 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80795) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80795) (weight := fun _ => 1) (xs := [736, 738, 744, 746, 948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80795 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79789 : P.leaf 36 79789 = 6660816 :=
  orient4 (v := 80795) (by decide) (by decide +kernel) h80795

theorem cover101851 : P.CoversSplit 26 10 101851 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101851 : P.leaf 36 101851 = 4072188 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101851) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101851) (weight := fun _ => 1) (xs := [997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101851 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79790 : P.leaf 36 79790 = 4072188 :=
  orient72 (v := 101851) (by decide) (by decide +kernel) h101851

theorem cover101855 : P.CoversSplit 26 10 101855 0xffffffff00000000000000000000000000000000000000000000000000000000000000000000000055550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem c101855_0 : P.sumLeaves 26 104299520 1024 = 17948714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 101855) (lo := 0) (len := 1024) (W := 17948714) check rows elimOK (by decide) (by decide) cover101855 (by decide)
  decide +kernel

theorem h101855 : P.leaf 36 101855 = 17948714 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17948714)]) (.cons c101855_0 (.nil)) (by decide) (by decide))

theorem h79791 : P.leaf 36 79791 = 17948714 :=
  orient72 (v := 101855) (by decide) (by decide +kernel) h101855

theorem cover101875 : P.CoversSplit 26 10 101875 0x8800880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 881, 930, 965, 1273, 1322]) (by decide +kernel)

theorem h101875 : P.leaf 36 101875 = 3188480 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101875) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101875) (weight := fun _ => 1) (xs := [1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover101875 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79798 : P.leaf 36 79798 = 3188480 :=
  orient72 (v := 101875) (by decide) (by decide +kernel) h101875

theorem cover101879 : P.CoversSplit 26 10 101879 0xcc00cc0000000000000000000000000000000000000000000000000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 881, 922, 930, 965, 1273, 1315, 1658]) (by decide +kernel)

theorem h101879 : P.leaf 36 101879 = 17343352 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101879) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101879) (weight := fun _ => 1) (xs := [762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover101879 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79799 : P.leaf 36 79799 = 17343352 :=
  orient72 (v := 101879) (by decide) (by decide +kernel) h101879

theorem cover102227 : P.CoversSplit 26 10 102227 0xaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 881, 923, 929, 1658]) (by decide +kernel)

theorem h102227 : P.leaf 36 102227 = 509008 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 102227) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 102227) (weight := fun _ => 1) (xs := [505, 507, 509, 511, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover102227 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79800 : P.leaf 36 79800 = 509008 :=
  orient84 (v := 102227) (by decide) (by decide +kernel) h102227

theorem cover102231 : P.CoversSplit 26 10 102231 0xaa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 881, 923, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem h102231 : P.leaf 36 102231 = 8269536 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 102231) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 102231) (weight := fun _ => 1) (xs := [489, 491, 493, 495, 505, 507, 509, 511, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover102231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79801 : P.leaf 36 79801 = 8269536 :=
  orient84 (v := 102231) (by decide) (by decide +kernel) h102231

theorem cover101881 : P.CoversSplit 26 10 101881 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 580, 629, 636, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101881 : P.leaf 36 101881 = 7144416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101881) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101881) (weight := fun _ => 1) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101881 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79802 : P.leaf 36 79802 = 7144416 :=
  orient72 (v := 101881) (by decide) (by decide +kernel) h101881

theorem cover79803 : P.CoversSplit 26 10 79803 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79803_0 : P.sumLeaves 26 81718272 1024 = 26333016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79803) (lo := 0) (len := 1024) (W := 26333016) check rows elimOK (by decide) (by decide) cover79803 (by decide)
  decide +kernel

theorem h79803 : P.leaf 36 79803 = 26333016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26333016)]) (.cons c79803_0 (.nil)) (by decide) (by decide))

theorem cover101882 : P.CoversSplit 26 10 101882 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 881, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101882 : P.leaf 36 101882 = 9625652 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101882) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101882) (weight := fun _ => 1) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101882 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79804 : P.leaf 36 79804 = 9625652 :=
  orient72 (v := 101882) (by decide) (by decide +kernel) h101882

theorem cover80827 : P.CoversSplit 26 10 80827 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c80827_0 : P.sumLeaves 26 82766848 1024 = 30829228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 80827) (lo := 0) (len := 1024) (W := 30829228) check rows elimOK (by decide) (by decide) cover80827 (by decide)
  decide +kernel

theorem h80827 : P.leaf 36 80827 = 30829228 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30829228)]) (.cons c80827_0 (.nil)) (by decide) (by decide))

theorem h79805 : P.leaf 36 79805 = 30829228 :=
  orient4 (v := 80827) (by decide) (by decide +kernel) h80827

theorem cover101883 : P.CoversSplit 26 10 101883 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101883 : P.leaf 36 101883 = 34132756 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101883) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101883) (weight := fun _ => 1) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101883 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79806 : P.leaf 36 79806 = 34132756 :=
  orient72 (v := 101883) (by decide) (by decide +kernel) h101883

theorem cover101887 : P.CoversSplit 26 10 101887 0xffffffff00000000000000000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c101887_0 : P.sumLeaves 26 104332288 1024 = 109033368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 101887) (lo := 0) (len := 1024) (W := 109033368) check rows elimOK (by decide) (by decide) cover101887 (by decide)
  decide +kernel

theorem h101887 : P.leaf 36 101887 = 109033368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 109033368)]) (.cons c101887_0 (.nil)) (by decide) (by decide))

theorem h79807 : P.leaf 36 79807 = 109033368 :=
  orient72 (v := 101887) (by decide) (by decide +kernel) h101887

theorem cover564115 : P.CoversSplit 26 10 564115 0x8888000000000000000000000000000000000000000000000000000000000000888800000000000000000000000000000000000000000000000000000000000088880000000000000000000000000000000000000000000000000000000000008888000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 531, 537, 538, 922, 923, 929, 930, 1265, 1273]) (by decide +kernel)

theorem h564115 : P.leaf 36 564115 = 1556208 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 564115) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 564115) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 564115) (weight := rowWeight keep0 twice0) (xs := [243, 247, 251, 255, 499, 503, 507, 511, 755, 759, 763, 767, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover564115 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79817 : P.leaf 36 79817 = 1556208 :=
  orient324 (v := 564115) (by decide) (by decide +kernel) h564115

theorem cover276951 : P.CoversSplit 26 10 276951 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220020002200200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 929, 930, 972, 1265, 1273, 1308, 1658, 1665]) (by decide +kernel)

theorem h276951 : P.leaf 36 276951 = 7604614 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276951) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276951) (weight := fun _ => 1) (xs := [453, 465, 469, 485, 497, 501, 969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover276951 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79819 : P.leaf 36 79819 = 7604614 :=
  orient74 (v := 276951) (by decide) (by decide +kernel) h276951

theorem cover307667 : P.CoversSplit 26 10 307667 0xaa000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 872, 930, 1265, 1665]) (by decide +kernel)

theorem h307667 : P.leaf 36 307667 = 3170184 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 307667) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 307667) (weight := fun _ => 1) (xs := [465, 469, 497, 501, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover307667 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79820 : P.leaf 36 79820 = 3170184 :=
  orient80 (v := 307667) (by decide) (by decide +kernel) h307667

theorem cover307671 : P.CoversSplit 26 10 307671 0xaa000000aa000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000022000000220000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 872, 930, 1265, 1273, 1308, 1658, 1665]) (by decide +kernel)

theorem h307671 : P.leaf 36 307671 = 13245172 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 307671) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 307671) (weight := fun _ => 1) (xs := [209, 213, 241, 245, 465, 469, 497, 501, 729, 731, 733, 735, 761, 763, 765, 767, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover307671 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79821 : P.leaf 36 79821 = 13245172 :=
  orient80 (v := 307671) (by decide) (by decide +kernel) h307671

theorem cover276955 : P.CoversSplit 26 10 276955 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 923, 979, 1273, 1308, 1658, 1665]) (by decide +kernel)

theorem h276955 : P.leaf 36 276955 = 9078756 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276955) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276955) (weight := fun _ => 1) (xs := [465, 469, 497, 501, 977, 979, 981, 983, 985, 987, 989, 991, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover276955 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79822 : P.leaf 36 79822 = 9078756 :=
  orient74 (v := 276955) (by decide) (by decide +kernel) h276955

theorem cover276959 : P.CoversSplit 26 10 276959 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220022002200220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 923, 972, 979, 1265, 1273, 1308, 1658, 1665]) (by decide +kernel)

theorem c276959_0 : P.sumLeaves 26 283606016 1024 = 42587384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276959) (lo := 0) (len := 1024) (W := 42587384) check rows elimOK (by decide) (by decide) cover276959 (by decide)
  decide +kernel

theorem h276959 : P.leaf 36 276959 = 42587384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42587384)]) (.cons c276959_0 (.nil)) (by decide) (by decide))

theorem h79823 : P.leaf 36 79823 = 42587384 :=
  orient74 (v := 276959) (by decide) (by decide +kernel) h276959

theorem cover276983 : P.CoversSplit 26 10 276983 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330030003300300000000000000000003300300000000000110000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 929, 930, 972, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c276983_0 : P.sumLeaves 26 283630592 1024 = 25876290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276983) (lo := 0) (len := 1024) (W := 25876290) check rows elimOK (by decide) (by decide) cover276983 (by decide)
  decide +kernel

theorem h276983 : P.leaf 36 276983 = 25876290 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25876290)]) (.cons c276983_0 (.nil)) (by decide) (by decide))

theorem h79835 : P.leaf 36 79835 = 25876290 :=
  orient74 (v := 276983) (by decide) (by decide +kernel) h276983

theorem cover276986 : P.CoversSplit 26 10 276986 0xfffffffafffffffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 629, 636, 867, 923, 972, 1265, 1658]) (by decide +kernel)

theorem c276986_0 : P.sumLeaves 26 283633664 1024 = 34325966 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276986) (lo := 0) (len := 1024) (W := 34325966) check rows elimOK (by decide) (by decide) cover276986 (by decide)
  decide +kernel

theorem h276986 : P.leaf 36 276986 = 34325966 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34325966)]) (.cons c276986_0 (.nil)) (by decide) (by decide))

theorem h79836 : P.leaf 36 79836 = 34325966 :=
  orient74 (v := 276986) (by decide) (by decide +kernel) h276986

theorem cover276990 : P.CoversSplit 26 10 276990 0xfffffffafffffffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330032003300320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 867, 923, 972, 1265, 1658, 1665]) (by decide +kernel)

theorem c276990_0 : P.sumLeaves 26 283637760 1024 = 83009512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276990) (lo := 0) (len := 1024) (W := 83009512) check rows elimOK (by decide) (by decide) cover276990 (by decide)
  decide +kernel

theorem h276990 : P.leaf 36 276990 = 83009512 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 83009512)]) (.cons c276990_0 (.nil)) (by decide) (by decide))

theorem h79837 : P.leaf 36 79837 = 83009512 :=
  orient74 (v := 276990) (by decide) (by decide +kernel) h276990

def seg : List (ℕ × ℕ) := [(79774, 360), (79775, 720), (79781, 360), (79782, 720), (79783, 720), (79784, 720), (79785, 720), (79786, 720), (79787, 720), (79788, 720), (79789, 720), (79790, 720), (79791, 720), (79798, 360), (79799, 360), (79800, 720), (79801, 720), (79802, 720), (79803, 720), (79804, 720), (79805, 720), (79806, 720), (79807, 720), (79817, 360), (79819, 720), (79820, 720), (79821, 720), (79822, 720), (79823, 720), (79835, 360), (79836, 720), (79837, 720)]

theorem segOK : checkSeg 20 perms 79774 79838 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79774 79838 20880 367216798320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 367216798320)
    (SegSum.cons (w := 360) h79774 (SegSum.cons (w := 720) h79775 (SegSum.cons (w := 360) h79781 (SegSum.cons (w := 720) h79782 (SegSum.cons (w := 720) h79783 (SegSum.cons (w := 720) h79784 (SegSum.cons (w := 720) h79785 (SegSum.cons (w := 720) h79786 (SegSum.cons (w := 720) h79787 (SegSum.cons (w := 720) h79788 (SegSum.cons (w := 720) h79789 (SegSum.cons (w := 720) h79790 (SegSum.cons (w := 720) h79791 (SegSum.cons (w := 360) h79798 (SegSum.cons (w := 360) h79799 (SegSum.cons (w := 720) h79800 (SegSum.cons (w := 720) h79801 (SegSum.cons (w := 720) h79802 (SegSum.cons (w := 720) h79803 (SegSum.cons (w := 720) h79804 (SegSum.cons (w := 720) h79805 (SegSum.cons (w := 720) h79806 (SegSum.cons (w := 720) h79807 (SegSum.cons (w := 360) h79817 (SegSum.cons (w := 720) h79819 (SegSum.cons (w := 720) h79820 (SegSum.cons (w := 720) h79821 (SegSum.cons (w := 720) h79822 (SegSum.cons (w := 720) h79823 (SegSum.cons (w := 360) h79835 (SegSum.cons (w := 720) h79836 (SegSum.cons (w := 720) h79837 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S48
