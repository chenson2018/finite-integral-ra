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

namespace RACert.S6N0.C0.S54

open RACert RACert.Problem

theorem cover276275 : P.CoversSplit 26 10 276275 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 972, 1273]) (by decide +kernel)

theorem h276275 : P.leaf 36 276275 = 1393400 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276275) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276275) (weight := fun _ => 1) (xs := [170, 511, 682, 1023]) check rows elimOK (by decide) (by decide) cover276275 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88793 : P.leaf 36 88793 = 1393400 :=
  orient6 (v := 276275) (by decide) (by decide +kernel) h276275

theorem cover111075 : P.CoversSplit 26 10 111075 0x8800000088000000880000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 1266, 1273, 1315]) (by decide +kernel)

theorem h111075 : P.leaf 36 111075 = 1917528 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 111075) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 111075) (weight := fun _ => 1) (xs := [923, 927, 955, 959, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover111075 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88794 : P.leaf 36 88794 = 1917528 :=
  orient86 (v := 111075) (by decide) (by decide +kernel) h111075

theorem cover276279 : P.CoversSplit 26 10 276279 0xcc000400000000000000000000000000000000000000000000000000000000004400000000000000040000000000000000000000000000000000000000000000cc000400000000000000000000000000000000000000000000000000000000004400000000000000040000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 1265, 1273, 1658]) (by decide +kernel)

theorem h276279 : P.leaf 36 276279 = 9001884 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276279) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276279) (weight := fun _ => 1) (xs := [186, 250, 254, 490, 506, 507, 510, 511, 698, 762, 766, 1002, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276279 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88795 : P.leaf 36 88795 = 9001884 :=
  orient6 (v := 276279) (by decide) (by decide +kernel) h276279

theorem cover538874 : P.CoversSplit 26 10 538874 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000000000000003300000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 629, 636, 874, 930, 1265, 1273, 1308, 1315]) (by decide +kernel)

theorem h538874 : P.leaf 36 538874 = 3802034 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 538874) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 538874) (weight := fun _ => 1) (xs := [272, 273, 276, 277, 336, 337, 340, 341, 762, 954, 955, 958, 959, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover538874 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88796 : P.leaf 36 88796 = 3802034 :=
  orient92 (v := 538874) (by decide) (by decide +kernel) h538874

theorem cover538878 : P.CoversSplit 26 10 538878 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000000000000003300000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 629, 636, 874, 930, 1265, 1273, 1308, 1315]) (by decide +kernel)

theorem h538878 : P.leaf 36 538878 = 10326820 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 538878) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 538878) (weight := fun _ => 1) (xs := [272, 273, 276, 277, 336, 337, 340, 341, 698, 762, 954, 955, 958, 959, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover538878 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88797 : P.leaf 36 88797 = 10326820 :=
  orient92 (v := 538878) (by decide) (by decide +kernel) h538878

theorem cover103918 : P.CoversSplit 26 10 103918 0xffff0000ffff0505000000000000000000000000000000000000000011000000050505050505050505050000050500000000000000000000000000000100000000000000333301010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 629, 636, 873, 922, 930, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c103918_0 : P.sumLeaves 26 106412032 704 = 420290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103918) (lo := 0) (len := 704) (W := 420290) check rows elimOK (by decide) (by decide) cover103918 (by decide)
  decide +kernel

theorem contract103918_1 : P.leaf 32 1662699 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 923), (28, 0, 1315), (30, 0, 1315), (12, 1, 908), (21, 0, 1658), (5, 1, 586), (9, 0, 1259), (26, 1, 579), (15, 1, 915)]) (q := 1259) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c103918_1 : P.sumLeaves 26 106412736 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1662699) rows (by decide) (by decide)).symm.trans contract103918_1

theorem c103918_2 : P.sumLeaves 26 106412800 256 = 22113582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103918) (lo := 768) (len := 256) (W := 22113582) check rows elimOK (by decide) (by decide) cover103918 (by decide)
  decide +kernel

theorem h103918 : P.leaf 36 103918 = 22533872 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 420290), (64, 0), (256, 22113582)]) (.cons c103918_0 (.cons c103918_1 (.cons c103918_2 (.nil)))) (by decide) (by decide))

theorem h88798 : P.leaf 36 88798 = 22533872 :=
  orient4 (v := 103918) (by decide) (by decide +kernel) h103918

theorem cover103919 : P.CoversSplit 26 10 103919 0xffff0000ffff0505000000000000000000000000000000000000000011000000050505050505050505050000050500000000000000000000000000000100000000000000333301010000000000000000000000000000000000000000000000000000000001010101000000000101000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c103919_0 : P.sumLeaves 26 106413056 704 = 1208526 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103919) (lo := 0) (len := 704) (W := 1208526) check rows elimOK (by decide) (by decide) cover103919 (by decide)
  decide +kernel

theorem contract103919_1 : P.leaf 32 1662715 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 923), (28, 0, 1315), (30, 0, 1315), (12, 1, 866), (21, 0, 1658), (5, 1, 586), (9, 0, 1259), (26, 1, 579), (15, 1, 915)]) (q := 1259) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c103919_1 : P.sumLeaves 26 106413760 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1662715) rows (by decide) (by decide)).symm.trans contract103919_1

theorem c103919_2 : P.sumLeaves 26 106413824 256 = 50863872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103919) (lo := 768) (len := 256) (W := 50863872) check rows elimOK (by decide) (by decide) cover103919 (by decide)
  decide +kernel

theorem h103919 : P.leaf 36 103919 = 52072398 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 1208526), (64, 0), (256, 50863872)]) (.cons c103919_0 (.cons c103919_1 (.cons c103919_2 (.nil)))) (by decide) (by decide))

theorem h88799 : P.leaf 36 88799 = 52072398 :=
  orient4 (v := 103919) (by decide) (by decide +kernel) h103919

theorem cover103894 : P.CoversSplit 26 10 103894 0xc0000000c0000000000000000000000000000000000000000000000000100000000000000000000004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 629, 636, 873, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem h103894 : P.leaf 36 103894 = 1660972 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103894) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103894) (weight := fun _ => 1) (xs := [528, 666, 698, 788, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103894 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88806 : P.leaf 36 88806 = 1660972 :=
  orient4 (v := 103894) (by decide) (by decide +kernel) h103894

theorem cover103895 : P.CoversSplit 26 10 103895 0xc0000000c0000000000000000000000000000000000000000000000000100000000000000000000004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 873, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem h103895 : P.leaf 36 103895 = 3579156 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103895) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103895) (weight := fun _ => 1) (xs := [528, 666, 698, 788, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103895 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88807 : P.leaf 36 88807 = 3579156 :=
  orient4 (v := 103895) (by decide) (by decide +kernel) h103895

theorem cover539347 : P.CoversSplit 26 10 539347 0xaa00000022000000aa0000002200000000000000000000000000000000000000000000000000000005000000010000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220000000000000000000000000000000000000000000000000000000000000001000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 530, 930, 972, 979, 1273, 1315]) (by decide +kernel)

theorem h539347 : P.leaf 36 539347 = 1566008 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 539347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 539347) (weight := fun _ => 1) (xs := [24, 281, 285, 345, 349, 664, 696, 698, 921, 925, 953, 955, 957, 959, 985, 989, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover539347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88810 : P.leaf 36 88810 = 1566008 :=
  orient92 (v := 539347) (by decide) (by decide +kernel) h539347

theorem cover103901 : P.CoversSplit 26 10 103901 0xf0f00000f0f00000000000000000000000000000000000000000000010000000000000000000000005050000050500000000000000000000000000000100000000000000303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 580, 629, 636, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h103901 : P.leaf 36 103901 = 5368073 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103901) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103901) (weight := fun _ => 1) (xs := [468, 469, 476, 477, 536, 656, 658, 664, 666, 688, 690, 696, 698, 796, 980, 981, 982, 983, 988, 989, 990, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103901 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88811 : P.leaf 36 88811 = 5368073 :=
  orient4 (v := 103901) (by decide) (by decide +kernel) h103901

theorem cover103902 : P.CoversSplit 26 10 103902 0xf0f00000f0f00000000000000000000000000000000000000000000010000000000000000000000005050000050500000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 531, 629, 636, 873, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem h103902 : P.leaf 36 103902 = 7391727 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103902) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103902) (weight := fun _ => 1) (xs := [536, 656, 658, 664, 666, 688, 690, 696, 698, 796, 980, 981, 982, 983, 988, 989, 990, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103902 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88814 : P.leaf 36 88814 = 7391727 :=
  orient4 (v := 103902) (by decide) (by decide +kernel) h103902

theorem cover103903 : P.CoversSplit 26 10 103903 0xf0f00000f0f00000000000000000000000000000000000000000000010000000000000000000000005050000050500000000000000000000000000000100000000000000303000000000000000000000000000000000000000000000000000000000000000000000000000000101000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h103903 : P.leaf 36 103903 = 16770959 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103903) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103903) (weight := fun _ => 1) (xs := [144, 152, 468, 469, 476, 477, 536, 656, 658, 664, 666, 688, 690, 696, 698, 796, 980, 981, 982, 983, 988, 989, 990, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103903 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88815 : P.leaf 36 88815 = 16770959 :=
  orient4 (v := 103903) (by decide) (by decide +kernel) h103903

theorem cover304539 : P.CoversSplit 26 10 304539 0x8888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 531, 537, 538, 629, 958, 1265, 1272, 1665]) (by decide +kernel)

theorem h304539 : P.leaf 36 304539 = 657452 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 304539) (keep := keep16) (twice := twice16) rows (by decide) (by decide) bal16 (invRow16 (H := 304539) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 304539) (weight := rowWeight keep16 twice16) (xs := [1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover304539 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88820 : P.leaf 36 88820 = 657452 :=
  orient84 (v := 304539) (by decide) (by decide +kernel) h304539

theorem cover103923 : P.CoversSplit 26 10 103923 0x8000000080000000000000000000000000000000000000000000000000000000000000000000000000000400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 873, 922, 930, 1315]) (by decide +kernel)

theorem h103923 : P.leaf 36 103923 = 2720324 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103923) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103923) (weight := fun _ => 1) (xs := [650, 682, 991, 1023]) check rows elimOK (by decide) (by decide) cover103923 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88821 : P.leaf 36 88821 = 2720324 :=
  orient4 (v := 103923) (by decide) (by decide +kernel) h103923

theorem cover103926 : P.CoversSplit 26 10 103926 0xcc000000cc000400000000000000000000000000000000000000000000110000040004000400040004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 531, 629, 636, 873, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h103926 : P.leaf 36 103926 = 12948954 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103926) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103926) (weight := fun _ => 1) (xs := [528, 666, 698, 714, 730, 746, 762, 784, 788, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103926 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88822 : P.leaf 36 88822 = 12948954 :=
  orient4 (v := 103926) (by decide) (by decide +kernel) h103926

theorem cover103927 : P.CoversSplit 26 10 103927 0xcc000000cc000400000000000000000000000000000000000000000000110000040004000400040004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h103927 : P.leaf 36 103927 = 25627797 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103927) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103927) (weight := fun _ => 1) (xs := [528, 666, 698, 714, 730, 746, 762, 784, 788, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103927 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88823 : P.leaf 36 88823 = 25627797 :=
  orient4 (v := 103927) (by decide) (by decide +kernel) h103927

theorem cover276339 : P.CoversSplit 26 10 276339 0xa0000000a00000000000000000000000000000000000000000000000000000000000000000000000000005000000050000000000000000000000000000000000a0000000a02000000000000000000000000000002000000000000000000000000000000000000000000005000000050100000000000000000000000000000100 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972]) (by decide +kernel)

theorem h276339 : P.leaf 36 276339 = 6999652 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 276339) (keep := keep13) (twice := twice13) rows (by decide) (by decide) bal13 (invRow13 (H := 276339) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276339) (weight := rowWeight keep13 twice13) (xs := [8, 128, 136, 138, 168, 170, 349, 469, 477, 479, 509, 511, 648, 650, 680, 682, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover276339 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88825 : P.leaf 36 88825 = 6999652 :=
  orient6 (v := 276339) (by decide) (by decide +kernel) h276339

theorem cover111083 : P.CoversSplit 26 10 111083 0xaaaa0000aaaa0000aaaa0000aaaa010100000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 930, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c111083_0 : P.sumLeaves 26 113748992 1024 = 11696534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 111083) (lo := 0) (len := 1024) (W := 11696534) check rows elimOK (by decide) (by decide) cover111083 (by decide)
  decide +kernel

theorem h111083 : P.leaf 36 111083 = 11696534 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11696534)]) (.cons c111083_0 (.nil)) (by decide) (by decide))

theorem h88826 : P.leaf 36 88826 = 11696534 :=
  orient86 (v := 111083) (by decide) (by decide +kernel) h111083

theorem cover103933 : P.CoversSplit 26 10 103933 0xffff0000ffff0505000000000000000000000000000000000000000011000000050505050505050505050000050500000000000000000000000000000100000000000000333301010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [580, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c103933_0 : P.sumLeaves 26 106427392 1024 = 38368915 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103933) (lo := 0) (len := 1024) (W := 38368915) check rows elimOK (by decide) (by decide) cover103933 (by decide)
  decide +kernel

theorem h103933 : P.leaf 36 103933 = 38368915 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 38368915)]) (.cons c103933_0 (.nil)) (by decide) (by decide))

theorem h88827 : P.leaf 36 88827 = 38368915 :=
  orient4 (v := 103933) (by decide) (by decide +kernel) h103933

theorem cover103930 : P.CoversSplit 26 10 103930 0xa0a00000a0a00000000000000000000000000000000000000000000000000000000000000000000000000505000005050000000000000000000000000000000000000000202000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 873, 922, 930, 965, 1665]) (by decide +kernel)

theorem h103930 : P.leaf 36 103930 = 8976154 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103930) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103930) (weight := fun _ => 1) (xs := [469, 477, 640, 642, 648, 650, 672, 674, 680, 682, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover103930 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88828 : P.leaf 36 88828 = 8976154 :=
  orient4 (v := 103930) (by decide) (by decide +kernel) h103930

theorem cover538879 : P.CoversSplit 26 10 538879 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000000000000003300000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 629, 636, 874, 930, 1265, 1273, 1308, 1315]) (by decide +kernel)

theorem h538879 : P.leaf 36 538879 = 22963948 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 538879) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 538879) (weight := fun _ => 1) (xs := [272, 273, 276, 277, 336, 337, 340, 341, 698, 762, 954, 955, 958, 959, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover538879 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88829 : P.leaf 36 88829 = 22963948 :=
  orient92 (v := 538879) (by decide) (by decide +kernel) h538879

theorem cover103934 : P.CoversSplit 26 10 103934 0xffff0000ffff0505000000000000000000000000000000000000000011000000050505050505050505050000050500000000000000000000000000000100000000000000333301010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 629, 636, 873, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c103934_0 : P.sumLeaves 26 106428416 1024 = 60204799 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103934) (lo := 0) (len := 1024) (W := 60204799) check rows elimOK (by decide) (by decide) cover103934 (by decide)
  decide +kernel

theorem h103934 : P.leaf 36 103934 = 60204799 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 60204799)]) (.cons c103934_0 (.nil)) (by decide) (by decide))

theorem h88830 : P.leaf 36 88830 = 60204799 :=
  orient4 (v := 103934) (by decide) (by decide +kernel) h103934

theorem cover103935 : P.CoversSplit 26 10 103935 0xffff0000ffff0505000000000000000000000000000000000000000011000000050505050505050505050000050500000000000000000000000000000100000000000000333301010000000000000000000000000000000000000000000000000000000001010101000000000101000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c103935_0 : P.sumLeaves 26 106429440 1024 = 128708033 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 103935) (lo := 0) (len := 1024) (W := 128708033) check rows elimOK (by decide) (by decide) cover103935 (by decide)
  decide +kernel

theorem h103935 : P.leaf 36 103935 = 128708033 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 128708033)]) (.cons c103935_0 (.nil)) (by decide) (by decide))

theorem h88831 : P.leaf 36 88831 = 128708033 :=
  orient4 (v := 103935) (by decide) (by decide +kernel) h103935

theorem cover88979 : P.CoversSplit 26 10 88979 0x8000000000000000800000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 615, 972, 979, 1315]) (by decide +kernel)

theorem h88979 : P.leaf 36 88979 = 1205480 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 88979) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88979) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88979) (weight := rowWeight keep4 twice4) (xs := [831, 895, 959, 1023]) check rows elimOK (by decide) (by decide) cover88979 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover104355 : P.CoversSplit 26 10 104355 0xc000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000c000000000300000000000000000000000000000000000000000000000000000c000000000300000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 608, 873, 922, 929, 930, 1658]) (by decide +kernel)

theorem h104355 : P.leaf 36 104355 = 687608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 104355) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 104355) (weight := fun _ => 1) (xs := [212, 213, 254, 255, 468, 469, 510, 511, 766, 767, 1022, 1023]) check rows elimOK (by decide) (by decide) cover104355 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88981 : P.leaf 36 88981 = 687608 :=
  orient4 (v := 104355) (by decide) (by decide +kernel) h104355

theorem cover88983 : P.CoversSplit 26 10 88983 0xcc00000000000000cc00000000000000cc00000000000003c80000000000000000000c0000000000000000000000000000000c0000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 538, 922, 972, 979, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem h88983 : P.leaf 36 88983 = 12231677 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88983) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88983) (weight := fun _ => 1) (xs := [576, 577, 618, 619, 746, 747, 827, 830, 831, 832, 833, 890, 891, 894, 895, 954, 955, 958, 959, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover88983 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover276387 : P.CoversSplit 26 10 276387 0xc000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 873, 930, 972, 1273, 1658]) (by decide +kernel)

theorem h276387 : P.leaf 36 276387 = 990432 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276387) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276387) (weight := fun _ => 1) (xs := [446, 447, 510, 511, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276387 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88985 : P.leaf 36 88985 = 990432 :=
  orient6 (v := 276387) (by decide) (by decide +kernel) h276387

theorem cover304499 : P.CoversSplit 26 10 304499 0x8000000080000000000000000000000000000000000000000000000000000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 579, 636, 881, 930, 958, 1265, 1665]) (by decide +kernel)

theorem h304499 : P.leaf 36 304499 = 743296 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 304499) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 304499) (weight := fun _ => 1) (xs := [735, 767, 991, 1023]) check rows elimOK (by decide) (by decide) cover304499 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88986 : P.leaf 36 88986 = 743296 :=
  orient74 (v := 304499) (by decide) (by decide +kernel) h304499

theorem cover111093 : P.CoversSplit 26 10 111093 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 580, 629, 636, 873, 930, 1266, 1315, 1658, 1665]) (by decide +kernel)

theorem h111093 : P.leaf 36 111093 = 8369676 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 111093) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 111093) (weight := fun _ => 1) (xs := [906, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover111093 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88987 : P.leaf 36 88987 = 8369676 :=
  orient86 (v := 111093) (by decide) (by decide +kernel) h111093

theorem cover289619 : P.CoversSplit 26 10 289619 0xa000a000000000000000000000000000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 530, 579, 881, 972, 979, 1273, 1658]) (by decide +kernel)

theorem h289619 : P.leaf 36 289619 = 924128 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289619) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289619) (weight := fun _ => 1) (xs := [877, 879, 893, 895, 1005, 1007, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289619 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88988 : P.leaf 36 88988 = 924128 :=
  orient80 (v := 289619) (by decide) (by decide +kernel) h289619

theorem cover104363 : P.CoversSplit 26 10 104363 0xf0f0000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0f0000000c00000000000000000000000000000000000000000000000000000f0f0000000c00000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 873, 922, 929, 1273, 1658]) (by decide +kernel)

theorem c104363_0 : P.sumLeaves 26 106867712 1024 = 5515996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 104363) (lo := 0) (len := 1024) (W := 5515996) check rows elimOK (by decide) (by decide) cover104363 (by decide)
  decide +kernel

theorem h104363 : P.leaf 36 104363 = 5515996 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5515996)]) (.cons c104363_0 (.nil)) (by decide) (by decide))

theorem h88989 : P.leaf 36 88989 = 5515996 :=
  orient4 (v := 104363) (by decide) (by decide +kernel) h104363

def seg : List (ℕ × ℕ) := [(88793, 360), (88794, 720), (88795, 720), (88796, 720), (88797, 720), (88798, 720), (88799, 720), (88806, 720), (88807, 720), (88810, 720), (88811, 720), (88814, 720), (88815, 720), (88820, 360), (88821, 720), (88822, 720), (88823, 720), (88825, 360), (88826, 720), (88827, 720), (88828, 720), (88829, 720), (88830, 720), (88831, 720), (88979, 360), (88981, 720), (88983, 720), (88985, 720), (88986, 720), (88987, 720), (88988, 720), (88989, 720)]

theorem segOK : checkSeg 20 perms 88793 88990 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88793 88990 21600 347614339680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 347614339680)
    (SegSum.cons (w := 360) h88793 (SegSum.cons (w := 720) h88794 (SegSum.cons (w := 720) h88795 (SegSum.cons (w := 720) h88796 (SegSum.cons (w := 720) h88797 (SegSum.cons (w := 720) h88798 (SegSum.cons (w := 720) h88799 (SegSum.cons (w := 720) h88806 (SegSum.cons (w := 720) h88807 (SegSum.cons (w := 720) h88810 (SegSum.cons (w := 720) h88811 (SegSum.cons (w := 720) h88814 (SegSum.cons (w := 720) h88815 (SegSum.cons (w := 360) h88820 (SegSum.cons (w := 720) h88821 (SegSum.cons (w := 720) h88822 (SegSum.cons (w := 720) h88823 (SegSum.cons (w := 360) h88825 (SegSum.cons (w := 720) h88826 (SegSum.cons (w := 720) h88827 (SegSum.cons (w := 720) h88828 (SegSum.cons (w := 720) h88829 (SegSum.cons (w := 720) h88830 (SegSum.cons (w := 720) h88831 (SegSum.cons (w := 360) h88979 (SegSum.cons (w := 720) h88981 (SegSum.cons (w := 720) h88983 (SegSum.cons (w := 720) h88985 (SegSum.cons (w := 720) h88986 (SegSum.cons (w := 720) h88987 (SegSum.cons (w := 720) h88988 (SegSum.cons (w := 720) h88989 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S54
