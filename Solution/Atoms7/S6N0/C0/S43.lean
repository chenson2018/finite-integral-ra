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

namespace RACert.S6N0.C0.S43

open RACert RACert.Problem

theorem cover99707 : P.CoversSplit 26 10 99707 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 629, 636, 873, 881, 922, 958, 965, 1322]) (by decide +kernel)

theorem h99707 : P.leaf 36 99707 = 641480 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99707) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99707) (weight := fun _ => 1) (xs := [1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover99707 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78750 : P.leaf 36 78750 = 641480 :=
  orient72 (v := 99707) (by decide) (by decide +kernel) h99707

theorem cover99711 : P.CoversSplit 26 10 99711 0xf0f0000000000000000000000000000000000000000000000000000000000000000055550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000110000000000000000000000000000000000000000000000000000000000000011000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 629, 636, 873, 881, 922, 965, 1315, 1322, 1665]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem h99711 : P.leaf 36 99711 = 3286513 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99711) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99711) (weight := fun _ => 1) (xs := [72, 76, 328, 332, 348, 349, 736, 738, 740, 742, 744, 746, 748, 750, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover99711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78751 : P.leaf 36 78751 = 3286513 :=
  orient72 (v := 99711) (by decide) (by decide +kernel) h99711

theorem cover530559 : P.CoversSplit 26 10 530559 0x8000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 622, 629, 636, 874, 922, 930, 1265, 1273]) (by decide +kernel)

theorem h530559 : P.leaf 36 530559 = 932856 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 530559) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 530559) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530559) (weight := rowWeight keep0 twice0) (xs := [256, 320, 384, 448, 512, 576, 640, 704, 768, 832, 896, 960, 1023]) check rows elimOK (by decide) (by decide) cover530559 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78774 : P.leaf 36 78774 = 932856 :=
  orient324 (v := 530559) (by decide) (by decide +kernel) h530559

theorem cover99831 : P.CoversSplit 26 10 99831 0xcc00000000000000000000000000000000000000000000000000000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 873, 881, 930, 958, 965, 1273, 1315]) (by decide +kernel)

theorem h99831 : P.leaf 36 99831 = 3683424 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99831) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99831) (weight := fun _ => 1) (xs := [762, 766, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover99831 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78775 : P.leaf 36 78775 = 3683424 :=
  orient72 (v := 99831) (by decide) (by decide +kernel) h99831

theorem cover530651 : P.CoversSplit 26 10 530651 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 629, 636, 922, 930, 972, 1273]) (by decide +kernel)

theorem h530651 : P.leaf 36 530651 = 102032 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 530651) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530651) (weight := fun _ => 1) (xs := [341, 1023]) check rows elimOK (by decide) (by decide) cover530651 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78776 : P.leaf 36 78776 = 102032 :=
  orient324 (v := 530651) (by decide) (by decide +kernel) h530651

theorem cover100183 : P.CoversSplit 26 10 100183 0xa0000000000000000000000000000000000000002020000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 874, 881, 930, 1315, 1322]) (by decide +kernel)

theorem h100183 : P.leaf 36 100183 = 1079392 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100183) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100183) (weight := fun _ => 1) (xs := [509, 511, 853, 861, 1021, 1023]) check rows elimOK (by decide) (by decide) cover100183 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78777 : P.leaf 36 78777 = 1079392 :=
  orient84 (v := 100183) (by decide) (by decide +kernel) h100183

theorem cover530655 : P.CoversSplit 26 10 530655 0xc000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000001000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 629, 636, 880, 922, 930, 965, 972, 1265, 1273, 1308]) (by decide +kernel)

theorem h530655 : P.leaf 36 530655 = 703914 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 530655) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530655) (weight := fun _ => 1) (xs := [276, 340, 341, 958, 1022, 1023]) check rows elimOK (by decide) (by decide) cover530655 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78778 : P.leaf 36 78778 = 703914 :=
  orient324 (v := 530655) (by decide) (by decide +kernel) h530655

theorem cover100215 : P.CoversSplit 26 10 100215 0xf0000000000000000000000000000000000000003030000000000000000000005000000000000000000000000000000000000000101000000000000000000000f0000000000000000000000000000000000000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 874, 881, 922, 930, 1322, 1658]) (by decide +kernel)

theorem h100215 : P.leaf 36 100215 = 3267486 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100215) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100215) (weight := fun _ => 1) (xs := [252, 254, 508, 509, 510, 511, 596, 604, 764, 766, 852, 853, 860, 861, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover100215 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78779 : P.leaf 36 78779 = 3267486 :=
  orient84 (v := 100215) (by decide) (by decide +kernel) h100215

theorem cover99835 : P.CoversSplit 26 10 99835 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 873, 881, 922, 958, 965, 1322]) (by decide +kernel)

theorem h99835 : P.leaf 36 99835 = 4236932 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99835) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99835) (weight := fun _ => 1) (xs := [672, 674, 680, 682, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover99835 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78782 : P.leaf 36 78782 = 4236932 :=
  orient72 (v := 99835) (by decide) (by decide +kernel) h99835

theorem cover100343 : P.CoversSplit 26 10 100343 0xff00000000000000000000000000000000000000333300000000000000000000ff00000000000000000000000000000000000000333300000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 874, 881, 923, 930, 1322]) (by decide +kernel)

theorem c100343_0 : P.sumLeaves 26 102751232 1024 = 28826304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 100343) (lo := 0) (len := 1024) (W := 28826304) check rows elimOK (by decide) (by decide) cover100343 (by decide)
  decide +kernel

theorem h100343 : P.leaf 36 100343 = 28826304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28826304)]) (.cons c100343_0 (.nil)) (by decide) (by decide))

theorem h78783 : P.leaf 36 78783 = 28826304 :=
  orient84 (v := 100343) (by decide) (by decide +kernel) h100343

theorem cover531347 : P.CoversSplit 26 10 531347 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 537, 922, 930, 972, 979]) (by decide +kernel)

theorem h531347 : P.leaf 36 531347 = 99808 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 531347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 531347) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover531347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78793 : P.leaf 36 78793 = 99808 :=
  orient324 (v := 531347) (by decide) (by decide +kernel) h531347

theorem cover274903 : P.CoversSplit 26 10 274903 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 872, 873, 930, 1265, 1273, 1308, 1665]) (by decide +kernel)

theorem h274903 : P.leaf 36 274903 = 737296 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274903) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274903) (weight := fun _ => 1) (xs := [469, 501, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover274903 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78795 : P.leaf 36 78795 = 737296 :=
  orient74 (v := 274903) (by decide) (by decide +kernel) h274903

theorem cover530871 : P.CoversSplit 26 10 530871 0xc000000000000000c0000000000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 922, 930, 972, 979, 1265, 1315]) (by decide +kernel)

theorem h530871 : P.leaf 36 530871 = 1002640 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 530871) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530871) (weight := fun _ => 1) (xs := [683, 746, 747, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover530871 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78798 : P.leaf 36 78798 = 1002640 :=
  orient324 (v := 530871) (by decide) (by decide +kernel) h530871

theorem cover274911 : P.CoversSplit 26 10 274911 0xa0a00000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 872, 873, 1265, 1273, 1308, 1665]) (by decide +kernel)

theorem h274911 : P.leaf 36 274911 = 11050148 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274911) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274911) (weight := fun _ => 1) (xs := [469, 501, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover274911 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78799 : P.leaf 36 78799 = 11050148 :=
  orient74 (v := 274911) (by decide) (by decide +kernel) h274911

theorem cover274935 : P.CoversSplit 26 10 274935 0xf000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300033003000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 873, 929, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h274935 : P.leaf 36 274935 = 4833370 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274935) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274935) (weight := fun _ => 1) (xs := [448, 449, 452, 453, 468, 469, 480, 481, 484, 485, 500, 501, 972, 973, 974, 975, 988, 989, 990, 991, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274935 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78811 : P.leaf 36 78811 = 4833370 :=
  orient74 (v := 274935) (by decide) (by decide +kernel) h274935

theorem cover530875 : P.CoversSplit 26 10 530875 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 874, 922, 930, 965, 972, 979, 1265, 1273, 1308, 1315]) (ps := [(11, [879], [922]), (16, [866], [1273])]) (by decide +kernel)

theorem h530875 : P.leaf 36 530875 = 901968 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 530875) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 530875) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530875) (weight := rowWeight keep4 twice4) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover530875 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78812 : P.leaf 36 78812 = 901968 :=
  orient324 (v := 530875) (by decide) (by decide +kernel) h530875

theorem cover531387 : P.CoversSplit 26 10 531387 0xf0f0f0f000000000000000000000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000300030000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 922, 929, 930, 972, 979, 1265, 1266, 1273, 1322]) (ps := [(11, [879], [922]), (16, [866], [1273])]) (by decide +kernel)

theorem h531387 : P.leaf 36 531387 = 6982611 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 531387) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 531387) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 531387) (weight := rowWeight keep4 twice4) (xs := [228, 484, 485, 500, 501, 740, 742, 748, 750, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover531387 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78813 : P.leaf 36 78813 = 6982611 :=
  orient324 (v := 531387) (by decide) (by decide +kernel) h531387

theorem cover530879 : P.CoversSplit 26 10 530879 0xf000000000000000f00000000000000030000000000000002000000000000000000005000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 629, 636, 874, 922, 930, 972, 979, 1265, 1273, 1308, 1315]) (ps := [(16, [1265], [1273])]) (by decide +kernel)

theorem h530879 : P.leaf 36 530879 = 3299858 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 530879) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530879) (weight := fun _ => 1) (xs := [616, 744, 746, 829, 892, 893, 956, 957, 958, 959, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover530879 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78814 : P.leaf 36 78814 = 3299858 :=
  orient324 (v := 530879) (by decide) (by decide +kernel) h530879

theorem cover274943 : P.CoversSplit 26 10 274943 0xf0f0f0f5f0f0f0f5000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000300031003000310000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 923, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c274943_0 : P.sumLeaves 26 281541632 1024 = 74688935 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 274943) (lo := 0) (len := 1024) (W := 74688935) check rows elimOK (by decide) (by decide) cover274943 (by decide)
  decide +kernel

theorem h274943 : P.leaf 36 274943 = 74688935 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 74688935)]) (.cons c274943_0 (.nil)) (by decide) (by decide))

theorem h78815 : P.leaf 36 78815 = 74688935 :=
  orient74 (v := 274943) (by decide) (by decide +kernel) h274943

theorem cover530943 : P.CoversSplit 26 10 530943 0xf000000000000001f000000000000000f000000000000000f000000000000000000005000000000100000000000000000000050000000000000000000000000000000000003000010000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 874, 922, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

theorem h530943 : P.leaf 36 530943 = 26900142 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 530943) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 530943) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530943) (weight := rowWeight keep0 twice0) (xs := [404, 405, 448, 468, 469, 616, 618, 704, 744, 746, 828, 829, 830, 831, 892, 893, 894, 895, 956, 957, 958, 959, 960, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover530943 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78846 : P.leaf 36 78846 = 26900142 :=
  orient324 (v := 530943) (by decide) (by decide +kernel) h530943

theorem cover531455 : P.CoversSplit 26 10 531455 0xfffffffafffcfac8fafaaaaafaf8aa88ffccffc8ccccc8c8fac8aa88c8c88888fffffafafffcfac8fafaaaaafaf8aa88ffccfac8ccccc8c8fac8aa88c8c88888fffffffaffccfac8fafaaaaafac8aa88ffccffc8ccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f531455 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (544209920 + i)

theorem c531455_0 : rowSum f531455 0 311 = 467743688 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 531455) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover531455 (by decide)
  decide +kernel

theorem c531455_1 : rowSum f531455 311 165 = 651134632 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 531455) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover531455 (by decide)
  decide +kernel

theorem c531455_2 : rowSum f531455 476 506 = 739317160 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 531455) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover531455 (by decide)
  decide +kernel

theorem c531455_3 : rowSum f531455 982 42 = 196952756 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 531455) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover531455 (by decide)
  decide +kernel

theorem sum531455 : rowSum f531455 0 1024 = 2055148236 :=
  rowSum_append (F := f531455) (lo := 0) (n := 311) (m := 713) (A := 467743688) (B := 1587404548) c531455_0 (rowSum_append (F := f531455) (lo := 311) (n := 165) (m := 548) (A := 651134632) (B := 936269916) c531455_1 (rowSum_append (F := f531455) (lo := 476) (n := 506) (m := 42) (A := 739317160) (B := 196952756) c531455_2 (c531455_3)))

theorem h531455 : P.leaf 36 531455 = 2055148236 :=
  leaf_weighted (k := 26) (d := 10) (H := 531455) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 531455) (by decide) (by decide +kernel)) sum531455

theorem h78847 : P.leaf 36 78847 = 2055148236 :=
  orient324 (v := 531455) (by decide) (by decide +kernel) h531455

theorem cover79068 : P.CoversSplit 26 10 79068 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 475, 537, 580, 587, 629, 930, 972, 1273, 1658]) (by decide +kernel)

theorem h79068 : P.leaf 36 79068 = 123904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79068) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79068) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79068 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79069 : P.CoversSplit 26 10 79069 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79069 : P.leaf 36 79069 = 123904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79069) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79069) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79069 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79070 : P.CoversSplit 26 10 79070 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79070 : P.leaf 36 79070 = 123904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79070) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79070) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79070 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79071 : P.CoversSplit 26 10 79071 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79071 : P.leaf 36 79071 = 123904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79071) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79071) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79071 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79086 : P.CoversSplit 26 10 79086 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79086 : P.leaf 36 79086 = 245216 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79086) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79086) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79086 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79087 : P.CoversSplit 26 10 79087 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79087 : P.leaf 36 79087 = 245216 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79087) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79087) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79087 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79102 : P.CoversSplit 26 10 79102 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79102 : P.leaf 36 79102 = 306152 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79102) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79102) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79102 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79103 : P.CoversSplit 26 10 79103 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h79103 : P.leaf 36 79103 = 306152 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79103) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79103) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79103 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79159 : P.CoversSplit 26 10 79159 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h79159 : P.leaf 36 79159 = 280129 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 79159) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 79159) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79159) (weight := rowWeight keep9 twice9) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover79159 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79163 : P.CoversSplit 26 10 79163 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79163 : P.leaf 36 79163 = 245760 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79163) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79163) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79163 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79164 : P.CoversSplit 26 10 79164 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79164 : P.leaf 36 79164 = 81508 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79164) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79164) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79164 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(78750, 720), (78751, 720), (78774, 180), (78775, 180), (78776, 360), (78777, 360), (78778, 720), (78779, 720), (78782, 360), (78783, 360), (78793, 180), (78795, 720), (78798, 360), (78799, 360), (78811, 360), (78812, 360), (78813, 360), (78814, 720), (78815, 720), (78846, 180), (78847, 180), (79068, 360), (79069, 360), (79070, 360), (79071, 360), (79086, 360), (79087, 360), (79102, 360), (79103, 360), (79159, 90), (79163, 180), (79164, 360)]

theorem segOK : checkSeg 20 perms 78750 79165 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78750 79165 12690 459907691850 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 459907691850)
    (SegSum.cons (w := 720) h78750 (SegSum.cons (w := 720) h78751 (SegSum.cons (w := 180) h78774 (SegSum.cons (w := 180) h78775 (SegSum.cons (w := 360) h78776 (SegSum.cons (w := 360) h78777 (SegSum.cons (w := 720) h78778 (SegSum.cons (w := 720) h78779 (SegSum.cons (w := 360) h78782 (SegSum.cons (w := 360) h78783 (SegSum.cons (w := 180) h78793 (SegSum.cons (w := 720) h78795 (SegSum.cons (w := 360) h78798 (SegSum.cons (w := 360) h78799 (SegSum.cons (w := 360) h78811 (SegSum.cons (w := 360) h78812 (SegSum.cons (w := 360) h78813 (SegSum.cons (w := 720) h78814 (SegSum.cons (w := 720) h78815 (SegSum.cons (w := 180) h78846 (SegSum.cons (w := 180) h78847 (SegSum.cons (w := 360) h79068 (SegSum.cons (w := 360) h79069 (SegSum.cons (w := 360) h79070 (SegSum.cons (w := 360) h79071 (SegSum.cons (w := 360) h79086 (SegSum.cons (w := 360) h79087 (SegSum.cons (w := 360) h79102 (SegSum.cons (w := 360) h79103 (SegSum.cons (w := 90) h79159 (SegSum.cons (w := 180) h79163 (SegSum.cons (w := 360) h79164 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S43
