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

namespace RACert.S6N0.C0.S50

open RACert RACert.Problem

theorem cover81374 : P.CoversSplit 26 10 81374 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81374 : P.leaf 36 81374 = 4274000 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81374) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81374) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81374 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81375 : P.CoversSplit 26 10 81375 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81375 : P.leaf 36 81375 = 5435960 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81375) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81375) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81375 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81388 : P.CoversSplit 26 10 81388 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81388 : P.leaf 36 81388 = 1545664 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81388) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81388) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81388 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81389 : P.CoversSplit 26 10 81389 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81389 : P.leaf 36 81389 = 1569322 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81389) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81389) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81389 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81390 : P.CoversSplit 26 10 81390 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81390 : P.leaf 36 81390 = 3412344 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81390) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81390) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81390 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81391 : P.CoversSplit 26 10 81391 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81391 : P.leaf 36 81391 = 3569296 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81391) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81391) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81391 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81406 : P.CoversSplit 26 10 81406 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81406 : P.leaf 36 81406 = 9553084 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81406) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81406) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81406 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81407 : P.CoversSplit 26 10 81407 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h81407 : P.leaf 36 81407 = 10138416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81407) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81407) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover81407 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81683 : P.CoversSplit 26 10 81683 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 608, 930, 972, 979, 1658]) (by decide +kernel)

theorem h81683 : P.leaf 36 81683 = 421804 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81683) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81683) (weight := fun _ => 1) (xs := [682, 1023]) check rows elimOK (by decide) (by decide) cover81683 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover789659 : P.CoversSplit 26 10 789659 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 587, 636, 881, 922, 1273]) (by decide +kernel)

theorem h789659 : P.leaf 36 789659 = 57472 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 789659) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 789659) (weight := fun _ => 1) (xs := [767, 1023]) check rows elimOK (by decide) (by decide) cover789659 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81684 : P.leaf 36 81684 = 57472 :=
  orient85 (v := 789659) (by decide) (by decide +kernel) h789659

theorem cover81685 : P.CoversSplit 26 10 81685 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h81685 : P.leaf 36 81685 = 583840 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81685) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81685) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81685 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81686 : P.CoversSplit 26 10 81686 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h81686 : P.leaf 36 81686 = 693496 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81686) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81686) (weight := fun _ => 1) (xs := [698, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81686 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81687 : P.CoversSplit 26 10 81687 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h81687 : P.leaf 36 81687 = 3372526 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81687) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81687) (weight := fun _ => 1) (xs := [698, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81687 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81688 : P.CoversSplit 26 10 81688 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 558, 579, 615, 923, 1273, 1322]) (by decide +kernel)

theorem h81688 : P.leaf 36 81688 = 36064 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81688) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81688) (weight := fun _ => 1) (xs := [373, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover81688 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81689 : P.CoversSplit 26 10 81689 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 538, 579, 615, 923, 1273, 1322]) (by decide +kernel)

theorem h81689 : P.leaf 36 81689 = 813568 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81689) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81689) (weight := fun _ => 1) (xs := [373, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover81689 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81690 : P.CoversSplit 26 10 81690 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 972, 1273, 1322]) (by decide +kernel)

theorem h81690 : P.leaf 36 81690 = 1110929 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81690) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81690) (weight := fun _ => 1) (xs := [32, 373, 672, 674, 680, 682, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover81690 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81691 : P.CoversSplit 26 10 81691 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 972, 1273, 1322]) (by decide +kernel)

theorem h81691 : P.leaf 36 81691 = 3525887 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81691) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81691) (weight := fun _ => 1) (xs := [32, 373, 672, 674, 680, 682, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover81691 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81706 : P.CoversSplit 26 10 81706 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1266, 1273, 1315, 1322, 1658]) (ps := [(16, [523, 565], [1273])]) (by decide +kernel)

theorem h81706 : P.leaf 36 81706 = 672688 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81706) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81706) (weight := fun _ => 1) (xs := [357, 373, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81706 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81692 : P.leaf 36 81692 = 672688 :=
  orient4 (v := 81706) (by decide) (by decide +kernel) h81706

theorem cover81707 : P.CoversSplit 26 10 81707 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1266, 1273, 1315, 1322, 1658]) (ps := [(16, [523], [1273])]) (by decide +kernel)

theorem h81707 : P.leaf 36 81707 = 4489188 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81707) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81707) (weight := fun _ => 1) (xs := [357, 373, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81707 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81693 : P.leaf 36 81693 = 4489188 :=
  orient4 (v := 81707) (by decide) (by decide +kernel) h81707

theorem cover81694 : P.CoversSplit 26 10 81694 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000110000000000000000000000000000000000000000000000000000000000000001000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (ps := [(21, [867, 1272], [1658])]) (by decide +kernel)

theorem h81694 : P.leaf 36 81694 = 4314857 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81694) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81694) (weight := fun _ => 1) (xs := [48, 304, 308, 368, 369, 372, 373, 688, 690, 696, 698, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81694 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81695 : P.CoversSplit 26 10 81695 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000110000000000000000000000000000000000000000000000000000000000000001000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h81695 : P.leaf 36 81695 = 15659500 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81695) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81695) (weight := fun _ => 1) (xs := [48, 304, 308, 368, 369, 372, 373, 688, 690, 696, 698, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81695 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover110051 : P.CoversSplit 26 10 110051 0x8800880000000000880088000000000000000000000000000000000000000000000000000000000000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 881, 930, 1273, 1322]) (by decide +kernel)

theorem h110051 : P.leaf 36 110051 = 4657828 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 110051) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 110051) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 110051) (weight := rowWeight keep1 twice1) (xs := [683, 687, 939, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover110051 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81718 : P.leaf 36 81718 = 4657828 :=
  orient72 (v := 110051) (by decide) (by decide +kernel) h110051

theorem cover81719 : P.CoversSplit 26 10 81719 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h81719 : P.leaf 36 81719 = 18960778 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 81719) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81719) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81719) (weight := rowWeight keep3 twice3) (xs := [686, 698, 702, 750, 762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81719 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81720 : P.CoversSplit 26 10 81720 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 874, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h81720 : P.leaf 36 81720 = 315492 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81720) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81720) (weight := fun _ => 1) (xs := [288, 292, 308, 352, 356, 357, 372, 373, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81720 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81721 : P.CoversSplit 26 10 81721 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h81721 : P.leaf 36 81721 = 9537245 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81721) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81721) (weight := fun _ => 1) (xs := [288, 292, 308, 352, 356, 357, 372, 373, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81721 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81722 : P.CoversSplit 26 10 81722 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1273, 1315, 1322, 1658]) (ps := [(21, [929], [1658])]) (by decide +kernel)

theorem h81722 : P.leaf 36 81722 = 10395308 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81722) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81722) (weight := fun _ => 1) (xs := [288, 292, 308, 352, 356, 357, 372, 373, 676, 678, 684, 686, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81722 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover81723 : P.CoversSplit 26 10 81723 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (ps := [(21, [929], [1658])]) (by decide +kernel)

theorem h81723 : P.leaf 36 81723 = 27548557 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 81723) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 81723) (weight := fun _ => 1) (xs := [36, 288, 292, 308, 352, 356, 357, 372, 373, 676, 678, 684, 686, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover81723 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover110059 : P.CoversSplit 26 10 110059 0xaaaaaaaa00000000aaaaabab0000000000000000000000000000000000000022000000000000000000000a0a000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f110059 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (112700416 + i)

theorem c110059_0 : rowSum f110059 0 1024 = 39667563 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 110059) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover110059 (by decide)
  decide +kernel

theorem sum110059 : rowSum f110059 0 1024 = 39667563 :=
  c110059_0

theorem h110059 : P.leaf 36 110059 = 39667563 :=
  leaf_weighted (k := 26) (d := 10) (H := 110059) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 110059) (by decide) (by decide +kernel)) sum110059

theorem h81726 : P.leaf 36 81726 = 39667563 :=
  orient72 (v := 110059) (by decide) (by decide +kernel) h110059

theorem cover81727 : P.CoversSplit 26 10 81727 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000110010000000000011001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81727_0 : P.sumLeaves 26 83688448 1024 = 100494116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81727) (lo := 0) (len := 1024) (W := 100494116) check rows elimOK (by decide) (by decide) cover81727 (by decide)
  decide +kernel

theorem h81727 : P.leaf 36 81727 = 100494116 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100494116)]) (.cons c81727_0 (.nil)) (by decide) (by decide))

theorem cover302483 : P.CoversSplit 26 10 302483 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 538, 629, 636, 922, 929]) (by decide +kernel)

theorem h302483 : P.leaf 36 302483 = 880384 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 302483) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302483) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover302483 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81737 : P.leaf 36 81737 = 880384 :=
  orient6 (v := 302483) (by decide) (by decide +kernel) h302483

theorem cover302486 : P.CoversSplit 26 10 302486 0xcc00040000000000000000000000000000000000000000000000000000000000440004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 615, 629, 636, 923, 930, 1265, 1658]) (by decide +kernel)

theorem h302486 : P.leaf 36 302486 = 1267928 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 302486) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302486) (weight := fun _ => 1) (xs := [746, 762, 766, 1002, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover302486 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81738 : P.leaf 36 81738 = 1267928 :=
  orient6 (v := 302486) (by decide) (by decide +kernel) h302486

theorem cover302487 : P.CoversSplit 26 10 302487 0xcc00040000000000000000000000000000000000000000000000000000000000440004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 538, 629, 636, 923, 930, 1265, 1658]) (by decide +kernel)

theorem h302487 : P.leaf 36 302487 = 6873032 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 302487) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 302487) (weight := fun _ => 1) (xs := [746, 762, 766, 1002, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover302487 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h81739 : P.leaf 36 81739 = 6873032 :=
  orient6 (v := 302487) (by decide) (by decide +kernel) h302487

def seg : List (ℕ × ℕ) := [(81374, 720), (81375, 720), (81388, 360), (81389, 360), (81390, 720), (81391, 720), (81406, 360), (81407, 360), (81683, 360), (81684, 360), (81685, 360), (81686, 720), (81687, 720), (81688, 360), (81689, 720), (81690, 720), (81691, 720), (81692, 720), (81693, 720), (81694, 720), (81695, 720), (81718, 180), (81719, 180), (81720, 360), (81721, 360), (81722, 720), (81723, 720), (81726, 360), (81727, 360), (81737, 90), (81738, 360), (81739, 720)]

theorem segOK : checkSeg 20 perms 81374 81742 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81374 81742 16650 136634285160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 136634285160)
    (SegSum.cons (w := 720) h81374 (SegSum.cons (w := 720) h81375 (SegSum.cons (w := 360) h81388 (SegSum.cons (w := 360) h81389 (SegSum.cons (w := 720) h81390 (SegSum.cons (w := 720) h81391 (SegSum.cons (w := 360) h81406 (SegSum.cons (w := 360) h81407 (SegSum.cons (w := 360) h81683 (SegSum.cons (w := 360) h81684 (SegSum.cons (w := 360) h81685 (SegSum.cons (w := 720) h81686 (SegSum.cons (w := 720) h81687 (SegSum.cons (w := 360) h81688 (SegSum.cons (w := 720) h81689 (SegSum.cons (w := 720) h81690 (SegSum.cons (w := 720) h81691 (SegSum.cons (w := 720) h81692 (SegSum.cons (w := 720) h81693 (SegSum.cons (w := 720) h81694 (SegSum.cons (w := 720) h81695 (SegSum.cons (w := 180) h81718 (SegSum.cons (w := 180) h81719 (SegSum.cons (w := 360) h81720 (SegSum.cons (w := 360) h81721 (SegSum.cons (w := 720) h81722 (SegSum.cons (w := 720) h81723 (SegSum.cons (w := 360) h81726 (SegSum.cons (w := 360) h81727 (SegSum.cons (w := 90) h81737 (SegSum.cons (w := 360) h81738 (SegSum.cons (w := 720) h81739 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S50
