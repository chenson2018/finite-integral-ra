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

namespace RACert.S6N0.C0.S46

open RACert RACert.Problem

theorem cover80362 : P.CoversSplit 26 10 80362 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 879, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80362 : P.leaf 36 80362 = 959352 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80362) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80362) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80362 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79580 : P.leaf 36 79580 = 959352 :=
  orient4 (v := 80362) (by decide) (by decide +kernel) h80362

theorem cover80363 : P.CoversSplit 26 10 80363 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80363 : P.leaf 36 80363 = 1049680 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80363) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80363) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80363 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79581 : P.leaf 36 79581 = 1049680 :=
  orient4 (v := 80363) (by decide) (by decide +kernel) h80363

theorem cover80366 : P.CoversSplit 26 10 80366 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 879, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80366 : P.leaf 36 80366 = 1174072 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80366) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80366) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80366 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79582 : P.leaf 36 79582 = 1174072 :=
  orient4 (v := 80366) (by decide) (by decide +kernel) h80366

theorem cover80367 : P.CoversSplit 26 10 80367 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80367 : P.leaf 36 80367 = 1304068 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80367) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80367) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80367 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79583 : P.leaf 36 79583 = 1304068 :=
  orient4 (v := 80367) (by decide) (by decide +kernel) h80367

theorem cover80346 : P.CoversSplit 26 10 80346 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 482, 629, 636, 867, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80346 : P.leaf 36 80346 = 1260168 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80346) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80346) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80346 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79596 : P.leaf 36 79596 = 1260168 :=
  orient4 (v := 80346) (by decide) (by decide +kernel) h80346

theorem cover80347 : P.CoversSplit 26 10 80347 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80347 : P.leaf 36 80347 = 1893880 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80347) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79597 : P.leaf 36 79597 = 1893880 :=
  orient4 (v := 80347) (by decide) (by decide +kernel) h80347

theorem cover80350 : P.CoversSplit 26 10 80350 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 867, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80350 : P.leaf 36 80350 = 2914188 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80350) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80350) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80350 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79598 : P.leaf 36 79598 = 2914188 :=
  orient4 (v := 80350) (by decide) (by decide +kernel) h80350

theorem cover80351 : P.CoversSplit 26 10 80351 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80351 : P.leaf 36 80351 = 3599708 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80351) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80351) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80351 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79599 : P.leaf 36 79599 = 3599708 :=
  orient4 (v := 80351) (by decide) (by decide +kernel) h80351

theorem cover80382 : P.CoversSplit 26 10 80382 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 867, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80382 : P.leaf 36 80382 = 6995992 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80382) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80382) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80382 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79614 : P.leaf 36 79614 = 6995992 :=
  orient4 (v := 80382) (by decide) (by decide +kernel) h80382

theorem cover80383 : P.CoversSplit 26 10 80383 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80383 : P.leaf 36 80383 = 7806480 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80383) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80383) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80383 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79615 : P.leaf 36 79615 = 7806480 :=
  orient4 (v := 80383) (by decide) (by decide +kernel) h80383

theorem cover79637 : P.CoversSplit 26 10 79637 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h79637 : P.leaf 36 79637 = 129728 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79637) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79637) (weight := fun _ => 1) (xs := [1019, 1023]) check rows elimOK (by decide) (by decide) cover79637 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79639 : P.CoversSplit 26 10 79639 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h79639 : P.leaf 36 79639 = 607952 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79639) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79639) (weight := fun _ => 1) (xs := [698, 1019, 1023]) check rows elimOK (by decide) (by decide) cover79639 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover298403 : P.CoversSplit 26 10 298403 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 538, 636, 922, 929, 1658]) (by decide +kernel)

theorem h298403 : P.leaf 36 298403 = 96000 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298403) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298403) (weight := fun _ => 1) (xs := [1007, 1023]) check rows elimOK (by decide) (by decide) cover298403 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79641 : P.leaf 36 79641 = 96000 :=
  orient6 (v := 298403) (by decide) (by decide +kernel) h298403

theorem cover79643 : P.CoversSplit 26 10 79643 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 873, 972, 979, 1273, 1322]) (by decide +kernel)

theorem h79643 : P.leaf 36 79643 = 651840 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79643) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79643) (weight := fun _ => 1) (xs := [1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79643 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79644 : P.CoversSplit 26 10 79644 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 538, 923, 930, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem h79644 : P.leaf 36 79644 = 143808 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79644) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79644) (weight := fun _ => 1) (xs := [1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79644 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79645 : P.CoversSplit 26 10 79645 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h79645 : P.leaf 36 79645 = 1003976 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79645) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79645) (weight := fun _ => 1) (xs := [1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79645 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover101739 : P.CoversSplit 26 10 101739 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 629, 636, 922, 930, 965, 1273, 1322, 1658]) (by decide +kernel)

theorem h101739 : P.leaf 36 101739 = 542624 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 101739) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 101739) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101739) (weight := rowWeight keep12 twice12) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101739 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79646 : P.leaf 36 79646 = 542624 :=
  orient72 (v := 101739) (by decide) (by decide +kernel) h101739

theorem cover79647 : P.CoversSplit 26 10 79647 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem h79647 : P.leaf 36 79647 = 2992312 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79647) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79647) (weight := fun _ => 1) (xs := [688, 690, 696, 698, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79647 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover80659 : P.CoversSplit 26 10 80659 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 608, 930, 972, 979, 1658]) (by decide +kernel)

theorem h80659 : P.leaf 36 80659 = 102416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80659) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80659) (weight := fun _ => 1) (xs := [682, 1023]) check rows elimOK (by decide) (by decide) cover80659 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79653 : P.leaf 36 79653 = 102416 :=
  orient4 (v := 80659) (by decide) (by decide +kernel) h80659

theorem cover101827 : P.CoversSplit 26 10 101827 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 608, 629, 636, 881, 930, 965, 1273, 1322]) (by decide +kernel)

theorem h101827 : P.leaf 36 101827 = 96768 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101827) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101827) (weight := fun _ => 1) (xs := [1007, 1023]) check rows elimOK (by decide) (by decide) cover101827 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79654 : P.leaf 36 79654 = 96768 :=
  orient72 (v := 101827) (by decide) (by decide +kernel) h101827

theorem cover80663 : P.CoversSplit 26 10 80663 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h80663 : P.leaf 36 80663 = 810040 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80663) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80663) (weight := fun _ => 1) (xs := [698, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80663 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79655 : P.leaf 36 79655 = 810040 :=
  orient4 (v := 80663) (by decide) (by decide +kernel) h80663

theorem cover298434 : P.CoversSplit 26 10 298434 0x8000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 510, 530, 608, 629, 636, 922, 929, 1665]) (by decide +kernel)

theorem h298434 : P.leaf 36 298434 = 6272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298434) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298434) (weight := fun _ => 1) (xs := [991, 1023]) check rows elimOK (by decide) (by decide) cover298434 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79656 : P.leaf 36 79656 = 6272 :=
  orient6 (v := 298434) (by decide) (by decide +kernel) h298434

theorem cover298435 : P.CoversSplit 26 10 298435 0x8000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 922, 929, 1665]) (by decide +kernel)

theorem h298435 : P.leaf 36 298435 = 110336 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298435) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298435) (weight := fun _ => 1) (xs := [991, 1023]) check rows elimOK (by decide) (by decide) cover298435 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79657 : P.leaf 36 79657 = 110336 :=
  orient6 (v := 298435) (by decide) (by decide +kernel) h298435

theorem cover277267 : P.CoversSplit 26 10 277267 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 579, 615, 930, 972, 1272, 1273, 1658]) (by decide +kernel)

theorem h277267 : P.leaf 36 277267 = 100800 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 277267) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 277267) (weight := fun _ => 1) (xs := [495, 511, 1007, 1023]) check rows elimOK (by decide) (by decide) cover277267 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79658 : P.leaf 36 79658 = 100800 :=
  orient74 (v := 277267) (by decide) (by decide +kernel) h277267

theorem cover79659 : P.CoversSplit 26 10 79659 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1266, 1273, 1322, 1658]) (by decide +kernel)

theorem h79659 : P.leaf 36 79659 = 888384 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79659) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79659) (weight := fun _ => 1) (xs := [997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79659 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover307507 : P.CoversSplit 26 10 307507 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 629, 636, 930, 1265]) (by decide +kernel)

theorem h307507 : P.leaf 36 307507 = 176032 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 307507) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 307507) (weight := fun _ => 1) (xs := [85, 341, 767, 1023]) check rows elimOK (by decide) (by decide) cover307507 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79660 : P.leaf 36 79660 = 176032 :=
  orient80 (v := 307507) (by decide) (by decide +kernel) h307507

theorem cover80667 : P.CoversSplit 26 10 80667 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 930, 972, 1273, 1322]) (by decide +kernel)

theorem h80667 : P.leaf 36 80667 = 869712 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80667) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80667) (weight := fun _ => 1) (xs := [672, 674, 680, 682, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover80667 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79661 : P.leaf 36 79661 = 869712 :=
  orient4 (v := 80667) (by decide) (by decide +kernel) h80667

theorem cover101835 : P.CoversSplit 26 10 101835 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101835 : P.leaf 36 101835 = 697264 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101835) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101835) (weight := fun _ => 1) (xs := [997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101835 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79662 : P.leaf 36 79662 = 697264 :=
  orient72 (v := 101835) (by decide) (by decide +kernel) h101835

theorem cover80671 : P.CoversSplit 26 10 80671 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 930, 972, 1273, 1315, 1322, 1658]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem h80671 : P.leaf 36 80671 = 3892712 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80671) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80671) (weight := fun _ => 1) (xs := [688, 690, 696, 698, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80671 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79663 : P.leaf 36 79663 = 3892712 :=
  orient4 (v := 80671) (by decide) (by decide +kernel) h80671

theorem cover101859 : P.CoversSplit 26 10 101859 0x8800880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 881, 930, 965, 1273, 1322]) (by decide +kernel)

theorem h101859 : P.leaf 36 101859 = 889584 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101859) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101859) (weight := fun _ => 1) (xs := [1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover101859 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79670 : P.leaf 36 79670 = 889584 :=
  orient72 (v := 101859) (by decide) (by decide +kernel) h101859

theorem cover79671 : P.CoversSplit 26 10 79671 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h79671 : P.leaf 36 79671 = 4524360 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 79671) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79671) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79671) (weight := rowWeight keep3 twice3) (xs := [686, 698, 702, 750, 762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover79671 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover298466 : P.CoversSplit 26 10 298466 0x8000800080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 636, 881, 922, 929, 1658, 1665]) (by decide +kernel)

theorem h298466 : P.leaf 36 298466 = 34016 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298466) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298466) (weight := fun _ => 1) (xs := [975, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover298466 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79672 : P.leaf 36 79672 = 34016 :=
  orient6 (v := 298466) (by decide) (by decide +kernel) h298466

def seg : List (ℕ × ℕ) := [(79580, 720), (79581, 720), (79582, 720), (79583, 720), (79596, 180), (79597, 360), (79598, 720), (79599, 720), (79614, 360), (79615, 360), (79637, 720), (79639, 720), (79641, 720), (79643, 720), (79644, 360), (79645, 720), (79646, 360), (79647, 720), (79653, 360), (79654, 720), (79655, 720), (79656, 360), (79657, 720), (79658, 720), (79659, 720), (79660, 720), (79661, 720), (79662, 720), (79663, 720), (79670, 360), (79671, 360), (79672, 720)]

theorem segOK : checkSeg 20 perms 79580 79673 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79580 79673 19260 25867216800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 25867216800)
    (SegSum.cons (w := 720) h79580 (SegSum.cons (w := 720) h79581 (SegSum.cons (w := 720) h79582 (SegSum.cons (w := 720) h79583 (SegSum.cons (w := 180) h79596 (SegSum.cons (w := 360) h79597 (SegSum.cons (w := 720) h79598 (SegSum.cons (w := 720) h79599 (SegSum.cons (w := 360) h79614 (SegSum.cons (w := 360) h79615 (SegSum.cons (w := 720) h79637 (SegSum.cons (w := 720) h79639 (SegSum.cons (w := 720) h79641 (SegSum.cons (w := 720) h79643 (SegSum.cons (w := 360) h79644 (SegSum.cons (w := 720) h79645 (SegSum.cons (w := 360) h79646 (SegSum.cons (w := 720) h79647 (SegSum.cons (w := 360) h79653 (SegSum.cons (w := 720) h79654 (SegSum.cons (w := 720) h79655 (SegSum.cons (w := 360) h79656 (SegSum.cons (w := 720) h79657 (SegSum.cons (w := 720) h79658 (SegSum.cons (w := 720) h79659 (SegSum.cons (w := 720) h79660 (SegSum.cons (w := 720) h79661 (SegSum.cons (w := 720) h79662 (SegSum.cons (w := 720) h79663 (SegSum.cons (w := 360) h79670 (SegSum.cons (w := 360) h79671 (SegSum.cons (w := 720) h79672 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S46
