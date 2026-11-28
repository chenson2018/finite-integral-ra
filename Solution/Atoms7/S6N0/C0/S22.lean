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

namespace RACert.S6N0.C0.S22

open RACert RACert.Problem

theorem cover99303 : P.CoversSplit 26 10 99303 0xf0300000303000000000000000000000303000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0300000303000000000000000000000303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 866, 874, 881, 923, 930, 1266, 1273]) (by decide +kernel)

theorem h99303 : P.leaf 36 99303 = 1087652 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 99303) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 99303) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99303) (weight := rowWeight keep1 twice1) (xs := [372, 373, 380, 381, 468, 469, 476, 477, 500, 501, 508, 509, 510, 511, 852, 853, 860, 861, 884, 885, 892, 893, 980, 981, 988, 989, 1012, 1013, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover99303 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13119 : P.leaf 36 13119 = 1087652 :=
  orient84 (v := 99303) (by decide) (by decide +kernel) h99303

theorem cover270619 : P.CoversSplit 26 10 270619 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 629, 873, 881, 930, 979, 1273]) (by decide +kernel)

theorem h270619 : P.leaf 36 270619 = 1105 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270619) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270619) (weight := fun _ => 1) (xs := [512, 544, 1023]) check rows elimOK (by decide) (by decide) cover270619 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13168 : P.leaf 36 13168 = 1105 :=
  orient86 (v := 270619) (by decide) (by decide +kernel) h270619

theorem cover270623 : P.CoversSplit 26 10 270623 0x8000000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 615, 629, 636, 873, 881, 908, 929, 930, 1265, 1273]) (by decide +kernel)

theorem h270623 : P.leaf 36 270623 = 17424 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270623) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270623) (weight := fun _ => 1) (xs := [784, 816, 1023]) check rows elimOK (by decide) (by decide) cover270623 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13169 : P.leaf 36 13169 = 17424 :=
  orient86 (v := 270623) (by decide) (by decide +kernel) h270623

theorem cover270651 : P.CoversSplit 26 10 270651 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 629, 636, 873, 881, 930, 972, 1273]) (by decide +kernel)

theorem h270651 : P.leaf 36 270651 = 16320 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270651) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270651) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover270651 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13170 : P.leaf 36 13170 = 16320 :=
  orient86 (v := 270651) (by decide) (by decide +kernel) h270651

theorem cover270655 : P.CoversSplit 26 10 270655 0xc000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 629, 636, 873, 881, 929, 930, 958, 1265, 1273, 1308]) (by decide +kernel)

theorem h270655 : P.leaf 36 270655 = 117664 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270655) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270655) (weight := fun _ => 1) (xs := [1006, 1022, 1023]) check rows elimOK (by decide) (by decide) cover270655 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13171 : P.leaf 36 13171 = 117664 :=
  orient86 (v := 270655) (by decide) (by decide +kernel) h270655

theorem cover98795 : P.CoversSplit 26 10 98795 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 866, 873, 881, 922, 930, 958, 965, 1322]) (by decide +kernel)

theorem h98795 : P.leaf 36 98795 = 248416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 98795) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 98795) (weight := fun _ => 1) (xs := [1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover98795 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13174 : P.leaf 36 13174 = 248416 :=
  orient84 (v := 98795) (by decide) (by decide +kernel) h98795

theorem cover98799 : P.CoversSplit 26 10 98799 0xf0f0000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 866, 881, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h98799 : P.leaf 36 98799 = 855786 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 98799) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 98799) (weight := fun _ => 1) (xs := [780, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover98799 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13175 : P.leaf 36 13175 = 855786 :=
  orient84 (v := 98799) (by decide) (by decide +kernel) h98799

theorem cover270751 : P.CoversSplit 26 10 270751 0x8000000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 615, 629, 636, 872, 873, 881, 923, 930, 1265, 1273]) (by decide +kernel)

theorem h270751 : P.leaf 36 270751 = 195080 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270751) (weight := fun _ => 1) (xs := [784, 816, 1023]) check rows elimOK (by decide) (by decide) cover270751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13177 : P.leaf 36 13177 = 195080 :=
  orient86 (v := 270751) (by decide) (by decide +kernel) h270751

theorem cover270783 : P.CoversSplit 26 10 270783 0xc000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 873, 881, 923, 930, 958, 1265, 1273, 1308]) (by decide +kernel)

theorem h270783 : P.leaf 36 270783 = 2002260 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270783) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270783) (weight := fun _ => 1) (xs := [1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover270783 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13179 : P.leaf 36 13179 = 2002260 :=
  orient86 (v := 270783) (by decide) (by decide +kernel) h270783

theorem cover34303 : P.CoversSplit 26 10 34303 0xffff000000001111000000000000000000000000000000001111000000001000555555550000111155555050000010100000000000000000111110100000100033330000333311110000000000000000333300003300110011110000110010001111111111111111111110101111101011111111110011001111101011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f34303 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (35126272 + i)

theorem c34303_0 : rowSum f34303 0 1024 = 17890038 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 34303) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover34303 (by decide)
  decide +kernel

theorem sum34303 : rowSum f34303 0 1024 = 17890038 :=
  c34303_0

theorem h34303 : P.leaf 36 34303 = 17890038 :=
  leaf_weighted (k := 26) (d := 10) (H := 34303) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 34303) (by decide) (by decide +kernel)) sum34303

theorem h13183 : P.leaf 36 13183 = 17890038 :=
  orient6 (v := 34303) (by decide) (by decide +kernel) h34303

theorem cover80292 : P.CoversSplit 26 10 80292 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem h80292 : P.leaf 36 80292 = 16699 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 80292) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 80292) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80292) (weight := rowWeight keep9 twice9) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover80292 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13296 : P.leaf 36 13296 = 16699 :=
  orient348 (v := 80292) (by decide) (by decide +kernel) h80292

theorem cover270687 : P.CoversSplit 26 10 270687 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 629, 636, 873, 881, 958, 979, 1265, 1273, 1308]) (by decide +kernel)

theorem h270687 : P.leaf 36 270687 = 182272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 270687) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 270687) (weight := fun _ => 1) (xs := [989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover270687 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13297 : P.leaf 36 13297 = 182272 :=
  orient86 (v := 270687) (by decide) (by decide +kernel) h270687

theorem cover13299 : P.CoversSplit 26 10 13299 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (ps := [(12, [880], [979]), (13, [923], [972])]) (by decide +kernel)

theorem h13299 : P.leaf 36 13299 = 604816 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 13299) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 13299) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13299) (weight := rowWeight keep2 twice2) (xs := [924, 925, 926, 927, 956, 957, 958, 959, 988, 989, 990, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover13299 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover98811 : P.CoversSplit 26 10 98811 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 866, 873, 881, 922, 930, 958, 965, 1322]) (by decide +kernel)

theorem h98811 : P.leaf 36 98811 = 2069120 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 98811) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 98811) (weight := fun _ => 1) (xs := [1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover98811 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13302 : P.leaf 36 13302 = 2069120 :=
  orient84 (v := 98811) (by decide) (by decide +kernel) h98811

theorem cover98815 : P.CoversSplit 26 10 98815 0xffff000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 881, 922, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h98815 : P.leaf 36 98815 = 12815819 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 98815) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 98815) (weight := fun _ => 1) (xs := [780, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover98815 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h13303 : P.leaf 36 13303 = 12815819 :=
  orient84 (v := 98815) (by decide) (by decide +kernel) h98815

theorem cover34815 : P.CoversSplit 26 10 34815 0xffffffffffff8888fffffafaffff8888ffffffffffcc88888888888888888888ffffaaaaffff8888aaaaaaaaaaaa8888ffffaaaaffcc88888888888888888888ffffffffcccc8888fffffafacccc8888cccccccccccc88888888888888888888ffffaaaacccc8888aaaaaaaa88888888cccc8888cccc88888888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f34815 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (35650560 + i)

theorem c34815_0 : rowSum f34815 0 379 = 242834606 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 34815) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover34815 (by decide)
  decide +kernel

theorem c34815_1 : rowSum f34815 379 452 = 380611552 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 34815) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover34815 (by decide)
  decide +kernel

theorem c34815_2 : rowSum f34815 831 193 = 294252804 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 34815) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover34815 (by decide)
  decide +kernel

theorem sum34815 : rowSum f34815 0 1024 = 917698962 :=
  rowSum_append (F := f34815) (lo := 0) (n := 379) (m := 645) (A := 242834606) (B := 674864356) c34815_0 (rowSum_append (F := f34815) (lo := 379) (n := 452) (m := 193) (A := 380611552) (B := 294252804) c34815_1 (c34815_2))

theorem h34815 : P.leaf 36 34815 = 917698962 :=
  leaf_weighted (k := 26) (d := 10) (H := 34815) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 34815) (by decide) (by decide +kernel)) sum34815

theorem h13311 : P.leaf 36 13311 = 917698962 :=
  orient6 (v := 34815) (by decide) (by decide +kernel) h34815

theorem cover13526 : P.CoversSplit 26 10 13526 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13526 : P.leaf 36 13526 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13526) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13526) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13526 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13527 : P.CoversSplit 26 10 13527 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13527 : P.leaf 36 13527 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13527) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13527) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13527 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13532 : P.CoversSplit 26 10 13532 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13532 : P.leaf 36 13532 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13532) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13532) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13532 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13533 : P.CoversSplit 26 10 13533 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13533 : P.leaf 36 13533 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13533) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13533) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13533 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13535 : P.CoversSplit 26 10 13535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13535 : P.leaf 36 13535 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13535) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13535) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13535 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13542 : P.CoversSplit 26 10 13542 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13542 : P.leaf 36 13542 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13542) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13542) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13542 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13543 : P.CoversSplit 26 10 13543 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13543 : P.leaf 36 13543 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13543) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13543) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13543 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13544 : P.CoversSplit 26 10 13544 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13544 : P.leaf 36 13544 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13544) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13544) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13544 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13545 : P.CoversSplit 26 10 13545 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13545 : P.leaf 36 13545 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13545) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13545) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13545 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13546 : P.CoversSplit 26 10 13546 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13546 : P.leaf 36 13546 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13546) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13546) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13546 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13547 : P.CoversSplit 26 10 13547 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13547 : P.leaf 36 13547 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13547) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13547) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13547 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13550 : P.CoversSplit 26 10 13550 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13550 : P.leaf 36 13550 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13550) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13550) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13550 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13551 : P.CoversSplit 26 10 13551 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13551 : P.leaf 36 13551 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13551) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13551) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13551 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13558 : P.CoversSplit 26 10 13558 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13558 : P.leaf 36 13558 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13558) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13558) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13558 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13559 : P.CoversSplit 26 10 13559 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13559 : P.leaf 36 13559 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13559) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13559) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13559 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13560 : P.CoversSplit 26 10 13560 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h13560 : P.leaf 36 13560 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 13560) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 13560) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover13560 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(13119, 90), (13168, 180), (13169, 360), (13170, 360), (13171, 720), (13174, 180), (13175, 360), (13177, 180), (13179, 360), (13183, 180), (13296, 90), (13297, 360), (13299, 360), (13302, 180), (13303, 360), (13311, 90), (13526, 360), (13527, 360), (13532, 180), (13533, 360), (13535, 180), (13542, 360), (13543, 360), (13544, 360), (13545, 360), (13546, 720), (13547, 720), (13550, 360), (13551, 360), (13558, 720), (13559, 720), (13560, 720)]

theorem segOK : checkSeg 20 perms 13119 13561 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13119 13561 11610 92387783790 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92387783790)
    (SegSum.cons (w := 90) h13119 (SegSum.cons (w := 180) h13168 (SegSum.cons (w := 360) h13169 (SegSum.cons (w := 360) h13170 (SegSum.cons (w := 720) h13171 (SegSum.cons (w := 180) h13174 (SegSum.cons (w := 360) h13175 (SegSum.cons (w := 180) h13177 (SegSum.cons (w := 360) h13179 (SegSum.cons (w := 180) h13183 (SegSum.cons (w := 90) h13296 (SegSum.cons (w := 360) h13297 (SegSum.cons (w := 360) h13299 (SegSum.cons (w := 180) h13302 (SegSum.cons (w := 360) h13303 (SegSum.cons (w := 90) h13311 (SegSum.cons (w := 360) h13526 (SegSum.cons (w := 360) h13527 (SegSum.cons (w := 180) h13532 (SegSum.cons (w := 360) h13533 (SegSum.cons (w := 180) h13535 (SegSum.cons (w := 360) h13542 (SegSum.cons (w := 360) h13543 (SegSum.cons (w := 360) h13544 (SegSum.cons (w := 360) h13545 (SegSum.cons (w := 720) h13546 (SegSum.cons (w := 720) h13547 (SegSum.cons (w := 360) h13550 (SegSum.cons (w := 360) h13551 (SegSum.cons (w := 720) h13558 (SegSum.cons (w := 720) h13559 (SegSum.cons (w := 720) h13560 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S22
