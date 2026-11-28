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

namespace RACert.S6N0.C0.S41

open RACert RACert.Problem

theorem cover78268 : P.CoversSplit 26 10 78268 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78268 : P.leaf 36 78268 = 17680 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78268) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78268) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78268 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78269 : P.CoversSplit 26 10 78269 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78269 : P.leaf 36 78269 = 65456 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78269) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78269) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78269 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78270 : P.CoversSplit 26 10 78270 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78270 : P.leaf 36 78270 = 72648 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78270) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78270) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78270 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78271 : P.CoversSplit 26 10 78271 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78271 : P.leaf 36 78271 = 376088 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78271) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78271) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78271 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78285 : P.CoversSplit 26 10 78285 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78285 : P.leaf 36 78285 = 13920 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78285) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78285) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78285 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78286 : P.CoversSplit 26 10 78286 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 873, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h78286 : P.leaf 36 78286 = 13440 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78286) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78286) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78286 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78287 : P.CoversSplit 26 10 78287 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78287 : P.leaf 36 78287 = 90016 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78287) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78287) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78287 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78300 : P.CoversSplit 26 10 78300 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 531, 629, 636, 867, 972, 979, 1322, 1658]) (by decide +kernel)

theorem h78300 : P.leaf 36 78300 = 26048 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78300) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78300) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78300 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78301 : P.CoversSplit 26 10 78301 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78301 : P.leaf 36 78301 = 104840 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78301) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78301) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78301 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78302 : P.CoversSplit 26 10 78302 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h78302 : P.leaf 36 78302 = 73152 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78302) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78302) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78302 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78303 : P.CoversSplit 26 10 78303 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78303 : P.leaf 36 78303 = 665272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78303) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78303) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78303 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78317 : P.CoversSplit 26 10 78317 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78317 : P.leaf 36 78317 = 68352 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78317) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78317) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78317 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78318 : P.CoversSplit 26 10 78318 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h78318 : P.leaf 36 78318 = 73872 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78318) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78318) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78318 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78319 : P.CoversSplit 26 10 78319 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78319 : P.leaf 36 78319 = 638200 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78319) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78319) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78319 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78334 : P.CoversSplit 26 10 78334 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h78334 : P.leaf 36 78334 = 350692 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78334) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78334) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78334 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78335 : P.CoversSplit 26 10 78335 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78335 : P.leaf 36 78335 = 6302754 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78335) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78335) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78335 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78593 : P.CoversSplit 26 10 78593 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 481, 489, 530, 538, 559, 579, 923, 930, 972, 979]) (ps := [(11, [508], [930])]) (by decide +kernel)

theorem h78593 : P.leaf 36 78593 = 64 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78593) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78593) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78593 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78595 : P.CoversSplit 26 10 78595 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 538, 579, 608, 930, 972, 979, 1266]) (by decide +kernel)

theorem h78595 : P.leaf 36 78595 = 512 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78595) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78595) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78595 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover99655 : P.CoversSplit 26 10 99655 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 629, 636, 873, 881, 922, 930, 1273, 1315]) (by decide +kernel)

theorem h99655 : P.leaf 36 99655 = 6272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99655) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99655) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover99655 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78599 : P.leaf 36 78599 = 6272 :=
  orient72 (v := 99655) (by decide) (by decide +kernel) h99655

theorem cover296323 : P.CoversSplit 26 10 296323 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 538, 629, 636, 922, 929]) (by decide +kernel)

theorem h296323 : P.leaf 36 296323 = 1024 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 296323) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 296323) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover296323 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78601 : P.leaf 36 78601 = 1024 :=
  orient6 (v := 296323) (by decide) (by decide +kernel) h296323

theorem cover274711 : P.CoversSplit 26 10 274711 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 615, 629, 636, 873, 929, 930, 1265]) (by decide +kernel)

theorem h274711 : P.leaf 36 274711 = 6272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274711) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274711) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover274711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78603 : P.leaf 36 78603 = 6272 :=
  orient74 (v := 274711) (by decide) (by decide +kernel) h274711

theorem cover274719 : P.CoversSplit 26 10 274719 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 579, 615, 629, 636, 873, 929, 1265, 1273]) (ps := [(5, [523], [636])]) (by decide +kernel)

theorem h274719 : P.leaf 36 274719 = 65280 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274719) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274719) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274719 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78607 : P.leaf 36 78607 = 65280 :=
  orient74 (v := 274719) (by decide) (by decide +kernel) h274719

theorem cover99682 : P.CoversSplit 26 10 99682 0x8000000000000000000000000000000000000000000000000000000000001111000000000000000000000000000000000000000000000000000000000000101000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 531, 579, 608, 629, 636, 873, 881, 922, 930, 1273]) (by decide +kernel)

theorem h99682 : P.leaf 36 99682 = 4256 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 99682) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 99682) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99682) (weight := rowWeight keep12 twice12) (xs := [264, 268, 516, 524, 768, 772, 776, 780, 1023]) check rows elimOK (by decide) (by decide) cover99682 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78612 : P.leaf 36 78612 = 4256 :=
  orient72 (v := 99682) (by decide) (by decide +kernel) h99682

theorem cover78613 : P.CoversSplit 26 10 78613 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h78613 : P.leaf 36 78613 = 6656 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78613) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78613) (weight := fun _ => 1) (xs := [1019, 1023]) check rows elimOK (by decide) (by decide) cover78613 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover99683 : P.CoversSplit 26 10 99683 0x8000000000000000000000000000000000000000000000000000000000001111000000000000000000000000000000000000000000000000000000000000101000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 608, 629, 636, 873, 881, 922, 930, 1273]) (by decide +kernel)

theorem h99683 : P.leaf 36 99683 = 24548 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 99683) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 99683) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99683) (weight := rowWeight keep12 twice12) (xs := [12, 264, 268, 516, 524, 768, 772, 776, 780, 1023]) check rows elimOK (by decide) (by decide) cover99683 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78614 : P.leaf 36 78614 = 24548 :=
  orient72 (v := 99683) (by decide) (by decide +kernel) h99683

theorem cover99687 : P.CoversSplit 26 10 99687 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 579, 629, 636, 873, 881, 922, 930, 958, 1273, 1315]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem h99687 : P.leaf 36 99687 = 87808 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99687) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99687) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover99687 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78615 : P.leaf 36 78615 = 87808 :=
  orient72 (v := 99687) (by decide) (by decide +kernel) h99687

theorem cover274837 : P.CoversSplit 26 10 274837 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 615, 629, 636, 872, 873, 929, 930, 1265, 1273]) (by decide +kernel)

theorem h274837 : P.leaf 36 274837 = 7168 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274837) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274837) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover274837 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78617 : P.leaf 36 78617 = 7168 :=
  orient86 (v := 274837) (by decide) (by decide +kernel) h274837

theorem cover274869 : P.CoversSplit 26 10 274869 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 872, 929, 930, 972, 979, 1273, 1658]) (by decide +kernel)

theorem h274869 : P.leaf 36 274869 = 44800 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274869) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274869) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover274869 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78619 : P.leaf 36 78619 = 44800 :=
  orient86 (v := 274869) (by decide) (by decide +kernel) h274869

theorem cover274746 : P.CoversSplit 26 10 274746 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 579, 629, 636, 867, 873, 972, 1273]) (by decide +kernel)

theorem h274746 : P.leaf 36 274746 = 7168 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274746) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274746) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274746 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78620 : P.leaf 36 78620 = 7168 :=
  orient74 (v := 274746) (by decide) (by decide +kernel) h274746

theorem cover274876 : P.CoversSplit 26 10 274876 0xc0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 538, 629, 636, 867, 873, 908, 923, 972, 1273, 1658]) (by decide +kernel)

theorem h274876 : P.leaf 36 274876 = 41232 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274876) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274876) (weight := fun _ => 1) (xs := [1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274876 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78621 : P.leaf 36 78621 = 41232 :=
  orient92 (v := 274876) (by decide) (by decide +kernel) h274876

theorem cover274747 : P.CoversSplit 26 10 274747 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 579, 629, 636, 873, 972, 979, 1273, 1665]) (ps := [(19, [908], [1273])]) (by decide +kernel)

theorem h274747 : P.leaf 36 274747 = 63840 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274747) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274747) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274747 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78622 : P.leaf 36 78622 = 63840 :=
  orient74 (v := 274747) (by decide) (by decide +kernel) h274747

theorem cover274751 : P.CoversSplit 26 10 274751 0xc0c0404400100011000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000003000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 579, 629, 636, 873, 929, 972, 979, 1265, 1273, 1658, 1665]) (ps := [(16, [1266], [1265])]) (by decide +kernel)

theorem h274751 : P.leaf 36 274751 = 486690 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274751) (weight := fun _ => 1) (xs := [448, 452, 468, 469, 772, 960, 964, 980, 994, 998, 1006, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78623 : P.leaf 36 78623 = 486690 :=
  orient74 (v := 274751) (by decide) (by decide +kernel) h274751

def seg : List (ℕ × ℕ) := [(78268, 720), (78269, 720), (78270, 720), (78271, 720), (78285, 720), (78286, 720), (78287, 720), (78300, 720), (78301, 720), (78302, 720), (78303, 720), (78317, 360), (78318, 720), (78319, 720), (78334, 360), (78335, 360), (78593, 30), (78595, 240), (78599, 360), (78601, 180), (78603, 720), (78607, 360), (78612, 120), (78613, 360), (78614, 360), (78615, 720), (78617, 720), (78619, 720), (78620, 720), (78621, 720), (78622, 720), (78623, 720)]

theorem segOK : checkSeg 20 perms 78268 78646 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78268 78646 18210 4600098480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4600098480)
    (SegSum.cons (w := 720) h78268 (SegSum.cons (w := 720) h78269 (SegSum.cons (w := 720) h78270 (SegSum.cons (w := 720) h78271 (SegSum.cons (w := 720) h78285 (SegSum.cons (w := 720) h78286 (SegSum.cons (w := 720) h78287 (SegSum.cons (w := 720) h78300 (SegSum.cons (w := 720) h78301 (SegSum.cons (w := 720) h78302 (SegSum.cons (w := 720) h78303 (SegSum.cons (w := 360) h78317 (SegSum.cons (w := 720) h78318 (SegSum.cons (w := 720) h78319 (SegSum.cons (w := 360) h78334 (SegSum.cons (w := 360) h78335 (SegSum.cons (w := 30) h78593 (SegSum.cons (w := 240) h78595 (SegSum.cons (w := 360) h78599 (SegSum.cons (w := 180) h78601 (SegSum.cons (w := 720) h78603 (SegSum.cons (w := 360) h78607 (SegSum.cons (w := 120) h78612 (SegSum.cons (w := 360) h78613 (SegSum.cons (w := 360) h78614 (SegSum.cons (w := 720) h78615 (SegSum.cons (w := 720) h78617 (SegSum.cons (w := 720) h78619 (SegSum.cons (w := 720) h78620 (SegSum.cons (w := 720) h78621 (SegSum.cons (w := 720) h78622 (SegSum.cons (w := 720) h78623 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S41
