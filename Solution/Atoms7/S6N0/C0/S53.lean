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

namespace RACert.S6N0.C0.S53

open RACert RACert.Problem

theorem cover88517 : P.CoversSplit 26 10 88517 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88517 : P.leaf 36 88517 = 34448 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88517) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88517) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88517 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88519 : P.CoversSplit 26 10 88519 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88519 : P.leaf 36 88519 = 343632 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88519) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88519) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88519 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88525 : P.CoversSplit 26 10 88525 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88525 : P.leaf 36 88525 = 70088 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88525) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88525) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88525 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88527 : P.CoversSplit 26 10 88527 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88527 : P.leaf 36 88527 = 377552 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88527) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88527) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88527 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88534 : P.CoversSplit 26 10 88534 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88534 : P.leaf 36 88534 = 3278990 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88534) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88534) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88534 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88535 : P.CoversSplit 26 10 88535 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88535 : P.leaf 36 88535 = 3978058 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88535) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88535) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88535 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88540 : P.CoversSplit 26 10 88540 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88540 : P.leaf 36 88540 = 500960 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88540) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88540) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88540 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88541 : P.CoversSplit 26 10 88541 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88541 : P.leaf 36 88541 = 667612 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88541) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88541) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88541 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88542 : P.CoversSplit 26 10 88542 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88542 : P.leaf 36 88542 = 4881826 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88542) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88542) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88542 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88543 : P.CoversSplit 26 10 88543 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88543 : P.leaf 36 88543 = 5697700 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88543) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88543) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88543 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88557 : P.CoversSplit 26 10 88557 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88557 : P.leaf 36 88557 = 139936 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88557) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88557) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88557 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88558 : P.CoversSplit 26 10 88558 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88558 : P.leaf 36 88558 = 691008 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88558) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88558) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88558 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88559 : P.CoversSplit 26 10 88559 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88559 : P.leaf 36 88559 = 737336 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88559) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88559) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88559 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88574 : P.CoversSplit 26 10 88574 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88574 : P.leaf 36 88574 = 8794202 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88574) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88574) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88574 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88575 : P.CoversSplit 26 10 88575 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88575 : P.leaf 36 88575 = 9370534 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88575) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88575) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88575 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88662 : P.CoversSplit 26 10 88662 0x8800000088020401000000000000000000000000000000000000000000000000000004000000040100000000000000000000000000000000000000000000000000000000002200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88662 : P.leaf 36 88662 = 519156 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 88662) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88662) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88662) (weight := rowWeight keep4 twice4) (xs := [448, 465, 469, 704, 714, 746, 960, 970, 977, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover88662 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88663 : P.CoversSplit 26 10 88663 0x8800000088020401000000000000000000000000000000000000000000000000000004000000040100000000000000000000000000000000000000000000000000000000002200010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88663 : P.leaf 36 88663 = 1106101 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 88663) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 88663) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88663) (weight := rowWeight keep4 twice4) (xs := [192, 448, 465, 469, 704, 714, 746, 960, 970, 977, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover88663 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover275774 : P.CoversSplit 26 10 275774 0xc0c0000400100001000000000000000000000000000000000000000000000000000004040000000100000000000000000000000000000000000000000000000000000000003000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 538, 579, 629, 636, 873, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h275774 : P.leaf 36 275774 = 1626096 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 275774) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 275774) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 275774) (weight := rowWeight keep8 twice8) (xs := [448, 468, 469, 704, 738, 746, 960, 980, 994, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover275774 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88670 : P.leaf 36 88670 = 1626096 :=
  orient6 (v := 275774) (by decide) (by decide +kernel) h275774

theorem cover275775 : P.CoversSplit 26 10 275775 0xc0c0000400100001000000000000000000000000000000000000000000000000000004040000000100000000000000000000000000000000000000000000000000000000003000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h275775 : P.leaf 36 275775 = 3458642 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 275775) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 275775) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 275775) (weight := rowWeight keep8 twice8) (xs := [192, 448, 468, 469, 704, 738, 746, 960, 980, 994, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover275775 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88671 : P.leaf 36 88671 = 3458642 :=
  orient6 (v := 275775) (by decide) (by decide +kernel) h275775

theorem cover113571 : P.CoversSplit 26 10 113571 0xcc00cc0000000000cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc33cc3300330030cc33c83200330030003300330000000000220022000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 1266, 1315, 1658]) (by decide +kernel)

noncomputable def f113571 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (116296704 + i)

theorem c113571_0 : rowSum f113571 0 1024 = 6784884 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 113571) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover113571 (by decide)
  decide +kernel

theorem sum113571 : rowSum f113571 0 1024 = 6784884 :=
  c113571_0

theorem h113571 : P.leaf 36 113571 = 6784884 :=
  leaf_weighted (k := 26) (d := 10) (H := 113571) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 113571) (by decide) (by decide +kernel)) sum113571

theorem h88702 : P.leaf 36 88702 = 6784884 :=
  orient93 (v := 113571) (by decide) (by decide +kernel) h113571

theorem cover113575 : P.CoversSplit 26 10 113575 0xcc00cc0000000000cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc33cc3300330030cc33cc3300330030003300330000000000220022000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 1266, 1315, 1658]) (by decide +kernel)

noncomputable def f113575 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (116300800 + i)

theorem c113575_0 : rowSum f113575 0 1024 = 14215296 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 113575) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover113575 (by decide)
  decide +kernel

theorem sum113575 : rowSum f113575 0 1024 = 14215296 :=
  c113575_0

theorem h113575 : P.leaf 36 113575 = 14215296 :=
  leaf_weighted (k := 26) (d := 10) (H := 113575) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 113575) (by decide) (by decide +kernel)) sum113575

theorem h88703 : P.leaf 36 88703 = 14215296 :=
  orient93 (v := 113575) (by decide) (by decide +kernel) h113575

theorem cover304577 : P.CoversSplit 26 10 304577 0x88000000a0000000080000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 881, 930, 958, 1265, 1272, 1665]) (by decide +kernel)

theorem h304577 : P.leaf 36 304577 = 2401 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 304577) (keep := keep18) (twice := twice18) rows (by decide) (by decide) bal18 (invRow18 (H := 304577) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 304577) (weight := rowWeight keep18 twice18) (xs := [129, 469, 683, 955, 989, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover304577 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88770 : P.leaf 36 88770 = 2401 :=
  orient74 (v := 304577) (by decide) (by decide +kernel) h304577

theorem cover88771 : P.CoversSplit 26 10 88771 0x8000000080000000800000008000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000200001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 972, 979, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem h88771 : P.leaf 36 88771 = 98125 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88771) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88771) (weight := fun _ => 1) (xs := [384, 405, 469, 898, 927, 959, 991, 1023]) check rows elimOK (by decide) (by decide) cover88771 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover103879 : P.CoversSplit 26 10 103879 0xc0000000c0000000000000000000000000000000000000000000000000100000000000000000000004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 873, 930, 1315, 1658, 1665]) (by decide +kernel)

theorem h103879 : P.leaf 36 103879 = 1334330 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103879) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103879) (weight := fun _ => 1) (xs := [528, 666, 698, 788, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103879 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88775 : P.leaf 36 88775 = 1334330 :=
  orient4 (v := 103879) (by decide) (by decide +kernel) h103879

theorem cover304579 : P.CoversSplit 26 10 304579 0x8800000080000000080000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 881, 930, 958, 1265, 1665]) (by decide +kernel)

theorem h304579 : P.leaf 36 304579 = 56868 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 304579) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 304579) (weight := fun _ => 1) (xs := [683, 955, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover304579 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88778 : P.leaf 36 88778 = 56868 :=
  orient74 (v := 304579) (by decide) (by decide +kernel) h304579

theorem cover276247 : P.CoversSplit 26 10 276247 0xc0000000000000000000000000000000000000000000000000000000000000004000000000000000040000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000004000000000000000040000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 615, 873, 930, 1265, 1272, 1273, 1658]) (by decide +kernel)

theorem h276247 : P.leaf 36 276247 = 678592 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276247) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276247) (weight := fun _ => 1) (xs := [186, 254, 510, 511, 698, 766, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276247 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88779 : P.leaf 36 88779 = 678592 :=
  orient6 (v := 276247) (by decide) (by decide +kernel) h276247

theorem cover288987 : P.CoversSplit 26 10 288987 0xaa00000022000000000000000000000000000000000000000000000000020000000000000000000000000a00000002000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 629, 636, 881, 923, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem h288987 : P.leaf 36 288987 = 614326 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 288987) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288987) (weight := fun _ => 1) (xs := [513, 649, 681, 683, 785, 985, 989, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover288987 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88782 : P.leaf 36 88782 = 614326 :=
  orient80 (v := 288987) (by decide) (by decide +kernel) h288987

theorem cover288991 : P.CoversSplit 26 10 288991 0xaa00ab002200220000000000000000000000000000000000000000000002000200000f000000020000000a00000002000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 587, 629, 636, 881, 923, 972, 979, 1265, 1273, 1658, 1665]) (ps := [(19, [1265], [1273])]) (by decide +kernel)

theorem h288991 : P.leaf 36 288991 = 5398116 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 288991) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 288991) (weight := fun _ => 1) (xs := [513, 649, 681, 683, 713, 744, 745, 746, 747, 769, 785, 969, 973, 985, 989, 1000, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover288991 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88783 : P.leaf 36 88783 = 5398116 :=
  orient80 (v := 288991) (by decide) (by decide +kernel) h288991

theorem cover304537 : P.CoversSplit 26 10 304537 0x8888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 531, 537, 538, 629, 930, 958, 1265, 1272, 1665]) (by decide +kernel)

theorem h304537 : P.leaf 36 304537 = 160032 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 304537) (keep := keep16) (twice := twice16) rows (by decide) (by decide) bal16 (invRow16 (H := 304537) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 304537) (weight := rowWeight keep16 twice16) (xs := [1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover304537 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88788 : P.leaf 36 88788 = 160032 :=
  orient84 (v := 304537) (by decide) (by decide +kernel) h304537

theorem cover103907 : P.CoversSplit 26 10 103907 0x8000000080000000000000000000000000000000000000000000000000000000000000000000000000000400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 873, 922, 930, 1315]) (by decide +kernel)

theorem h103907 : P.leaf 36 103907 = 1329464 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103907) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103907) (weight := fun _ => 1) (xs := [650, 682, 991, 1023]) check rows elimOK (by decide) (by decide) cover103907 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88789 : P.leaf 36 88789 = 1329464 :=
  orient4 (v := 103907) (by decide) (by decide +kernel) h103907

theorem cover103910 : P.CoversSplit 26 10 103910 0xcc000000cc000400000000000000000000000000000000000000000000110000040004000400040004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 531, 629, 636, 873, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h103910 : P.leaf 36 103910 = 5540898 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103910) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103910) (weight := fun _ => 1) (xs := [528, 666, 698, 714, 730, 746, 762, 784, 788, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103910 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88790 : P.leaf 36 88790 = 5540898 :=
  orient4 (v := 103910) (by decide) (by decide +kernel) h103910

theorem cover103911 : P.CoversSplit 26 10 103911 0xcc000000cc000400000000000000000000000000000000000000000000110000040004000400040004000000040000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 922, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h103911 : P.leaf 36 103911 = 12044486 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 103911) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 103911) (weight := fun _ => 1) (xs := [528, 666, 698, 714, 730, 746, 762, 784, 788, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover103911 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88791 : P.leaf 36 88791 = 12044486 :=
  orient4 (v := 103911) (by decide) (by decide +kernel) h103911

def seg : List (ℕ × ℕ) := [(88517, 360), (88519, 360), (88525, 720), (88527, 360), (88534, 180), (88535, 360), (88540, 720), (88541, 720), (88542, 720), (88543, 720), (88557, 360), (88558, 720), (88559, 720), (88574, 360), (88575, 360), (88662, 120), (88663, 120), (88670, 360), (88671, 360), (88702, 360), (88703, 360), (88770, 120), (88771, 720), (88775, 720), (88778, 720), (88779, 720), (88782, 720), (88783, 720), (88788, 360), (88789, 720), (88790, 720), (88791, 720)]

theorem segOK : checkSeg 20 perms 88517 88793 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88517 88793 16380 47573578680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 47573578680)
    (SegSum.cons (w := 360) h88517 (SegSum.cons (w := 360) h88519 (SegSum.cons (w := 720) h88525 (SegSum.cons (w := 360) h88527 (SegSum.cons (w := 180) h88534 (SegSum.cons (w := 360) h88535 (SegSum.cons (w := 720) h88540 (SegSum.cons (w := 720) h88541 (SegSum.cons (w := 720) h88542 (SegSum.cons (w := 720) h88543 (SegSum.cons (w := 360) h88557 (SegSum.cons (w := 720) h88558 (SegSum.cons (w := 720) h88559 (SegSum.cons (w := 360) h88574 (SegSum.cons (w := 360) h88575 (SegSum.cons (w := 120) h88662 (SegSum.cons (w := 120) h88663 (SegSum.cons (w := 360) h88670 (SegSum.cons (w := 360) h88671 (SegSum.cons (w := 360) h88702 (SegSum.cons (w := 360) h88703 (SegSum.cons (w := 120) h88770 (SegSum.cons (w := 720) h88771 (SegSum.cons (w := 720) h88775 (SegSum.cons (w := 720) h88778 (SegSum.cons (w := 720) h88779 (SegSum.cons (w := 720) h88782 (SegSum.cons (w := 720) h88783 (SegSum.cons (w := 360) h88788 (SegSum.cons (w := 720) h88789 (SegSum.cons (w := 720) h88790 (SegSum.cons (w := 720) h88791 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S53
