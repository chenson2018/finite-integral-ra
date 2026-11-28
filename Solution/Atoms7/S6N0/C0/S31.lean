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

namespace RACert.S6N0.C0.S31

open RACert RACert.Problem

theorem cover15853 : P.CoversSplit 26 10 15853 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15853 : P.leaf 36 15853 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15853) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15853) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15853 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15854 : P.CoversSplit 26 10 15854 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15854 : P.leaf 36 15854 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15854) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15854) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15854 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15855 : P.CoversSplit 26 10 15855 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15855 : P.leaf 36 15855 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15855) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15855) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15855 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15859 : P.CoversSplit 26 10 15859 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h15859 : P.leaf 36 15859 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15859) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15859) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15859 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15860 : P.CoversSplit 26 10 15860 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15860 : P.leaf 36 15860 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15860) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15860) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15860 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15861 : P.CoversSplit 26 10 15861 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15861 : P.leaf 36 15861 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15861) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15861) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15861 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15862 : P.CoversSplit 26 10 15862 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15862 : P.leaf 36 15862 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15862) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15862) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15862 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15863 : P.CoversSplit 26 10 15863 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15863 : P.leaf 36 15863 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15863) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15863) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15863 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15864 : P.CoversSplit 26 10 15864 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15864 : P.leaf 36 15864 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15864) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15864) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15864 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15865 : P.CoversSplit 26 10 15865 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15865 : P.leaf 36 15865 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15865) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15865) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15865 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15866 : P.CoversSplit 26 10 15866 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15866 : P.leaf 36 15866 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15866) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15866) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15866 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15867 : P.CoversSplit 26 10 15867 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15867 : P.leaf 36 15867 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15867) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15867) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15867 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15868 : P.CoversSplit 26 10 15868 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15868 : P.leaf 36 15868 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15868) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15868) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15868 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15869 : P.CoversSplit 26 10 15869 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15869 : P.leaf 36 15869 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15869) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15869) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15869 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15870 : P.CoversSplit 26 10 15870 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15870 : P.leaf 36 15870 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15870) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15870) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15870 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15871 : P.CoversSplit 26 10 15871 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15871 : P.leaf 36 15871 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15871) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15871) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15871 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover108867 : P.CoversSplit 26 10 108867 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 629, 636, 881, 930, 1273, 1322]) (by decide +kernel)

theorem h108867 : P.leaf 36 108867 = 1792 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 108867) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 108867) (weight := fun _ => 1) (xs := [683, 1023]) check rows elimOK (by decide) (by decide) cover108867 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16176 : P.leaf 36 16176 = 1792 :=
  orient84 (v := 108867) (by decide) (by decide +kernel) h108867

theorem cover16177 : P.CoversSplit 26 10 16177 0x8000800000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem h16177 : P.leaf 36 16177 = 98624 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16177) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16177) (weight := fun _ => 1) (xs := [686, 750, 1007, 1023]) check rows elimOK (by decide) (by decide) cover16177 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16178 : P.CoversSplit 26 10 16178 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem h16178 : P.leaf 36 16178 = 132428 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16178) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16178) (weight := fun _ => 1) (xs := [1007, 1023]) check rows elimOK (by decide) (by decide) cover16178 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16179 : P.CoversSplit 26 10 16179 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h16179 : P.leaf 36 16179 = 929536 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16179) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16179) (weight := fun _ => 1) (xs := [1007, 1023]) check rows elimOK (by decide) (by decide) cover16179 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover44515 : P.CoversSplit 26 10 44515 0x8800880000000000880080000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 629, 636, 881, 930, 1265, 1273, 1322]) (by decide +kernel)

theorem h44515 : P.leaf 36 44515 = 1886080 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 44515) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 44515) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 44515) (weight := rowWeight keep1 twice1) (xs := [687, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover44515 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16182 : P.leaf 36 16182 = 1886080 :=
  orient72 (v := 44515) (by decide) (by decide +kernel) h44515

theorem cover109031 : P.CoversSplit 26 10 109031 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 881, 930, 1266, 1273]) (by decide +kernel)

theorem h109031 : P.leaf 36 109031 = 8822848 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 109031) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 109031) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 109031) (weight := rowWeight keep1 twice1) (xs := [938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover109031 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16183 : P.leaf 36 16183 = 8822848 :=
  orient84 (v := 109031) (by decide) (by decide +kernel) h109031

theorem cover40418 : P.CoversSplit 26 10 40418 0x8000800080008000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 922, 930, 965]) (by decide +kernel)

theorem h40418 : P.leaf 36 40418 = 45330 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 40418) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 40418) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 40418) (weight := rowWeight keep0 twice0) (xs := [12, 268, 524, 780, 975, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover40418 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16184 : P.leaf 36 16184 = 45330 :=
  orient6 (v := 40418) (by decide) (by decide +kernel) h40418

theorem cover40419 : P.CoversSplit 26 10 40419 0x8000800080008000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 922, 930, 965]) (by decide +kernel)

theorem h40419 : P.leaf 36 40419 = 1166520 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 40419) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 40419) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 40419) (weight := rowWeight keep0 twice0) (xs := [12, 268, 524, 780, 975, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover40419 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16185 : P.leaf 36 16185 = 1166520 :=
  orient6 (v := 40419) (by decide) (by decide +kernel) h40419

theorem cover47923 : P.CoversSplit 26 10 47923 0x8800880000000000000000000000000000000000000000000000000000000000880080000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000008800800000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 1315, 1665]) (by decide +kernel)

theorem h47923 : P.leaf 36 47923 = 2329284 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 47923) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 47923) (weight := fun _ => 1) (xs := [239, 251, 255, 491, 495, 507, 511, 751, 763, 767, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover47923 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16186 : P.leaf 36 16186 = 2329284 :=
  orient74 (v := 47923) (by decide) (by decide +kernel) h47923

theorem cover16187 : P.CoversSplit 26 10 16187 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem h16187 : P.leaf 36 16187 = 8269264 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16187) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16187) (weight := fun _ => 1) (xs := [453, 469, 485, 501, 837, 869, 885, 965, 997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover16187 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover44523 : P.CoversSplit 26 10 44523 0xaaaaaaaa00000022aaaaa0a00000002000000000000000000022002000000000000000000000000000000000000000000000000000000000000000000000000000220022002200220022002000220020002200220000000000220020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1265, 1273, 1322, 1665]) (by decide +kernel)

noncomputable def f44523 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (45591552 + i)

theorem c44523_0 : rowSum f44523 0 1024 = 14821432 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 44523) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover44523 (by decide)
  decide +kernel

theorem sum44523 : rowSum f44523 0 1024 = 14821432 :=
  c44523_0

theorem h44523 : P.leaf 36 44523 = 14821432 :=
  leaf_weighted (k := 26) (d := 10) (H := 44523) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 44523) (by decide) (by decide +kernel)) sum44523

theorem h16190 : P.leaf 36 16190 = 14821432 :=
  orient72 (v := 44523) (by decide) (by decide +kernel) h44523

theorem cover109543 : P.CoversSplit 26 10 109543 0xff00ff0000000000ff00ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff33ff3333332222ff33ff3333332222333333330000000022222222000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 881, 930, 1266, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f109543 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (112172032 + i)

theorem c109543_0 : rowSum f109543 0 1024 = 49348876 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 109543) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover109543 (by decide)
  decide +kernel

theorem sum109543 : rowSum f109543 0 1024 = 49348876 :=
  c109543_0

theorem h109543 : P.leaf 36 109543 = 49348876 :=
  leaf_weighted (k := 26) (d := 10) (H := 109543) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 109543) (by decide) (by decide +kernel)) sum109543

theorem h16191 : P.leaf 36 16191 = 49348876 :=
  orient84 (v := 109543) (by decide) (by decide +kernel) h109543

theorem cover16208 : P.CoversSplit 26 10 16208 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16208 : P.leaf 36 16208 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16208) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16208) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16208 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16209 : P.CoversSplit 26 10 16209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16209 : P.leaf 36 16209 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16209) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16209) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16209 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16210 : P.CoversSplit 26 10 16210 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16210 : P.leaf 36 16210 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16210) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16210) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16210 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16211 : P.CoversSplit 26 10 16211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16211 : P.leaf 36 16211 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16211) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16211) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16211 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(15853, 720), (15854, 720), (15855, 720), (15859, 360), (15860, 720), (15861, 720), (15862, 720), (15863, 720), (15864, 720), (15865, 720), (15866, 720), (15867, 720), (15868, 720), (15869, 720), (15870, 720), (15871, 720), (16176, 360), (16177, 360), (16178, 720), (16179, 720), (16182, 360), (16183, 360), (16184, 360), (16185, 360), (16186, 720), (16187, 720), (16190, 360), (16191, 360), (16208, 720), (16209, 720), (16210, 720), (16211, 720)]

theorem segOK : checkSeg 20 perms 15853 16212 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 15853 16212 19800 35824509360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 35824509360)
    (SegSum.cons (w := 720) h15853 (SegSum.cons (w := 720) h15854 (SegSum.cons (w := 720) h15855 (SegSum.cons (w := 360) h15859 (SegSum.cons (w := 720) h15860 (SegSum.cons (w := 720) h15861 (SegSum.cons (w := 720) h15862 (SegSum.cons (w := 720) h15863 (SegSum.cons (w := 720) h15864 (SegSum.cons (w := 720) h15865 (SegSum.cons (w := 720) h15866 (SegSum.cons (w := 720) h15867 (SegSum.cons (w := 720) h15868 (SegSum.cons (w := 720) h15869 (SegSum.cons (w := 720) h15870 (SegSum.cons (w := 720) h15871 (SegSum.cons (w := 360) h16176 (SegSum.cons (w := 360) h16177 (SegSum.cons (w := 720) h16178 (SegSum.cons (w := 720) h16179 (SegSum.cons (w := 360) h16182 (SegSum.cons (w := 360) h16183 (SegSum.cons (w := 360) h16184 (SegSum.cons (w := 360) h16185 (SegSum.cons (w := 720) h16186 (SegSum.cons (w := 720) h16187 (SegSum.cons (w := 360) h16190 (SegSum.cons (w := 360) h16191 (SegSum.cons (w := 720) h16208 (SegSum.cons (w := 720) h16209 (SegSum.cons (w := 720) h16210 (SegSum.cons (w := 720) h16211 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S31
