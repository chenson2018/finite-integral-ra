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

namespace RACert.S6N0.C0.S35

open RACert RACert.Problem

theorem cover31475 : P.CoversSplit 26 10 31475 0xc000c000c000c000c0008000c000800000000000000000000000000000000000000000000000000000008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem h31475 : P.leaf 36 31475 = 8471548 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31475) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31475) (weight := fun _ => 1) (xs := [655, 687, 911, 926, 927, 943, 958, 959, 974, 975, 990, 991, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover31475 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover46579 : P.CoversSplit 26 10 46579 0x8000000080000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 873, 930, 1315, 1322]) (by decide +kernel)

theorem h46579 : P.leaf 36 46579 = 4721216 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 46579) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 46579) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 46579) (weight := rowWeight keep2 twice2) (xs := [927, 959, 991, 1023]) check rows elimOK (by decide) (by decide) cover46579 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31477 : P.leaf 36 31477 = 4721216 :=
  orient4 (v := 46579) (by decide) (by decide +kernel) h46579

theorem cover47027 : P.CoversSplit 26 10 47027 0xc000000000000000c00000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000c000000000000000c00000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 873, 930, 1658]) (by decide +kernel)

theorem h47027 : P.leaf 36 47027 = 10541504 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 47027) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 47027) (weight := fun _ => 1) (xs := [191, 254, 255, 446, 447, 510, 511, 703, 766, 767, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover47027 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31478 : P.leaf 36 31478 = 10541504 :=
  orient72 (v := 47027) (by decide) (by decide +kernel) h47027

theorem cover46583 : P.CoversSplit 26 10 46583 0xcc000000cc000400cc000000cc00000000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 930, 1265, 1315, 1658]) (by decide +kernel)

theorem h46583 : P.leaf 36 46583 = 47906912 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 46583) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 46583) (weight := fun _ => 1) (xs := [714, 730, 746, 762, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover46583 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31479 : P.leaf 36 31479 = 47906912 :=
  orient4 (v := 46583) (by decide) (by decide +kernel) h46583

theorem cover47075 : P.CoversSplit 26 10 47075 0xf0000000f0000000f0000000f000000000000000000000000000000000000000f0000000f0000000a0000000a000000000000000000000000000000000000000f0000000c0000000f0000000c000000000000000000000000000000000000000f0000000c0000000a00000008000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 1322, 1658]) (by decide +kernel)

noncomputable def f47075 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (48204800 + i)

theorem c47075_0 : rowSum f47075 0 1024 = 18526320 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 47075) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover47075 (by decide)
  decide +kernel

theorem sum47075 : rowSum f47075 0 1024 = 18526320 :=
  c47075_0

theorem h47075 : P.leaf 36 47075 = 18526320 :=
  leaf_weighted (k := 26) (d := 10) (H := 47075) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 47075) (by decide) (by decide +kernel)) sum47075

theorem h31482 : P.leaf 36 31482 = 18526320 :=
  orient74 (v := 47075) (by decide) (by decide +kernel) h47075

theorem cover31483 : P.CoversSplit 26 10 31483 0xf0f0f0f0f0f0f0c0f0f0a0a0f0f0a08000000000000000000030002000000000000000000000000000000000000000000000000000000000000000000000000000300030000000000030002000000000003000300000000000300020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c31483_0 : P.sumLeaves 26 32238592 1024 = 77812916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31483) (lo := 0) (len := 1024) (W := 77812916) check rows elimOK (by decide) (by decide) cover31483 (by decide)
  decide +kernel

theorem h31483 : P.leaf 36 31483 = 77812916 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 77812916)]) (.cons c31483_0 (.nil)) (by decide) (by decide))

theorem cover46591 : P.CoversSplit 26 10 46591 0xffff0000ffff0404ffff0000ffff000000000000000000000022000000000000050505050505040400000000000000000000000000000000000000000000000000330000000000000033000000000000003300000000000000220000000000000001000100000000000000000000000000010001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f46591 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (47709184 + i)

theorem c46591_0 : rowSum f46591 0 1024 = 320233020 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 46591) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover46591 (by decide)
  decide +kernel

theorem sum46591 : rowSum f46591 0 1024 = 320233020 :=
  c46591_0

theorem h46591 : P.leaf 36 46591 = 320233020 :=
  leaf_weighted (k := 26) (d := 10) (H := 46591) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 46591) (by decide) (by decide +kernel)) sum46591

theorem h31487 : P.leaf 36 31487 = 320233020 :=
  orient4 (v := 46591) (by decide) (by decide +kernel) h46591

theorem cover96740 : P.CoversSplit 26 10 96740 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96740 : P.leaf 36 96740 = 201550 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96740) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96740) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96740 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h31728 : P.leaf 36 31728 = 201550 :=
  orient348 (v := 96740) (by decide) (by decide +kernel) h96740

theorem cover797023 : P.CoversSplit 26 10 797023 0xaa00aa00aa00aa00aa00aa0000000000aa00000088000000aa00000000008800000000000000000000000a00000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 979, 1265, 1273, 1308]) (by decide +kernel)

noncomputable def f797023 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (816151552 + i)

theorem c797023_0 : rowSum f797023 0 1024 = 8014232 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 797023) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover797023 (by decide)
  decide +kernel

theorem sum797023 : rowSum f797023 0 1024 = 8014232 :=
  c797023_0

theorem h797023 : P.leaf 36 797023 = 8014232 :=
  leaf_weighted (k := 26) (d := 10) (H := 797023) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 797023) (by decide) (by decide +kernel)) sum797023

theorem h31729 : P.leaf 36 31729 = 8014232 :=
  orient92 (v := 797023) (by decide) (by decide +kernel) h797023

theorem cover31731 : P.CoversSplit 26 10 31731 0xf000f000f000f000f000a000f000a000f000f000c000c000f000a000c000800800000000000000000000aa000000aa0000000000000000000000aa00000088080000000000000000000000000000000000000000c0c0c0c000000000c0c080880000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f31731 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (32492544 + i)

theorem c31731_0 : rowSum f31731 0 1024 = 65602384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31731) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31731 (by decide)
  decide +kernel

theorem sum31731 : rowSum f31731 0 1024 = 65602384 :=
  c31731_0

theorem h31731 : P.leaf 36 31731 = 65602384 :=
  leaf_weighted (k := 26) (d := 10) (H := 31731) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 31731) (by decide) (by decide +kernel)) sum31731

theorem cover47091 : P.CoversSplit 26 10 47091 0xf0000000f0000000f0000000f000000000000000000000000000000000000000f0000000f0000000a0000000a000000000000000000000000000000000000000f0000000c0000000f0000000c000000000000000000000000000000000000000f0000000c0000000a00000008000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 1322, 1658]) (by decide +kernel)

noncomputable def f47091 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (48221184 + i)

theorem c47091_0 : rowSum f47091 0 1024 = 83196200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 47091) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover47091 (by decide)
  decide +kernel

theorem sum47091 : rowSum f47091 0 1024 = 83196200 :=
  c47091_0

theorem h47091 : P.leaf 36 47091 = 83196200 :=
  leaf_weighted (k := 26) (d := 10) (H := 47091) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 47091) (by decide) (by decide +kernel)) sum47091

theorem h31733 : P.leaf 36 31733 = 83196200 :=
  orient4 (v := 47091) (by decide) (by decide +kernel) h47091

theorem cover31735 : P.CoversSplit 26 10 31735 0xff00ff00ff00fa00ff00aa00ff00aa00ff00ff00cc00c800fa00aa00c8008800ff00fa00ff00fa00fa00a000fa00a000ff00fa00cc00c800fa00a000c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f31735 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (32496640 + i)

theorem c31735_0 : rowSum f31735 0 1019 = 395601896 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31735) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover31735 (by decide)
  decide +kernel

theorem c31735_1 : rowSum f31735 1019 5 = 30569200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31735) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover31735 (by decide)
  decide +kernel

theorem sum31735 : rowSum f31735 0 1024 = 426171096 :=
  rowSum_append (F := f31735) (lo := 0) (n := 1019) (m := 5) (A := 395601896) (B := 30569200) c31735_0 (c31735_1)

theorem h31735 : P.leaf 36 31735 = 426171096 :=
  leaf_weighted (k := 26) (d := 10) (H := 31735) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 31735) (by decide) (by decide +kernel)) sum31735

theorem cover47103 : P.CoversSplit 26 10 47103 0xffffffffffffc8c8fffffafaffffc8c8ffffffffffccc8c8aa88aa88aa888888fffffafaffffc8c8aaaaaaaaaaaa8888fffffafaffccc8c8aa88aa88aa888888ffffffffccccc8c8fffffafaccccc8c8ffccffccccccc8c8aa88aa8888888888fffffafaccccc8c8aaaaaaaa88888888ffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f47103 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (48233472 + i)

theorem c47103_0 : rowSum f47103 0 346 = 503353459 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 47103) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover47103 (by decide)
  decide +kernel

theorem c47103_1 : rowSum f47103 346 146 = 871282596 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 47103) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover47103 (by decide)
  decide +kernel

theorem c47103_2 : rowSum f47103 492 459 = 860262701 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 47103) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover47103 (by decide)
  decide +kernel

theorem c47103_3 : rowSum f47103 951 73 = 341146264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 47103) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover47103 (by decide)
  decide +kernel

theorem sum47103 : rowSum f47103 0 1024 = 2576045020 :=
  rowSum_append (F := f47103) (lo := 0) (n := 346) (m := 678) (A := 503353459) (B := 2072691561) c47103_0 (rowSum_append (F := f47103) (lo := 346) (n := 146) (m := 532) (A := 871282596) (B := 1201408965) c47103_1 (rowSum_append (F := f47103) (lo := 492) (n := 459) (m := 73) (A := 860262701) (B := 341146264) c47103_2 (c47103_3)))

theorem h47103 : P.leaf 36 47103 = 2576045020 :=
  leaf_weighted (k := 26) (d := 10) (H := 47103) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 47103) (by decide) (by decide +kernel)) sum47103

theorem h31743 : P.leaf 36 31743 = 2576045020 :=
  orient4 (v := 47103) (by decide) (by decide +kernel) h47103

theorem cover32243 : P.CoversSplit 26 10 32243 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h32243 : P.leaf 36 32243 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32243) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32243) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32243 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32244 : P.CoversSplit 26 10 32244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32244 : P.leaf 36 32244 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32244) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32244) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32244 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32245 : P.CoversSplit 26 10 32245 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32245 : P.leaf 36 32245 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32245) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32245) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32245 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32247 : P.CoversSplit 26 10 32247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32247 : P.leaf 36 32247 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32247) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32247) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32247 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32252 : P.CoversSplit 26 10 32252 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32252 : P.leaf 36 32252 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32252) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32252) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32252 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32253 : P.CoversSplit 26 10 32253 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32253 : P.leaf 36 32253 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32253) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32253) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32253 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32255 : P.CoversSplit 26 10 32255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h32255 : P.leaf 36 32255 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32255) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32255) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover32255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover88556 : P.CoversSplit 26 10 88556 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h88556 : P.leaf 36 88556 = 134080 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 88556) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 88556) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover88556 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h32496 : P.leaf 36 32496 = 134080 :=
  orient348 (v := 88556) (by decide) (by decide +kernel) h88556

theorem cover32497 : P.CoversSplit 26 10 32497 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h32497 : P.leaf 36 32497 = 4254080 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32497) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32497) (weight := fun _ => 1) (xs := [654, 655, 686, 687, 910, 911, 926, 927, 942, 943, 958, 959, 974, 975, 990, 991, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover32497 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32498 : P.CoversSplit 26 10 32498 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h32498 : P.leaf 36 32498 = 9554000 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32498) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32498) (weight := fun _ => 1) (xs := [654, 655, 686, 687, 910, 911, 926, 927, 942, 943, 958, 959, 974, 975, 990, 991, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover32498 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover32499 : P.CoversSplit 26 10 32499 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h32499 : P.leaf 36 32499 = 23784464 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 32499) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 32499) (weight := fun _ => 1) (xs := [654, 655, 686, 687, 910, 911, 926, 927, 942, 943, 958, 959, 974, 975, 990, 991, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover32499 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover49075 : P.CoversSplit 26 10 49075 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000cc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 1315, 1658]) (by decide +kernel)

noncomputable def f49075 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (50252800 + i)

theorem c49075_0 : rowSum f49075 0 1024 = 61133808 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49075) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover49075 (by decide)
  decide +kernel

theorem sum49075 : rowSum f49075 0 1024 = 61133808 :=
  c49075_0

theorem h49075 : P.leaf 36 49075 = 61133808 :=
  leaf_weighted (k := 26) (d := 10) (H := 49075) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 49075) (by decide) (by decide +kernel)) sum49075

theorem h32502 : P.leaf 36 32502 = 61133808 :=
  orient72 (v := 49075) (by decide) (by decide +kernel) h49075

theorem cover49079 : P.CoversSplit 26 10 49079 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000cc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c00000000000880080000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 1265, 1315, 1658]) (by decide +kernel)

noncomputable def f49079 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (50256896 + i)

theorem c49079_0 : rowSum f49079 0 1024 = 124748000 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49079) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover49079 (by decide)
  decide +kernel

theorem sum49079 : rowSum f49079 0 1024 = 124748000 :=
  c49079_0

theorem h49079 : P.leaf 36 49079 = 124748000 :=
  leaf_weighted (k := 26) (d := 10) (H := 49079) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 49079) (by decide) (by decide +kernel)) sum49079

theorem h32503 : P.leaf 36 32503 = 124748000 :=
  orient72 (v := 49079) (by decide) (by decide +kernel) h49079

theorem cover49010 : P.CoversSplit 26 10 49010 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000a0000000a0000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000220022000000000000000000aa00aa00aa00aa0000000a0000000a0000000000220022000000000000000200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 1315, 1322]) (by decide +kernel)

noncomputable def f49010 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (50186240 + i)

theorem c49010_0 : rowSum f49010 0 1024 = 7238172 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49010) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover49010 (by decide)
  decide +kernel

theorem sum49010 : rowSum f49010 0 1024 = 7238172 :=
  c49010_0

theorem h49010 : P.leaf 36 49010 = 7238172 :=
  leaf_weighted (k := 26) (d := 10) (H := 49010) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 49010) (by decide) (by decide +kernel)) sum49010

theorem h32504 : P.leaf 36 32504 = 7238172 :=
  orient6 (v := 49010) (by decide) (by decide +kernel) h49010

theorem cover49011 : P.CoversSplit 26 10 49011 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00aa00aa00aa0000000a0000000a0000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000220022000000000000000000aa00aa00aa00aa0000000a0000000a0000000000220022000000000000000200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 1315, 1322]) (by decide +kernel)

noncomputable def f49011 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (50187264 + i)

theorem c49011_0 : rowSum f49011 0 1024 = 59119112 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49011) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover49011 (by decide)
  decide +kernel

theorem sum49011 : rowSum f49011 0 1024 = 59119112 :=
  c49011_0

theorem h49011 : P.leaf 36 49011 = 59119112 :=
  leaf_weighted (k := 26) (d := 10) (H := 49011) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 49011) (by decide) (by decide +kernel)) sum49011

theorem h32505 : P.leaf 36 32505 = 59119112 :=
  orient6 (v := 49011) (by decide) (by decide +kernel) h49011

theorem cover32506 : P.CoversSplit 26 10 32506 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32506_0 : P.sumLeaves 26 33286144 1024 = 124874332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32506) (lo := 0) (len := 1024) (W := 124874332) check rows elimOK (by decide) (by decide) cover32506 (by decide)
  decide +kernel

theorem h32506 : P.leaf 36 32506 = 124874332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124874332)]) (.cons c32506_0 (.nil)) (by decide) (by decide))

theorem cover32507 : P.CoversSplit 26 10 32507 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000100000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32507_0 : P.sumLeaves 26 33287168 1024 = 260108342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32507) (lo := 0) (len := 1024) (W := 260108342) check rows elimOK (by decide) (by decide) cover32507 (by decide)
  decide +kernel

theorem h32507 : P.leaf 36 32507 = 260108342 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 260108342)]) (.cons c32507_0 (.nil)) (by decide) (by decide))

theorem cover49083 : P.CoversSplit 26 10 49083 0xffffffff00330000fffffafa0033000000330033003300000000000000000000fffff0f000330000aaaaa0a00022000000330030003300000000000000000000ffffffff00000000fffffafa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f49083 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (50260992 + i)

theorem c49083_0 : rowSum f49083 0 931 = 293541036 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49083) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover49083 (by decide)
  decide +kernel

theorem c49083_1 : rowSum f49083 931 93 = 197764276 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49083) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover49083 (by decide)
  decide +kernel

theorem sum49083 : rowSum f49083 0 1024 = 491305312 :=
  rowSum_append (F := f49083) (lo := 0) (n := 931) (m := 93) (A := 293541036) (B := 197764276) c49083_0 (c49083_1)

theorem h49083 : P.leaf 36 49083 = 491305312 :=
  leaf_weighted (k := 26) (d := 10) (H := 49083) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 49083) (by decide) (by decide +kernel)) sum49083

theorem h32510 : P.leaf 36 32510 = 491305312 :=
  orient72 (v := 49083) (by decide) (by decide +kernel) h49083

theorem cover49087 : P.CoversSplit 26 10 49087 0xffffffff00330000fffffafa0033000000330033003300000000000000000000fffff0f000330000aaaaa0a00022000000330030003300000000000000000000ffffffff00000000fffffafa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f49087 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (50265088 + i)

theorem c49087_0 : rowSum f49087 0 931 = 628859350 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49087) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover49087 (by decide)
  decide +kernel

theorem c49087_1 : rowSum f49087 931 93 = 338437132 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 49087) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover49087 (by decide)
  decide +kernel

theorem sum49087 : rowSum f49087 0 1024 = 967296482 :=
  rowSum_append (F := f49087) (lo := 0) (n := 931) (m := 93) (A := 628859350) (B := 338437132) c49087_0 (c49087_1)

theorem h49087 : P.leaf 36 49087 = 967296482 :=
  leaf_weighted (k := 26) (d := 10) (H := 49087) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 49087) (by decide) (by decide +kernel)) sum49087

theorem h32511 : P.leaf 36 32511 = 967296482 :=
  orient72 (v := 49087) (by decide) (by decide +kernel) h49087

def seg : List (ℕ × ℕ) := [(31475, 720), (31477, 360), (31478, 720), (31479, 720), (31482, 360), (31483, 720), (31487, 360), (31728, 90), (31729, 360), (31731, 180), (31733, 360), (31735, 360), (31743, 90), (32243, 45), (32244, 180), (32245, 360), (32247, 180), (32252, 90), (32253, 180), (32255, 90), (32496, 360), (32497, 360), (32498, 720), (32499, 720), (32502, 360), (32503, 360), (32504, 360), (32505, 360), (32506, 720), (32507, 720), (32510, 360), (32511, 360)]

theorem segOK : checkSeg 20 perms 31475 32736 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 31475 32736 12285 1576462320180 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1576462320180)
    (SegSum.cons (w := 720) h31475 (SegSum.cons (w := 360) h31477 (SegSum.cons (w := 720) h31478 (SegSum.cons (w := 720) h31479 (SegSum.cons (w := 360) h31482 (SegSum.cons (w := 720) h31483 (SegSum.cons (w := 360) h31487 (SegSum.cons (w := 90) h31728 (SegSum.cons (w := 360) h31729 (SegSum.cons (w := 180) h31731 (SegSum.cons (w := 360) h31733 (SegSum.cons (w := 360) h31735 (SegSum.cons (w := 90) h31743 (SegSum.cons (w := 45) h32243 (SegSum.cons (w := 180) h32244 (SegSum.cons (w := 360) h32245 (SegSum.cons (w := 180) h32247 (SegSum.cons (w := 90) h32252 (SegSum.cons (w := 180) h32253 (SegSum.cons (w := 90) h32255 (SegSum.cons (w := 360) h32496 (SegSum.cons (w := 360) h32497 (SegSum.cons (w := 720) h32498 (SegSum.cons (w := 720) h32499 (SegSum.cons (w := 360) h32502 (SegSum.cons (w := 360) h32503 (SegSum.cons (w := 360) h32504 (SegSum.cons (w := 360) h32505 (SegSum.cons (w := 720) h32506 (SegSum.cons (w := 720) h32507 (SegSum.cons (w := 360) h32510 (SegSum.cons (w := 360) h32511 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S35
