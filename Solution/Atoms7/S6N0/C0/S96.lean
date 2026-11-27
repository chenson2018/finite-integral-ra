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

namespace RACert.S6N0.C0.S96

open RACert RACert.Problem

theorem cover228351 : P.CoversSplit 26 10 228351 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228351 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (233831424 + i)

theorem c228351_0 : rowSum f228351 0 210 = 12825695 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228351) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_1 : rowSum f228351 210 141 = 997649050 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228351) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_2 : rowSum f228351 351 102 = 1560415288 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228351) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_3 : rowSum f228351 453 392 = 2343041380 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228351) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_4 : rowSum f228351 845 179 = 3479406872 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228351) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem sum228351 : rowSum f228351 0 1024 = 8393338285 :=
  rowSum_append (F := f228351) (lo := 0) (n := 210) (m := 814) (A := 12825695) (B := 8380512590) c228351_0 (rowSum_append (F := f228351) (lo := 210) (n := 141) (m := 673) (A := 997649050) (B := 7382863540) c228351_1 (rowSum_append (F := f228351) (lo := 351) (n := 102) (m := 571) (A := 1560415288) (B := 5822448252) c228351_2 (rowSum_append (F := f228351) (lo := 453) (n := 392) (m := 179) (A := 2343041380) (B := 3479406872) c228351_3 (c228351_4))))

theorem h228351 : P.leaf 36 228351 = 8393338285 :=
  leaf_weighted (k := 26) (d := 10) (H := 228351) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 228351) (by decide) (by decide +kernel)) sum228351

theorem cover228863 : P.CoversSplit 26 10 228863 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228863 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (234355712 + i)

theorem c228863_0 : rowSum f228863 0 1024 = 28907436 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228863) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228863 (by decide)
  decide +kernel

theorem sum228863 : rowSum f228863 0 1024 = 28907436 :=
  c228863_0

theorem h228863 : P.leaf 36 228863 = 28907436 :=
  leaf_weighted (k := 26) (d := 10) (H := 228863) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 228863) (by decide) (by decide +kernel)) sum228863

theorem cover229047 : P.CoversSplit 26 10 229047 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000003300330000000000330030 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 972, 979]) (by decide +kernel)

noncomputable def f229047 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (234544128 + i)

theorem c229047_0 : rowSum f229047 0 1024 = 188608245 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229047) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover229047 (by decide)
  decide +kernel

theorem sum229047 : rowSum f229047 0 1024 = 188608245 :=
  c229047_0

theorem h229047 : P.leaf 36 229047 = 188608245 :=
  leaf_weighted (k := 26) (d := 10) (H := 229047) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 229047) (by decide) (by decide +kernel)) sum229047

theorem cover229048 : P.CoversSplit 26 10 229048 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229048 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (234545152 + i)

theorem c229048_0 : rowSum f229048 0 1024 = 10186154 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229048) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover229048 (by decide)
  decide +kernel

theorem sum229048 : rowSum f229048 0 1024 = 10186154 :=
  c229048_0

theorem h229048 : P.leaf 36 229048 = 10186154 :=
  leaf_weighted (k := 26) (d := 10) (H := 229048) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 229048) (by decide) (by decide +kernel)) sum229048

theorem cover229049 : P.CoversSplit 26 10 229049 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229049_0 : P.sumLeaves 26 234546176 1024 = 189051915 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229049) (lo := 0) (len := 1024) (W := 189051915) check rows elimOK (by decide) (by decide) cover229049 (by decide)
  decide +kernel

theorem h229049 : P.leaf 36 229049 = 189051915 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 189051915)]) (.cons c229049_0 (.nil)) (by decide) (by decide))

theorem cover229051 : P.CoversSplit 26 10 229051 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229051 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (234548224 + i)

theorem c229051_0 : rowSum f229051 0 1024 = 334923694 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229051) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover229051 (by decide)
  decide +kernel

theorem sum229051 : rowSum f229051 0 1024 = 334923694 :=
  c229051_0

theorem h229051 : P.leaf 36 229051 = 334923694 :=
  leaf_weighted (k := 26) (d := 10) (H := 229051) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 229051) (by decide) (by decide +kernel)) sum229051

theorem cover229052 : P.CoversSplit 26 10 229052 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229052 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (234549248 + i)

theorem c229052_0 : rowSum f229052 0 1024 = 339397218 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229052) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover229052 (by decide)
  decide +kernel

theorem sum229052 : rowSum f229052 0 1024 = 339397218 :=
  c229052_0

theorem h229052 : P.leaf 36 229052 = 339397218 :=
  leaf_weighted (k := 26) (d := 10) (H := 229052) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 229052) (by decide) (by decide +kernel)) sum229052

theorem cover229053 : P.CoversSplit 26 10 229053 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229053_0 : P.sumLeaves 26 234550272 998 = 344776437 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229053) (lo := 0) (len := 998) (W := 344776437) check rows elimOK (by decide) (by decide) cover229053 (by decide)
  decide +kernel

theorem c229053_1 : P.sumLeaves 26 234551270 26 = 249750222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229053) (lo := 998) (len := 26) (W := 249750222) check rows elimOK (by decide) (by decide) cover229053 (by decide)
  decide +kernel

theorem h229053 : P.leaf 36 229053 = 594526659 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 344776437), (26, 249750222)]) (.cons c229053_0 (.cons c229053_1 (.nil))) (by decide) (by decide))

theorem cover229055 : P.CoversSplit 26 10 229055 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229055 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (234552320 + i)

theorem c229055_0 : rowSum f229055 0 1024 = 873454748 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229055) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover229055 (by decide)
  decide +kernel

theorem sum229055 : rowSum f229055 0 1024 = 873454748 :=
  c229055_0

theorem h229055 : P.leaf 36 229055 = 873454748 :=
  leaf_weighted (k := 26) (d := 10) (H := 229055) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 229055) (by decide) (by decide +kernel)) sum229055

theorem cover229069 : P.CoversSplit 26 10 229069 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229069_0 : P.sumLeaves 26 234566656 1024 = 71185308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229069) (lo := 0) (len := 1024) (W := 71185308) check rows elimOK (by decide) (by decide) cover229069 (by decide)
  decide +kernel

theorem h229069 : P.leaf 36 229069 = 71185308 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 71185308)]) (.cons c229069_0 (.nil)) (by decide) (by decide))

theorem cover229071 : P.CoversSplit 26 10 229071 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229071 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (234568704 + i)

theorem c229071_0 : rowSum f229071 0 1024 = 599428428 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229071) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover229071 (by decide)
  decide +kernel

theorem sum229071 : rowSum f229071 0 1024 = 599428428 :=
  c229071_0

theorem h229071 : P.leaf 36 229071 = 599428428 :=
  leaf_weighted (k := 26) (d := 10) (H := 229071) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 229071) (by decide) (by decide +kernel)) sum229071

theorem cover229084 : P.CoversSplit 26 10 229084 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229084 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (234582016 + i)

theorem c229084_0 : rowSum f229084 0 1024 = 404902368 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229084) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover229084 (by decide)
  decide +kernel

theorem sum229084 : rowSum f229084 0 1024 = 404902368 :=
  c229084_0

theorem h229084 : P.leaf 36 229084 = 404902368 :=
  leaf_weighted (k := 26) (d := 10) (H := 229084) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 229084) (by decide) (by decide +kernel)) sum229084

theorem cover229085 : P.CoversSplit 26 10 229085 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229085_0 : P.sumLeaves 26 234583040 1024 = 695033356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229085) (lo := 0) (len := 1024) (W := 695033356) check rows elimOK (by decide) (by decide) cover229085 (by decide)
  decide +kernel

theorem h229085 : P.leaf 36 229085 = 695033356 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 695033356)]) (.cons c229085_0 (.nil)) (by decide) (by decide))

theorem cover229087 : P.CoversSplit 26 10 229087 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229087 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (234585088 + i)

theorem c229087_0 : rowSum f229087 0 1024 = 1028931305 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229087) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover229087 (by decide)
  decide +kernel

theorem sum229087 : rowSum f229087 0 1024 = 1028931305 :=
  c229087_0

theorem h229087 : P.leaf 36 229087 = 1028931305 :=
  leaf_weighted (k := 26) (d := 10) (H := 229087) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 229087) (by decide) (by decide +kernel)) sum229087

theorem cover229101 : P.CoversSplit 26 10 229101 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229101 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (234599424 + i)

theorem c229101_0 : rowSum f229101 0 917 = 174986845 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229101) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229101 (by decide)
  decide +kernel

theorem c229101_1 : rowSum f229101 917 107 = 343643412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229101) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229101 (by decide)
  decide +kernel

theorem sum229101 : rowSum f229101 0 1024 = 518630257 :=
  rowSum_append (F := f229101) (lo := 0) (n := 917) (m := 107) (A := 174986845) (B := 343643412) c229101_0 (c229101_1)

theorem h229101 : P.leaf 36 229101 = 518630257 :=
  leaf_weighted (k := 26) (d := 10) (H := 229101) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 229101) (by decide) (by decide +kernel)) sum229101

theorem cover229102 : P.CoversSplit 26 10 229102 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229102_0 : P.sumLeaves 26 234600448 735 = 163944042 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229102) (lo := 0) (len := 735) (W := 163944042) check rows elimOK (by decide) (by decide) cover229102 (by decide)
  decide +kernel

theorem c229102_1 : P.sumLeaves 26 234601183 228 = 532880410 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229102) (lo := 735) (len := 228) (W := 532880410) check rows elimOK (by decide) (by decide) cover229102 (by decide)
  decide +kernel

theorem c229102_2 : P.sumLeaves 26 234601411 61 = 601266868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229102) (lo := 963) (len := 61) (W := 601266868) check rows elimOK (by decide) (by decide) cover229102 (by decide)
  decide +kernel

theorem h229102 : P.leaf 36 229102 = 1298091320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 163944042), (228, 532880410), (61, 601266868)]) (.cons c229102_0 (.cons c229102_1 (.cons c229102_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(228351, 60), (228863, 15), (229047, 60), (229048, 180), (229049, 720), (229051, 360), (229052, 360), (229053, 720), (229055, 360), (229069, 360), (229071, 360), (229084, 360), (229085, 720), (229087, 360), (229101, 180), (229102, 720)]

theorem segOK : checkSeg 20 perms 228351 229103 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 228351 229103 5895 3924564002160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3924564002160)
    (SegSum.cons (w := 60) h228351 (SegSum.cons (w := 15) h228863 (SegSum.cons (w := 60) h229047 (SegSum.cons (w := 180) h229048 (SegSum.cons (w := 720) h229049 (SegSum.cons (w := 360) h229051 (SegSum.cons (w := 360) h229052 (SegSum.cons (w := 720) h229053 (SegSum.cons (w := 360) h229055 (SegSum.cons (w := 360) h229069 (SegSum.cons (w := 360) h229071 (SegSum.cons (w := 360) h229084 (SegSum.cons (w := 720) h229085 (SegSum.cons (w := 360) h229087 (SegSum.cons (w := 180) h229101 (SegSum.cons (w := 720) h229102 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S96
