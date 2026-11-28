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

namespace RACert.S6N0.C0.S82

open RACert RACert.Problem

theorem cover228863 : P.CoversSplit 26 10 228863 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h228863 : P.leaf 36 228863 = 28907436 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 228863) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 228863) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 228863) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover228863 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover376247 : P.CoversSplit 26 10 376247 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000002200220000000000000000000000000000000000000000003300330000000000220022 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 930]) (by decide +kernel)

noncomputable def f376247 (i : ℕ) := rowWeight keep17 twice17 i * P.leaf 26 (385276928 + i)

theorem c376247_0 : rowSum f376247 0 1024 = 188608245 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 376247) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover376247 (by decide)
  decide +kernel

theorem sum376247 : rowSum f376247 0 1024 = 188608245 :=
  c376247_0

theorem h376247 : P.leaf 36 376247 = 188608245 :=
  leaf_weighted (k := 26) (d := 10) (H := 376247) (keep := keep17) (twice := twice17) rows (by decide) (by decide) (bal17) (invRow17 (H := 376247) (by decide) (by decide +kernel)) sum376247

theorem h229047 : P.leaf 36 229047 = 188608245 :=
  orient4 (v := 376247) (by decide) (by decide +kernel) h376247

theorem cover605787 : P.CoversSplit 26 10 605787 0xa000000000000000a00000000000000000000000000000000000000000000000a000000000000000a0000a000000000000000000000000000000000000000000a000000000200000a00000000020000000000000000000000000000000000000a000000000200000a0000a000020000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 587, 930, 1273]) (by decide +kernel)

theorem h605787 : P.leaf 36 605787 = 10186154 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 605787) (keep := keep16) (twice := twice16) rows (by decide) (by decide) bal16 (invRow16 (H := 605787) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 605787) (weight := rowWeight keep16 twice16) (xs := [129, 149, 169, 171, 189, 191, 213, 253, 255, 405, 445, 447, 469, 509, 511, 681, 683, 701, 703, 765, 767, 957, 959, 1021, 1023]) check rows elimOK (by decide) (by decide) cover605787 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h229048 : P.leaf 36 229048 = 10186154 :=
  orient85 (v := 605787) (by decide) (by decide +kernel) h605787

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
  leaf_weighted (k := 26) (d := 10) (H := 229051) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 229051) (by decide) (by decide +kernel)) sum229051

theorem cover229052 : P.CoversSplit 26 10 229052 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229052 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (234549248 + i)

theorem c229052_0 : rowSum f229052 0 1024 = 339397218 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229052) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover229052 (by decide)
  decide +kernel

theorem sum229052 : rowSum f229052 0 1024 = 339397218 :=
  c229052_0

theorem h229052 : P.leaf 36 229052 = 339397218 :=
  leaf_weighted (k := 26) (d := 10) (H := 229052) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 229052) (by decide) (by decide +kernel)) sum229052

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
  leaf_weighted (k := 26) (d := 10) (H := 229055) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 229055) (by decide) (by decide +kernel)) sum229055

theorem cover376267 : P.CoversSplit 26 10 376267 0xaaaaaaaaaaaaaaaaaaaaababaaaaabab00000000000000000000000000220022000000000000000000000a0a00000a0a0000000000000000000000000000000200000000002200220000000000220023000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 1273, 1665]) (by decide +kernel)

noncomputable def f376267 (i : ℕ) := rowWeight keep16 twice16 i * P.leaf 26 (385297408 + i)

theorem c376267_0 : rowSum f376267 0 1024 = 71185308 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 376267) (keep := keep16) (twice := twice16) check rows elimOK (by decide) (by decide) cover376267 (by decide)
  decide +kernel

theorem sum376267 : rowSum f376267 0 1024 = 71185308 :=
  c376267_0

theorem h376267 : P.leaf 36 376267 = 71185308 :=
  leaf_weighted (k := 26) (d := 10) (H := 376267) (keep := keep16) (twice := twice16) rows (by decide) (by decide) (bal16) (invRow16 (H := 376267) (by decide) (by decide +kernel)) sum376267

theorem h229069 : P.leaf 36 229069 = 71185308 :=
  orient4 (v := 376267) (by decide) (by decide +kernel) h376267

theorem cover229071 : P.CoversSplit 26 10 229071 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229071 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (234568704 + i)

theorem c229071_0 : rowSum f229071 0 1024 = 599428428 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229071) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover229071 (by decide)
  decide +kernel

theorem sum229071 : rowSum f229071 0 1024 = 599428428 :=
  c229071_0

theorem h229071 : P.leaf 36 229071 = 599428428 :=
  leaf_weighted (k := 26) (d := 10) (H := 229071) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 229071) (by decide) (by decide +kernel)) sum229071

theorem cover229084 : P.CoversSplit 26 10 229084 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229084 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (234582016 + i)

theorem c229084_0 : rowSum f229084 0 1024 = 404902368 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229084) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover229084 (by decide)
  decide +kernel

theorem sum229084 : rowSum f229084 0 1024 = 404902368 :=
  c229084_0

theorem h229084 : P.leaf 36 229084 = 404902368 :=
  leaf_weighted (k := 26) (d := 10) (H := 229084) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 229084) (by decide) (by decide +kernel)) sum229084

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
  leaf_weighted (k := 26) (d := 10) (H := 229087) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 229087) (by decide) (by decide +kernel)) sum229087

theorem cover376283 : P.CoversSplit 26 10 376283 0xaaaaaaaaaaaaaaaaaaaaababaaaaabab00000000000000000000000000220022000000000000000000000a0a00000a0a0000000000000000000000000000000200000000002200220000000000220023000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1665]) (by decide +kernel)

noncomputable def f376283 (i : ℕ) := rowWeight keep16 twice16 i * P.leaf 26 (385313792 + i)

theorem c376283_0 : rowSum f376283 0 1024 = 518630257 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 376283) (keep := keep16) (twice := twice16) check rows elimOK (by decide) (by decide) cover376283 (by decide)
  decide +kernel

theorem sum376283 : rowSum f376283 0 1024 = 518630257 :=
  c376283_0

theorem h376283 : P.leaf 36 376283 = 518630257 :=
  leaf_weighted (k := 26) (d := 10) (H := 376283) (keep := keep16) (twice := twice16) rows (by decide) (by decide) (bal16) (invRow16 (H := 376283) (by decide) (by decide +kernel)) sum376283

theorem h229101 : P.leaf 36 229101 = 518630257 :=
  orient4 (v := 376283) (by decide) (by decide +kernel) h376283

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

theorem cover229103 : P.CoversSplit 26 10 229103 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229103_0 : P.sumLeaves 26 234601472 735 = 283780350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 0) (len := 735) (W := 283780350) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem c229103_1 : P.sumLeaves 26 234602207 228 = 806341394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 735) (len := 228) (W := 806341394) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem c229103_2 : P.sumLeaves 26 234602435 61 = 826236858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229103) (lo := 963) (len := 61) (W := 826236858) check rows elimOK (by decide) (by decide) cover229103 (by decide)
  decide +kernel

theorem h229103 : P.leaf 36 229103 = 1916358602 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 283780350), (228, 806341394), (61, 826236858)]) (.cons c229103_0 (.cons c229103_1 (.cons c229103_2 (.nil)))) (by decide) (by decide))

theorem cover229118 : P.CoversSplit 26 10 229118 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229118 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (234616832 + i)

theorem c229118_0 : rowSum f229118 0 917 = 708892371 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229118) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem c229118_1 : rowSum f229118 917 107 = 1548774780 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229118) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover229118 (by decide)
  decide +kernel

theorem sum229118 : rowSum f229118 0 1024 = 2257667151 :=
  rowSum_append (F := f229118) (lo := 0) (n := 917) (m := 107) (A := 708892371) (B := 1548774780) c229118_0 (c229118_1)

theorem h229118 : P.leaf 36 229118 = 2257667151 :=
  leaf_weighted (k := 26) (d := 10) (H := 229118) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 229118) (by decide) (by decide +kernel)) sum229118

def seg : List (ℕ × ℕ) := [(228863, 15), (229047, 60), (229048, 180), (229049, 720), (229051, 360), (229052, 360), (229053, 720), (229055, 360), (229069, 360), (229071, 360), (229084, 360), (229085, 720), (229087, 360), (229101, 180), (229102, 720), (229103, 720), (229118, 360)]

theorem segOK : checkSeg 20 perms 228863 229119 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 228863 229119 6915 5613502072860 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5613502072860)
    (SegSum.cons (w := 15) h228863 (SegSum.cons (w := 60) h229047 (SegSum.cons (w := 180) h229048 (SegSum.cons (w := 720) h229049 (SegSum.cons (w := 360) h229051 (SegSum.cons (w := 360) h229052 (SegSum.cons (w := 720) h229053 (SegSum.cons (w := 360) h229055 (SegSum.cons (w := 360) h229069 (SegSum.cons (w := 360) h229071 (SegSum.cons (w := 360) h229084 (SegSum.cons (w := 720) h229085 (SegSum.cons (w := 360) h229087 (SegSum.cons (w := 180) h229101 (SegSum.cons (w := 720) h229102 (SegSum.cons (w := 720) h229103 (SegSum.cons (w := 360) h229118 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))) (by decide)

end RACert.S6N0.C0.S82
