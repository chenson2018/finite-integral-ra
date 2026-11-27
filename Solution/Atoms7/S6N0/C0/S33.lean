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

namespace RACert.S6N0.C0.S33

open RACert RACert.Problem

theorem cover16314 : P.CoversSplit 26 10 16314 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000050500000001000000000000000000000001000000010000000000000000000300031003000300030003000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16314_0 : P.sumLeaves 26 16705536 1024 = 19444986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16314) (lo := 0) (len := 1024) (W := 19444986) check rows elimOK (by decide) (by decide) cover16314 (by decide)
  decide +kernel

theorem h16314 : P.leaf 36 16314 = 19444986 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19444986)]) (.cons c16314_0 (.nil)) (by decide) (by decide))

theorem cover16315 : P.CoversSplit 26 10 16315 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000050500000001000000000000000000000001000000010000000000000000000300031003000300030003000300030000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16315_0 : P.sumLeaves 26 16706560 1024 = 67496199 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16315) (lo := 0) (len := 1024) (W := 67496199) check rows elimOK (by decide) (by decide) cover16315 (by decide)
  decide +kernel

theorem h16315 : P.leaf 36 16315 = 67496199 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 67496199)]) (.cons c16315_0 (.nil)) (by decide) (by decide))

theorem cover16318 : P.CoversSplit 26 10 16318 0xfffffffa00000030fffffafa0000003000330032000000300000000000000000fffff0f000000030aaaaa0a0000000200033003000000030000000000000000000330032003300300033003200330030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16318_0 : P.sumLeaves 26 16709632 944 = 37418944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16318) (lo := 0) (len := 944) (W := 37418944) check rows elimOK (by decide) (by decide) cover16318 (by decide)
  decide +kernel

theorem c16318_1 : P.sumLeaves 26 16710576 80 = 61210942 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16318) (lo := 944) (len := 80) (W := 61210942) check rows elimOK (by decide) (by decide) cover16318 (by decide)
  decide +kernel

theorem h16318 : P.leaf 36 16318 = 98629886 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(944, 37418944), (80, 61210942)]) (.cons c16318_0 (.cons c16318_1 (.nil))) (by decide) (by decide))

theorem cover16319 : P.CoversSplit 26 10 16319 0xfffffffa00000030fffffafa0000003000330032000000300000000000000000fffff0f000000030aaaaa0a0000000200033003000000030000000000000000000330032003300300033003200330030000000000000000000000000000000000033003000330030002200200022002000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16319_0 : P.sumLeaves 26 16710656 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16319) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover16319 (by decide)
  decide +kernel

theorem contract16319_1 : P.leaf 32 261106 = 47744 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 261106) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (29, 0, 1322), (31, 0, 1322), (9, 1, 1609), (28, 1, 1658), (5, 1, 629), (20, 1, 1665)]) (ids := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 28, 30, 31, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 12, 1, 13, 17, 18, 19, 20, 1, 0, 14, 0, 15, 16]) (bs := [15, 4]) (W := 47744) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16319_1 : P.sumLeaves 26 16710784 64 = 47744 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261106) rows (by decide) (by decide)).symm.trans contract16319_1

theorem contract16319_2 : P.leaf 32 261107 = 68096 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 261107) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (29, 0, 1322), (31, 0, 1322), (9, 1, 1609), (20, 1, 1665)]) (ids := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 24, 26, 28, 30, 31, 22, 23, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 12, 1, 13, 19, 20, 14, 21, 15, 0, 16, 0, 17, 18]) (bs := [17, 3]) (W := 68096) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16319_2 : P.sumLeaves 26 16710848 64 = 68096 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261107) rows (by decide) (by decide)).symm.trans contract16319_2

theorem c16319_3 : P.sumLeaves 26 16710912 688 = 119412486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16319) (lo := 256) (len := 688) (W := 119412486) check rows elimOK (by decide) (by decide) cover16319 (by decide)
  decide +kernel

theorem c16319_4 : P.sumLeaves 26 16711600 80 = 188869800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16319) (lo := 944) (len := 80) (W := 188869800) check rows elimOK (by decide) (by decide) cover16319 (by decide)
  decide +kernel

theorem h16319 : P.leaf 36 16319 = 308398126 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 47744), (64, 68096), (688, 119412486), (80, 188869800)]) (.cons c16319_0 (.cons c16319_1 (.cons c16319_2 (.cons c16319_3 (.cons c16319_4 (.nil)))))) (by decide) (by decide))

theorem cover16320 : P.CoversSplit 26 10 16320 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16320_0 : P.sumLeaves 26 16711680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16320) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16320 (by decide)
  decide +kernel

theorem h16320 : P.leaf 36 16320 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16320_0 (.nil)) (by decide) (by decide))

theorem cover16321 : P.CoversSplit 26 10 16321 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16321_0 : P.sumLeaves 26 16712704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16321) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16321 (by decide)
  decide +kernel

theorem h16321 : P.leaf 36 16321 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16321_0 (.nil)) (by decide) (by decide))

theorem cover16322 : P.CoversSplit 26 10 16322 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16322_0 : P.sumLeaves 26 16713728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16322) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16322 (by decide)
  decide +kernel

theorem h16322 : P.leaf 36 16322 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16322_0 (.nil)) (by decide) (by decide))

theorem cover16323 : P.CoversSplit 26 10 16323 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16323_0 : P.sumLeaves 26 16714752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16323) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16323 (by decide)
  decide +kernel

theorem h16323 : P.leaf 36 16323 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16323_0 (.nil)) (by decide) (by decide))

theorem cover16326 : P.CoversSplit 26 10 16326 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16326_0 : P.sumLeaves 26 16717824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16326) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16326 (by decide)
  decide +kernel

theorem h16326 : P.leaf 36 16326 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16326_0 (.nil)) (by decide) (by decide))

theorem cover16327 : P.CoversSplit 26 10 16327 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16327_0 : P.sumLeaves 26 16718848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16327) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16327 (by decide)
  decide +kernel

theorem h16327 : P.leaf 36 16327 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16327_0 (.nil)) (by decide) (by decide))

theorem cover16329 : P.CoversSplit 26 10 16329 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16329_0 : P.sumLeaves 26 16720896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16329) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16329 (by decide)
  decide +kernel

theorem h16329 : P.leaf 36 16329 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16329_0 (.nil)) (by decide) (by decide))

theorem cover16331 : P.CoversSplit 26 10 16331 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16331_0 : P.sumLeaves 26 16722944 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16331) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16331 (by decide)
  decide +kernel

theorem h16331 : P.leaf 36 16331 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16331_0 (.nil)) (by decide) (by decide))

theorem cover16335 : P.CoversSplit 26 10 16335 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c16335_0 : P.sumLeaves 26 16727040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16335) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16335 (by decide)
  decide +kernel

theorem h16335 : P.leaf 36 16335 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16335_0 (.nil)) (by decide) (by decide))

theorem cover16336 : P.CoversSplit 26 10 16336 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16336_0 : P.sumLeaves 26 16728064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16336) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16336 (by decide)
  decide +kernel

theorem h16336 : P.leaf 36 16336 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16336_0 (.nil)) (by decide) (by decide))

theorem cover16337 : P.CoversSplit 26 10 16337 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16337_0 : P.sumLeaves 26 16729088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16337) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16337 (by decide)
  decide +kernel

theorem h16337 : P.leaf 36 16337 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16337_0 (.nil)) (by decide) (by decide))

theorem cover16338 : P.CoversSplit 26 10 16338 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16338_0 : P.sumLeaves 26 16730112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16338) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16338 (by decide)
  decide +kernel

theorem h16338 : P.leaf 36 16338 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16338_0 (.nil)) (by decide) (by decide))

theorem cover16339 : P.CoversSplit 26 10 16339 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16339_0 : P.sumLeaves 26 16731136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16339) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16339 (by decide)
  decide +kernel

theorem h16339 : P.leaf 36 16339 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16339_0 (.nil)) (by decide) (by decide))

theorem cover16340 : P.CoversSplit 26 10 16340 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16340_0 : P.sumLeaves 26 16732160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16340) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16340 (by decide)
  decide +kernel

theorem h16340 : P.leaf 36 16340 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16340_0 (.nil)) (by decide) (by decide))

theorem cover16341 : P.CoversSplit 26 10 16341 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16341_0 : P.sumLeaves 26 16733184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16341) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16341 (by decide)
  decide +kernel

theorem h16341 : P.leaf 36 16341 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16341_0 (.nil)) (by decide) (by decide))

theorem cover16342 : P.CoversSplit 26 10 16342 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16342_0 : P.sumLeaves 26 16734208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16342) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16342 (by decide)
  decide +kernel

theorem h16342 : P.leaf 36 16342 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16342_0 (.nil)) (by decide) (by decide))

theorem cover16343 : P.CoversSplit 26 10 16343 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16343_0 : P.sumLeaves 26 16735232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16343) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16343 (by decide)
  decide +kernel

theorem h16343 : P.leaf 36 16343 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16343_0 (.nil)) (by decide) (by decide))

theorem cover16344 : P.CoversSplit 26 10 16344 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16344_0 : P.sumLeaves 26 16736256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16344) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16344 (by decide)
  decide +kernel

theorem h16344 : P.leaf 36 16344 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16344_0 (.nil)) (by decide) (by decide))

theorem cover16345 : P.CoversSplit 26 10 16345 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16345_0 : P.sumLeaves 26 16737280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16345) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16345 (by decide)
  decide +kernel

theorem h16345 : P.leaf 36 16345 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16345_0 (.nil)) (by decide) (by decide))

theorem cover16346 : P.CoversSplit 26 10 16346 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16346_0 : P.sumLeaves 26 16738304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16346) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16346 (by decide)
  decide +kernel

theorem h16346 : P.leaf 36 16346 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16346_0 (.nil)) (by decide) (by decide))

theorem cover16347 : P.CoversSplit 26 10 16347 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16347_0 : P.sumLeaves 26 16739328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16347) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16347 (by decide)
  decide +kernel

theorem h16347 : P.leaf 36 16347 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16347_0 (.nil)) (by decide) (by decide))

theorem cover16348 : P.CoversSplit 26 10 16348 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16348_0 : P.sumLeaves 26 16740352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16348) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16348 (by decide)
  decide +kernel

theorem h16348 : P.leaf 36 16348 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16348_0 (.nil)) (by decide) (by decide))

theorem cover16349 : P.CoversSplit 26 10 16349 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16349_0 : P.sumLeaves 26 16741376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16349) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16349 (by decide)
  decide +kernel

theorem h16349 : P.leaf 36 16349 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16349_0 (.nil)) (by decide) (by decide))

theorem cover16350 : P.CoversSplit 26 10 16350 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16350_0 : P.sumLeaves 26 16742400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16350) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16350 (by decide)
  decide +kernel

theorem h16350 : P.leaf 36 16350 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16350_0 (.nil)) (by decide) (by decide))

theorem cover16351 : P.CoversSplit 26 10 16351 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16351_0 : P.sumLeaves 26 16743424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16351) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16351 (by decide)
  decide +kernel

theorem h16351 : P.leaf 36 16351 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16351_0 (.nil)) (by decide) (by decide))

theorem cover16368 : P.CoversSplit 26 10 16368 0xf000f000f000f000f000f000f000f000000000000000000000000000000000000000aa000000aa000000aa000000aa00000000000000000000000000000000000000000000000000000000000000000000000000f0c0f0c800000000a080a08800000000000000000000000000000000000000000000aa88000000000000aa88 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1658]) (ps := [(21, [1658], [929])]) (by decide +kernel)

theorem contract16368_0 : P.leaf 32 261888 = 40 := by
  exact leaf_contract_factors (k := 32) (b := 6) (H := 261888) (ss := [(22, 1, 433), (2, 1, 475), (7, 1, 825), (13, 0, 874), (6, 0, 461), (3, 0, 412), (4, 0, 409), (5, 0, 409), (10, 0, 409), (11, 0, 410), (12, 0, 411), (17, 0, 531), (32, 20, 529), (20, 0, 531), (16, 0, 516), (18, 0, 516), (24, 19, 515), (19, 0, 516), (33, 0, 517), (21, 0, 522), (25, 0, 522), (26, 0, 530), (27, 0, 538), (8, 1, 1210), (9, 1, 1609), (28, 1, 1658)]) (ids := [12, 27, 29, 13, 21, 28]) (cs := [1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 1, 3, 7, 4, 0, 0]) (bs := [3, 3]) (W := 40) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_0 : P.sumLeaves 26 16760832 64 = 40 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261888) rows (by decide) (by decide)).symm.trans contract16368_0

theorem contract16368_1 : P.leaf 32 261889 = 0 := by
  exact leaf_contract_zero (ss := [(22, 1, 433), (2, 1, 475), (4, 1, 580), (3, 1, 409), (5, 1, 411), (6, 1, 412), (7, 1, 825), (10, 1, 458), (11, 1, 459), (12, 1, 460), (13, 1, 461), (21, 1, 867)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c16368_1 : P.sumLeaves 26 16760896 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261889) rows (by decide) (by decide)).symm.trans contract16368_1

theorem c16368_2 : P.sumLeaves 26 16760960 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16368) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover16368 (by decide)
  decide +kernel

theorem contract16368_3 : P.leaf 32 261892 = 7104 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 261892) (ss := [(2, 1, 475), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (7, 1, 458), (10, 1, 458), (11, 1, 459), (12, 1, 460), (21, 1, 867), (31, 0, 930), (8, 1, 486), (29, 1, 489), (33, 0, 930), (27, 1, 881), (28, 1, 1658)]) (ids := [7, 12, 13, 14, 15, 16, 17, 18, 22, 23, 24, 28, 30, 20, 21]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 9, 1, 15, 16, 10, 11, 12, 1, 1, 1, 13, 0, 14, 0]) (bs := [13, 2]) (W := 7104) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_3 : P.sumLeaves 26 16761088 64 = 7104 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261892) rows (by decide) (by decide)).symm.trans contract16368_3

theorem contract16368_4 : P.leaf 32 261893 = 14016 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 261893) (ss := [(2, 1, 475), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (7, 1, 458), (10, 1, 458), (11, 1, 459), (12, 1, 460), (21, 1, 867), (31, 0, 930), (8, 1, 486), (29, 1, 489), (33, 0, 930), (27, 1, 881)]) (ids := [7, 12, 13, 14, 15, 16, 17, 18, 22, 23, 24, 26, 28, 30, 20, 21]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 9, 1, 16, 17, 10, 11, 12, 1, 13, 1, 14, 0, 15, 0]) (bs := [14, 2]) (W := 14016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_4 : P.sumLeaves 26 16761152 64 = 14016 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261893) rows (by decide) (by decide)).symm.trans contract16368_4

theorem c16368_5 : P.sumLeaves 26 16761216 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16368) (lo := 384) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover16368 (by decide)
  decide +kernel

theorem contract16368_6 : P.leaf 32 261898 = 64 := by
  exact leaf_contract_factors (k := 32) (b := 7) (H := 261898) (ss := [(2, 1, 475), (13, 0, 923), (10, 0, 461), (11, 0, 458), (12, 0, 458), (7, 1, 818), (3, 0, 458), (4, 0, 409), (5, 0, 409), (6, 0, 409), (22, 1, 426), (20, 1, 580), (29, 1, 636), (16, 1, 867), (17, 1, 874), (18, 1, 879), (21, 0, 929), (19, 0, 916), (8, 1, 515), (14, 1, 858), (31, 1, 930), (32, 0, 972), (26, 1, 530), (9, 1, 1609), (28, 1, 1658)]) (ids := [13, 23, 28, 21, 22, 25, 31]) (cs := [1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 2, 1, 1, 1, 0, 1, 0, 1, 5, 6, 3, 1, 7, 1, 1, 4, 1, 0, 8]) (bs := [3, 4]) (W := 64) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_6 : P.sumLeaves 26 16761472 64 = 64 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261898) rows (by decide) (by decide)).symm.trans contract16368_6

theorem contract16368_7 : P.leaf 32 261899 = 208 := by
  exact leaf_contract_factors (k := 32) (b := 9) (H := 261899) (ss := [(2, 1, 475), (13, 0, 923), (10, 0, 461), (11, 0, 458), (12, 0, 458), (7, 1, 818), (3, 0, 458), (4, 0, 409), (5, 0, 409), (6, 0, 409), (22, 1, 426), (29, 1, 636), (16, 1, 867), (17, 1, 874), (18, 1, 879), (21, 0, 929), (19, 0, 916), (8, 1, 515), (14, 1, 858), (31, 1, 930), (32, 0, 972), (9, 1, 1609), (28, 1, 1658)]) (ids := [13, 18, 23, 24, 28, 21, 22, 25, 31]) (cs := [1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 2, 1, 1, 1, 0, 3, 0, 1, 7, 8, 4, 5, 9, 1, 1, 6, 1, 0, 10]) (bs := [5, 4]) (W := 208) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_7 : P.sumLeaves 26 16761536 64 = 208 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261899) rows (by decide) (by decide)).symm.trans contract16368_7

theorem c16368_8 : P.sumLeaves 26 16761600 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16368) (lo := 768) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover16368 (by decide)
  decide +kernel

theorem contract16368_9 : P.leaf 32 261902 = 136256 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 261902) (ss := [(2, 1, 475), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (7, 1, 458), (10, 1, 458), (11, 1, 459), (12, 1, 460), (21, 1, 929), (31, 1, 930), (15, 1, 916), (30, 1, 972)]) (ids := [6, 7, 12, 14, 15, 16, 17, 18, 22, 23, 24, 26, 27, 30, 20, 21, 25, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 6, 7, 8, 9, 1, 16, 17, 10, 11, 12, 18, 13, 14, 1, 1, 15, 19]) (bs := [14, 4]) (W := 136256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_9 : P.sumLeaves 26 16761728 64 = 136256 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261902) rows (by decide) (by decide)).symm.trans contract16368_9

theorem contract16368_10 : P.leaf 32 261903 = 144896 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 261903) (ss := [(2, 1, 475), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (7, 1, 458), (10, 1, 458), (11, 1, 459), (12, 1, 460), (21, 1, 929), (31, 1, 930), (15, 1, 916), (30, 1, 972)]) (ids := [6, 7, 12, 14, 15, 16, 17, 18, 22, 23, 26, 27, 20, 21, 24, 25, 30, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 6, 7, 8, 9, 1, 14, 15, 10, 11, 16, 17, 12, 13, 1, 1, 18, 19]) (bs := [12, 6]) (W := 144896) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16368_10 : P.sumLeaves 26 16761792 64 = 144896 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261903) rows (by decide) (by decide)).symm.trans contract16368_10

theorem h16368 : P.leaf 36 16368 = 302584 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 40), (64, 0), (128, 0), (64, 7104), (64, 14016), (256, 0), (64, 64), (64, 208), (128, 0), (64, 136256), (64, 144896)]) (.cons c16368_0 (.cons c16368_1 (.cons c16368_2 (.cons c16368_3 (.cons c16368_4 (.cons c16368_5 (.cons c16368_6 (.cons c16368_7 (.cons c16368_8 (.cons c16368_9 (.cons c16368_10 (.nil)))))))))))) (by decide) (by decide))

theorem cover16369 : P.CoversSplit 26 10 16369 0xf000f000f000f000f000f000f000f000000000000000000000000000000000000000aa000000aa000000aa000000aa00000000000000000000000000000000000000000000000000000000000000000000000000f0c0f0c800000000a080a08800000000000000000000000000000000000000000000aa88000000000000aa88 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1658]) (ps := [(21, [1658], [929])]) (by decide +kernel)

theorem contract16369_0 : P.leaf 32 261904 = 868 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 261904) (ss := [(22, 1, 433), (2, 1, 475), (7, 1, 825), (13, 0, 923), (16, 1, 867), (17, 1, 874), (3, 1, 531), (21, 0, 929), (5, 4, 586), (19, 0, 916), (33, 0, 930), (32, 0, 972), (8, 1, 1210), (9, 1, 1609), (28, 1, 1658)]) (ids := [2, 4, 8, 9, 10, 12, 13, 16, 18, 22, 23, 24, 25, 27, 28, 29, 21]) (cs := [1, 1, 2, 2, 3, 1, 1, 1, 4, 5, 6, 0, 7, 8, 1, 1, 9, 0, 10, 0, 1, 18, 11, 12, 13, 14, 1, 15, 16, 17, 0, 0]) (bs := [16, 1]) (W := 868) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16369_0 : P.sumLeaves 26 16761856 64 = 868 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261904) rows (by decide) (by decide)).symm.trans contract16369_0

theorem contract16369_1 : P.leaf 32 261905 = 1320 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 261905) (ss := [(22, 1, 433), (2, 1, 475), (4, 1, 580), (5, 1, 629), (3, 1, 537), (7, 1, 825), (13, 0, 923), (16, 1, 867), (17, 1, 874), (21, 0, 929), (19, 0, 916), (33, 0, 930), (32, 0, 972), (8, 1, 1210), (9, 1, 1609), (28, 1, 1658)]) (ids := [4, 8, 9, 10, 12, 13, 16, 18, 22, 23, 24, 25, 27, 28, 29, 21]) (cs := [1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 0, 6, 7, 1, 1, 8, 0, 9, 0, 1, 17, 10, 11, 12, 13, 1, 14, 15, 16, 0, 0]) (bs := [15, 1]) (W := 1320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16369_1 : P.sumLeaves 26 16761920 64 = 1320 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 261905) rows (by decide) (by decide)).symm.trans contract16369_1

theorem c16369_2 : P.sumLeaves 26 16761984 896 = 10227662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16369) (lo := 128) (len := 896) (W := 10227662) check rows elimOK (by decide) (by decide) cover16369 (by decide)
  decide +kernel

theorem h16369 : P.leaf 36 16369 = 10229850 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 868), (64, 1320), (896, 10227662)]) (.cons c16369_0 (.cons c16369_1 (.cons c16369_2 (.nil)))) (by decide) (by decide))

theorem cover16370 : P.CoversSplit 26 10 16370 0xf000f000f000f000f000f000f000f0000000000000000000000000000000000000000a0000000a0000000a0000000a000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000200020000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1315, 1658]) (ps := [(13, [923], [874, 972])]) (by decide +kernel)

theorem c16370_0 : P.sumLeaves 26 16762880 1024 = 11955014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16370) (lo := 0) (len := 1024) (W := 11955014) check rows elimOK (by decide) (by decide) cover16370 (by decide)
  decide +kernel

theorem h16370 : P.leaf 36 16370 = 11955014 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11955014)]) (.cons c16370_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(16314, 720), (16315, 720), (16318, 360), (16319, 360), (16320, 180), (16321, 360), (16322, 360), (16323, 720), (16326, 180), (16327, 360), (16329, 180), (16331, 360), (16335, 180), (16336, 720), (16337, 720), (16338, 720), (16339, 720), (16340, 720), (16341, 720), (16342, 720), (16343, 720), (16344, 720), (16345, 720), (16346, 720), (16347, 720), (16348, 720), (16349, 720), (16350, 720), (16351, 720), (16368, 360), (16369, 360), (16370, 720)]

theorem segOK : checkSeg 20 perms 16314 16371 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16314 16371 18000 221527023840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 221527023840)
    (SegSum.cons (w := 720) h16314 (SegSum.cons (w := 720) h16315 (SegSum.cons (w := 360) h16318 (SegSum.cons (w := 360) h16319 (SegSum.cons (w := 180) h16320 (SegSum.cons (w := 360) h16321 (SegSum.cons (w := 360) h16322 (SegSum.cons (w := 720) h16323 (SegSum.cons (w := 180) h16326 (SegSum.cons (w := 360) h16327 (SegSum.cons (w := 180) h16329 (SegSum.cons (w := 360) h16331 (SegSum.cons (w := 180) h16335 (SegSum.cons (w := 720) h16336 (SegSum.cons (w := 720) h16337 (SegSum.cons (w := 720) h16338 (SegSum.cons (w := 720) h16339 (SegSum.cons (w := 720) h16340 (SegSum.cons (w := 720) h16341 (SegSum.cons (w := 720) h16342 (SegSum.cons (w := 720) h16343 (SegSum.cons (w := 720) h16344 (SegSum.cons (w := 720) h16345 (SegSum.cons (w := 720) h16346 (SegSum.cons (w := 720) h16347 (SegSum.cons (w := 720) h16348 (SegSum.cons (w := 720) h16349 (SegSum.cons (w := 720) h16350 (SegSum.cons (w := 720) h16351 (SegSum.cons (w := 360) h16368 (SegSum.cons (w := 360) h16369 (SegSum.cons (w := 720) h16370 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S33
