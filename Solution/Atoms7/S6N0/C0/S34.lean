/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S34

open RACert RACert.Problem

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

theorem c16319_0 : P.sumLeaves 26 16710656 880 = 81090970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16319) (lo := 0) (len := 880) (W := 81090970) check rows elimOK (by decide) (by decide) cover16319 (by decide)
  decide +kernel

theorem c16319_1 : P.sumLeaves 26 16711536 144 = 227307156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16319) (lo := 880) (len := 144) (W := 227307156) check rows elimOK (by decide) (by decide) cover16319 (by decide)
  decide +kernel

theorem h16319 : P.leaf 36 16319 = 308398126 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(880, 81090970), (144, 227307156)]) (.cons c16319_0 (.cons c16319_1 (.nil))) (by decide) (by decide))

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

theorem cover16368 : P.CoversSplit 26 10 16368 0xf000f000f000f000f000f000f000f000000000000000000000000000000000000000fa000000fa000000aa000000aa00000000000000000000000000000000000000000000000000000000000000000000000000f0c0f0c800000000a080a08800000000000000000000000000000000000000000000fac8000000000000aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1658]) (by decide +kernel)

theorem c16368_0 : P.sumLeaves 26 16760832 1024 = 302584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16368) (lo := 0) (len := 1024) (W := 302584) check rows elimOK (by decide) (by decide) cover16368 (by decide)
  decide +kernel

theorem h16368 : P.leaf 36 16368 = 302584 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 302584)]) (.cons c16368_0 (.nil)) (by decide) (by decide))

theorem cover16369 : P.CoversSplit 26 10 16369 0xf000f000f000f000f000f000f000f000000000000000000000000000000000000000fa000000fa000000aa000000aa00000000000000000000000000000000000000000000000000000000000000000000000000f0c0f0c800000000a080a08800000000000000000000000000000000000000000000fac8000000000000aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1658]) (by decide +kernel)

theorem c16369_0 : P.sumLeaves 26 16761856 1024 = 10229850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16369) (lo := 0) (len := 1024) (W := 10229850) check rows elimOK (by decide) (by decide) cover16369 (by decide)
  decide +kernel

theorem h16369 : P.leaf 36 16369 = 10229850 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10229850)]) (.cons c16369_0 (.nil)) (by decide) (by decide))

theorem cover16370 : P.CoversSplit 26 10 16370 0xf000f000f000f000f000f000f000f000000000000000000000000000000000000000fa000000fa000000aa000000aa000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000200020000000000000000000000000000000000000000000000032000000000000002200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c16370_0 : P.sumLeaves 26 16762880 1024 = 11955014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16370) (lo := 0) (len := 1024) (W := 11955014) check rows elimOK (by decide) (by decide) cover16370 (by decide)
  decide +kernel

theorem h16370 : P.leaf 36 16370 = 11955014 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11955014)]) (.cons c16370_0 (.nil)) (by decide) (by decide))

theorem cover16371 : P.CoversSplit 26 10 16371 0xf000f000f000f000f000f000f000f000000000000000000000000000000000000000fa000000fa000000aa000000aa000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000200020000000000000000000000000000000000000000000000032000000000000002200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c16371_0 : P.sumLeaves 26 16763904 1024 = 33682912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16371) (lo := 0) (len := 1024) (W := 33682912) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem h16371 : P.leaf 36 16371 = 33682912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33682912)]) (.cons c16371_0 (.nil)) (by decide) (by decide))

theorem cover16374 : P.CoversSplit 26 10 16374 0xff00ff00ff00fa00ff00fa00ff00fa0000000000000000000000000000000000ff00f000ff00f000aa00a000aa00a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 880, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16374_0 : P.sumLeaves 26 16766976 1007 = 74077076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16374) (lo := 0) (len := 1007) (W := 74077076) check rows elimOK (by decide) (by decide) cover16374 (by decide)
  decide +kernel

theorem c16374_1 : P.sumLeaves 26 16767983 17 = 21184184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16374) (lo := 1007) (len := 17) (W := 21184184) check rows elimOK (by decide) (by decide) cover16374 (by decide)
  decide +kernel

theorem h16374 : P.leaf 36 16374 = 95261260 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1007, 74077076), (17, 21184184)]) (.cons c16374_0 (.cons c16374_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(16318, 360), (16319, 360), (16320, 180), (16321, 360), (16322, 360), (16323, 720), (16326, 180), (16327, 360), (16329, 180), (16331, 360), (16335, 180), (16336, 720), (16337, 720), (16338, 720), (16339, 720), (16340, 720), (16341, 720), (16342, 720), (16343, 720), (16344, 720), (16345, 720), (16346, 720), (16347, 720), (16348, 720), (16349, 720), (16350, 720), (16351, 720), (16368, 360), (16369, 360), (16370, 720), (16371, 720), (16374, 360)]

theorem segOK : checkSeg 20 perms 16318 16375 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16318 16375 17640 217475120880 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 217475120880)
    (SegSum.cons (w := 360) h16318 (SegSum.cons (w := 360) h16319 (SegSum.cons (w := 180) h16320 (SegSum.cons (w := 360) h16321 (SegSum.cons (w := 360) h16322 (SegSum.cons (w := 720) h16323 (SegSum.cons (w := 180) h16326 (SegSum.cons (w := 360) h16327 (SegSum.cons (w := 180) h16329 (SegSum.cons (w := 360) h16331 (SegSum.cons (w := 180) h16335 (SegSum.cons (w := 720) h16336 (SegSum.cons (w := 720) h16337 (SegSum.cons (w := 720) h16338 (SegSum.cons (w := 720) h16339 (SegSum.cons (w := 720) h16340 (SegSum.cons (w := 720) h16341 (SegSum.cons (w := 720) h16342 (SegSum.cons (w := 720) h16343 (SegSum.cons (w := 720) h16344 (SegSum.cons (w := 720) h16345 (SegSum.cons (w := 720) h16346 (SegSum.cons (w := 720) h16347 (SegSum.cons (w := 720) h16348 (SegSum.cons (w := 720) h16349 (SegSum.cons (w := 720) h16350 (SegSum.cons (w := 720) h16351 (SegSum.cons (w := 360) h16368 (SegSum.cons (w := 360) h16369 (SegSum.cons (w := 720) h16370 (SegSum.cons (w := 720) h16371 (SegSum.cons (w := 360) h16374 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S34
