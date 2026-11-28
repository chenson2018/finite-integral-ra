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

theorem cover44539 : P.CoversSplit 26 10 44539 0xaaaaaaaa00000022aaaaaaaa0000002200000000000000000022002200000000000000000000000000000a0a000000020000000000000000000000020000000000220022002200220022002200220022002200220000000000220022000000000000000000000000000000020000000200000000000000000000000200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1265, 1273, 1322, 1665]) (by decide +kernel)

noncomputable def f44539 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (45607936 + i)

theorem c44539_0 : rowSum f44539 0 1024 = 98629886 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 44539) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover44539 (by decide)
  decide +kernel

theorem sum44539 : rowSum f44539 0 1024 = 98629886 :=
  c44539_0

theorem h44539 : P.leaf 36 44539 = 98629886 :=
  leaf_weighted (k := 26) (d := 10) (H := 44539) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 44539) (by decide) (by decide +kernel)) sum44539

theorem h16318 : P.leaf 36 16318 = 98629886 :=
  orient72 (v := 44539) (by decide) (by decide +kernel) h44539

theorem cover44543 : P.CoversSplit 26 10 44543 0xffffffff00000022fffffafa0000002200000000000000000022002200000000ffffaaaa00000022aaaaaaaa000000220000000000000000002200220000000000330033003300220033003200330022003300330000000000220022000000000033002200330022002200220022002200330022000000000022002200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f44543 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (45612032 + i)

theorem c44543_0 : rowSum f44543 0 947 = 101478938 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 44543) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover44543 (by decide)
  decide +kernel

theorem c44543_1 : rowSum f44543 947 77 = 206919188 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 44543) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover44543 (by decide)
  decide +kernel

theorem sum44543 : rowSum f44543 0 1024 = 308398126 :=
  rowSum_append (F := f44543) (lo := 0) (n := 947) (m := 77) (A := 101478938) (B := 206919188) c44543_0 (c44543_1)

theorem h44543 : P.leaf 36 44543 = 308398126 :=
  leaf_weighted (k := 26) (d := 10) (H := 44543) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 44543) (by decide) (by decide +kernel)) sum44543

theorem h16319 : P.leaf 36 16319 = 308398126 :=
  orient72 (v := 44543) (by decide) (by decide +kernel) h44543

theorem cover16320 : P.CoversSplit 26 10 16320 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16320 : P.leaf 36 16320 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16320) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16320) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16320 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16321 : P.CoversSplit 26 10 16321 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16321 : P.leaf 36 16321 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16321) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16321) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16321 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16322 : P.CoversSplit 26 10 16322 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16322 : P.leaf 36 16322 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16322) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16322) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16322 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16323 : P.CoversSplit 26 10 16323 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16323 : P.leaf 36 16323 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16323) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16323) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16323 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16326 : P.CoversSplit 26 10 16326 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16326 : P.leaf 36 16326 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16326) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16326) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16326 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16327 : P.CoversSplit 26 10 16327 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16327 : P.leaf 36 16327 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16327) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16327) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16327 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16329 : P.CoversSplit 26 10 16329 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16329 : P.leaf 36 16329 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16329) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16329) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16329 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16331 : P.CoversSplit 26 10 16331 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16331 : P.leaf 36 16331 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16331) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16331) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16331 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16335 : P.CoversSplit 26 10 16335 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h16335 : P.leaf 36 16335 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16335) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16335) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16335 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16336 : P.CoversSplit 26 10 16336 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16336 : P.leaf 36 16336 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16336) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16336) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16336 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16337 : P.CoversSplit 26 10 16337 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16337 : P.leaf 36 16337 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16337) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16337) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16337 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16338 : P.CoversSplit 26 10 16338 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16338 : P.leaf 36 16338 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16338) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16338) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16338 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16339 : P.CoversSplit 26 10 16339 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16339 : P.leaf 36 16339 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16339) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16339) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16339 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16340 : P.CoversSplit 26 10 16340 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16340 : P.leaf 36 16340 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16340) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16340) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16340 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16341 : P.CoversSplit 26 10 16341 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16341 : P.leaf 36 16341 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16341) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16341) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16341 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16342 : P.CoversSplit 26 10 16342 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16342 : P.leaf 36 16342 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16342) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16342) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16342 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16343 : P.CoversSplit 26 10 16343 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16343 : P.leaf 36 16343 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16343) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16343) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16344 : P.CoversSplit 26 10 16344 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16344 : P.leaf 36 16344 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16344) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16344) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16344 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16345 : P.CoversSplit 26 10 16345 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16345 : P.leaf 36 16345 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16345) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16345) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16345 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16346 : P.CoversSplit 26 10 16346 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16346 : P.leaf 36 16346 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16346) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16346) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16346 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16347 : P.CoversSplit 26 10 16347 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16347 : P.leaf 36 16347 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16347) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16348 : P.CoversSplit 26 10 16348 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16348 : P.leaf 36 16348 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16348) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16348) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16348 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16349 : P.CoversSplit 26 10 16349 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16349 : P.leaf 36 16349 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16349) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16349) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16349 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16350 : P.CoversSplit 26 10 16350 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16350 : P.leaf 36 16350 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16350) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16350) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16350 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover16351 : P.CoversSplit 26 10 16351 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h16351 : P.leaf 36 16351 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 16351) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 16351) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover16351 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover80364 : P.CoversSplit 26 10 80364 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80364 : P.leaf 36 80364 = 302584 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80364) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80364) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80364 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h16368 : P.leaf 36 16368 = 302584 :=
  orient348 (v := 80364) (by decide) (by decide +kernel) h80364

theorem cover40945 : P.CoversSplit 26 10 40945 0xf000fa00f0c0fac8000000000000000000000000000000000000000000008888f000fa00f0c0fac8000000000000000000000000000000000000000000008888f000fa00f0c0fac8000000000000000000000000000000000000000000008888f000fa00f0c0fac8000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 922, 930, 965, 1658, 1665]) (by decide +kernel)

noncomputable def f40945 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (41927680 + i)

theorem c40945_0 : rowSum f40945 0 1024 = 10229850 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 40945) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover40945 (by decide)
  decide +kernel

theorem sum40945 : rowSum f40945 0 1024 = 10229850 :=
  c40945_0

theorem h40945 : P.leaf 36 40945 = 10229850 :=
  leaf_weighted (k := 26) (d := 10) (H := 40945) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 40945) (by decide) (by decide +kernel)) sum40945

theorem h16369 : P.leaf 36 16369 = 10229850 :=
  orient6 (v := 40945) (by decide) (by decide +kernel) h40945

theorem cover108923 : P.CoversSplit 26 10 108923 0xaaaaaaaa00000000aaaaabab0000000000000000000000000000000000000022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 930, 1272, 1322, 1658, 1665]) (by decide +kernel)

theorem c108923_0 : P.sumLeaves 26 111537152 1024 = 11955014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 108923) (lo := 0) (len := 1024) (W := 11955014) check rows elimOK (by decide) (by decide) cover108923 (by decide)
  decide +kernel

theorem h108923 : P.leaf 36 108923 = 11955014 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11955014)]) (.cons c108923_0 (.nil)) (by decide) (by decide))

theorem h16370 : P.leaf 36 16370 = 11955014 :=
  orient84 (v := 108923) (by decide) (by decide +kernel) h108923

def seg : List (ℕ × ℕ) := [(16314, 720), (16315, 720), (16318, 360), (16319, 360), (16320, 180), (16321, 360), (16322, 360), (16323, 720), (16326, 180), (16327, 360), (16329, 180), (16331, 360), (16335, 180), (16336, 720), (16337, 720), (16338, 720), (16339, 720), (16340, 720), (16341, 720), (16342, 720), (16343, 720), (16344, 720), (16345, 720), (16346, 720), (16347, 720), (16348, 720), (16349, 720), (16350, 720), (16351, 720), (16368, 360), (16369, 360), (16370, 720)]

theorem segOK : checkSeg 20 perms 16314 16371 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16314 16371 18000 221527023840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 221527023840)
    (SegSum.cons (w := 720) h16314 (SegSum.cons (w := 720) h16315 (SegSum.cons (w := 360) h16318 (SegSum.cons (w := 360) h16319 (SegSum.cons (w := 180) h16320 (SegSum.cons (w := 360) h16321 (SegSum.cons (w := 360) h16322 (SegSum.cons (w := 720) h16323 (SegSum.cons (w := 180) h16326 (SegSum.cons (w := 360) h16327 (SegSum.cons (w := 180) h16329 (SegSum.cons (w := 360) h16331 (SegSum.cons (w := 180) h16335 (SegSum.cons (w := 720) h16336 (SegSum.cons (w := 720) h16337 (SegSum.cons (w := 720) h16338 (SegSum.cons (w := 720) h16339 (SegSum.cons (w := 720) h16340 (SegSum.cons (w := 720) h16341 (SegSum.cons (w := 720) h16342 (SegSum.cons (w := 720) h16343 (SegSum.cons (w := 720) h16344 (SegSum.cons (w := 720) h16345 (SegSum.cons (w := 720) h16346 (SegSum.cons (w := 720) h16347 (SegSum.cons (w := 720) h16348 (SegSum.cons (w := 720) h16349 (SegSum.cons (w := 720) h16350 (SegSum.cons (w := 720) h16351 (SegSum.cons (w := 360) h16368 (SegSum.cons (w := 360) h16369 (SegSum.cons (w := 720) h16370 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S33
