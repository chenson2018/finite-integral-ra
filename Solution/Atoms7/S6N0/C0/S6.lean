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

namespace RACert.S6N0.C0.S6

open RACert RACert.Problem

theorem cover3258 : P.CoversSplit 26 10 3258 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3258_0 : P.sumLeaves 26 3336192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3258) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3258 (by decide)
  decide +kernel

theorem h3258 : P.leaf 36 3258 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3258_0 (.nil)) (by decide) (by decide))

theorem cover3259 : P.CoversSplit 26 10 3259 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3259_0 : P.sumLeaves 26 3337216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3259) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3259 (by decide)
  decide +kernel

theorem h3259 : P.leaf 36 3259 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3259_0 (.nil)) (by decide) (by decide))

theorem cover3262 : P.CoversSplit 26 10 3262 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3262_0 : P.sumLeaves 26 3340288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3262) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3262 (by decide)
  decide +kernel

theorem h3262 : P.leaf 36 3262 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3262_0 (.nil)) (by decide) (by decide))

theorem cover3263 : P.CoversSplit 26 10 3263 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3263_0 : P.sumLeaves 26 3341312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3263) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3263 (by decide)
  decide +kernel

theorem h3263 : P.leaf 36 3263 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3263_0 (.nil)) (by decide) (by decide))

theorem cover3272 : P.CoversSplit 26 10 3272 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3272_0 : P.sumLeaves 26 3350528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3272) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3272 (by decide)
  decide +kernel

theorem h3272 : P.leaf 36 3272 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3272_0 (.nil)) (by decide) (by decide))

theorem cover3273 : P.CoversSplit 26 10 3273 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3273_0 : P.sumLeaves 26 3351552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3273) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3273 (by decide)
  decide +kernel

theorem h3273 : P.leaf 36 3273 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3273_0 (.nil)) (by decide) (by decide))

theorem cover3274 : P.CoversSplit 26 10 3274 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3274_0 : P.sumLeaves 26 3352576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3274) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3274 (by decide)
  decide +kernel

theorem h3274 : P.leaf 36 3274 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3274_0 (.nil)) (by decide) (by decide))

theorem cover3275 : P.CoversSplit 26 10 3275 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3275_0 : P.sumLeaves 26 3353600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3275) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3275 (by decide)
  decide +kernel

theorem h3275 : P.leaf 36 3275 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3275_0 (.nil)) (by decide) (by decide))

theorem cover3278 : P.CoversSplit 26 10 3278 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3278_0 : P.sumLeaves 26 3356672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3278) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3278 (by decide)
  decide +kernel

theorem h3278 : P.leaf 36 3278 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3278_0 (.nil)) (by decide) (by decide))

theorem cover3279 : P.CoversSplit 26 10 3279 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3279_0 : P.sumLeaves 26 3357696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3279) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3279 (by decide)
  decide +kernel

theorem h3279 : P.leaf 36 3279 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3279_0 (.nil)) (by decide) (by decide))

theorem cover3290 : P.CoversSplit 26 10 3290 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3290_0 : P.sumLeaves 26 3368960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3290) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3290 (by decide)
  decide +kernel

theorem h3290 : P.leaf 36 3290 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3290_0 (.nil)) (by decide) (by decide))

theorem cover3291 : P.CoversSplit 26 10 3291 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3291_0 : P.sumLeaves 26 3369984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3291) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3291 (by decide)
  decide +kernel

theorem h3291 : P.leaf 36 3291 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3291_0 (.nil)) (by decide) (by decide))

theorem cover3292 : P.CoversSplit 26 10 3292 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3292_0 : P.sumLeaves 26 3371008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3292) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3292 (by decide)
  decide +kernel

theorem h3292 : P.leaf 36 3292 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3292_0 (.nil)) (by decide) (by decide))

theorem cover3293 : P.CoversSplit 26 10 3293 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3293_0 : P.sumLeaves 26 3372032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3293) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3293 (by decide)
  decide +kernel

theorem h3293 : P.leaf 36 3293 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3293_0 (.nil)) (by decide) (by decide))

theorem cover3294 : P.CoversSplit 26 10 3294 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3294_0 : P.sumLeaves 26 3373056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3294) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3294 (by decide)
  decide +kernel

theorem h3294 : P.leaf 36 3294 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3294_0 (.nil)) (by decide) (by decide))

theorem cover3295 : P.CoversSplit 26 10 3295 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3295_0 : P.sumLeaves 26 3374080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3295) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3295 (by decide)
  decide +kernel

theorem h3295 : P.leaf 36 3295 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3295_0 (.nil)) (by decide) (by decide))

theorem cover3326 : P.CoversSplit 26 10 3326 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3326_0 : P.sumLeaves 26 3405824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3326) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3326 (by decide)
  decide +kernel

theorem h3326 : P.leaf 36 3326 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3326_0 (.nil)) (by decide) (by decide))

theorem cover3327 : P.CoversSplit 26 10 3327 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3327_0 : P.sumLeaves 26 3406848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3327) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3327 (by decide)
  decide +kernel

theorem h3327 : P.leaf 36 3327 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3327_0 (.nil)) (by decide) (by decide))

theorem h3347 : P.leaf 36 3347 = 64 := by
  exact leaf_contract_factors (k := 36) (b := 6) (H := 3347) (ss := [(18, 1, 468), (20, 5, 474), (5, 1, 480), (13, 1, 486), (37, 1, 580), (12, 1, 825), (36, 1, 874), (6, 1, 433), (28, 1, 579), (9, 1, 572), (34, 1, 579), (4, 1, 425), (30, 1, 481), (2, 1, 411), (3, 1, 418), (32, 1, 530), (29, 1, 636), (7, 1, 461), (31, 1, 489), (8, 1, 517), (33, 1, 538), (10, 1, 811), (11, 1, 818), (14, 1, 860), (15, 1, 915), (35, 1, 930), (16, 1, 1210), (17, 1, 1217), (19, 1, 1258), (21, 1, 1609)]) (ids := [20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 6]) (W := 64) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover3348 : P.CoversSplit 26 10 3348 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3348_0 : P.sumLeaves 26 3428352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3348) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3348 (by decide)
  decide +kernel

theorem h3348 : P.leaf 36 3348 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3348_0 (.nil)) (by decide) (by decide))

theorem cover3349 : P.CoversSplit 26 10 3349 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3349_0 : P.sumLeaves 26 3429376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3349) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3349 (by decide)
  decide +kernel

theorem h3349 : P.leaf 36 3349 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3349_0 (.nil)) (by decide) (by decide))

theorem cover3350 : P.CoversSplit 26 10 3350 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3350_0 : P.sumLeaves 26 3430400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3350) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3350 (by decide)
  decide +kernel

theorem h3350 : P.leaf 36 3350 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3350_0 (.nil)) (by decide) (by decide))

theorem cover3351 : P.CoversSplit 26 10 3351 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3351_0 : P.sumLeaves 26 3431424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3351) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3351 (by decide)
  decide +kernel

theorem h3351 : P.leaf 36 3351 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3351_0 (.nil)) (by decide) (by decide))

theorem cover3356 : P.CoversSplit 26 10 3356 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3356_0 : P.sumLeaves 26 3436544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3356) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3356 (by decide)
  decide +kernel

theorem h3356 : P.leaf 36 3356 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3356_0 (.nil)) (by decide) (by decide))

theorem cover3357 : P.CoversSplit 26 10 3357 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3357_0 : P.sumLeaves 26 3437568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3357) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3357 (by decide)
  decide +kernel

theorem h3357 : P.leaf 36 3357 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3357_0 (.nil)) (by decide) (by decide))

theorem cover3359 : P.CoversSplit 26 10 3359 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3359_0 : P.sumLeaves 26 3439616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3359) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3359 (by decide)
  decide +kernel

theorem h3359 : P.leaf 36 3359 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3359_0 (.nil)) (by decide) (by decide))

theorem cover3364 : P.CoversSplit 26 10 3364 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3364_0 : P.sumLeaves 26 3444736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3364) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3364 (by decide)
  decide +kernel

theorem h3364 : P.leaf 36 3364 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3364_0 (.nil)) (by decide) (by decide))

theorem cover3365 : P.CoversSplit 26 10 3365 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3365_0 : P.sumLeaves 26 3445760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3365) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3365 (by decide)
  decide +kernel

theorem h3365 : P.leaf 36 3365 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3365_0 (.nil)) (by decide) (by decide))

theorem cover3366 : P.CoversSplit 26 10 3366 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3366_0 : P.sumLeaves 26 3446784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3366) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3366 (by decide)
  decide +kernel

theorem h3366 : P.leaf 36 3366 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3366_0 (.nil)) (by decide) (by decide))

theorem cover3367 : P.CoversSplit 26 10 3367 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3367_0 : P.sumLeaves 26 3447808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3367) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3367 (by decide)
  decide +kernel

theorem h3367 : P.leaf 36 3367 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3367_0 (.nil)) (by decide) (by decide))

theorem cover3368 : P.CoversSplit 26 10 3368 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c3368_0 : P.sumLeaves 26 3448832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3368) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3368 (by decide)
  decide +kernel

theorem h3368 : P.leaf 36 3368 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3368_0 (.nil)) (by decide) (by decide))

theorem cover3369 : P.CoversSplit 26 10 3369 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c3369_0 : P.sumLeaves 26 3449856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3369) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3369 (by decide)
  decide +kernel

theorem h3369 : P.leaf 36 3369 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3369_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3258, 720), (3259, 720), (3262, 360), (3263, 360), (3272, 180), (3273, 180), (3274, 720), (3275, 720), (3278, 360), (3279, 360), (3290, 360), (3291, 360), (3292, 360), (3293, 360), (3294, 720), (3295, 720), (3326, 180), (3327, 180), (3347, 90), (3348, 720), (3349, 720), (3350, 720), (3351, 720), (3356, 360), (3357, 720), (3359, 360), (3364, 360), (3365, 360), (3366, 720), (3367, 720), (3368, 720), (3369, 720)]

theorem segOK : checkSeg 20 perms 3258 3370 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3258 3370 15930 5760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5760)
    (SegSum.cons (w := 720) h3258 (SegSum.cons (w := 720) h3259 (SegSum.cons (w := 360) h3262 (SegSum.cons (w := 360) h3263 (SegSum.cons (w := 180) h3272 (SegSum.cons (w := 180) h3273 (SegSum.cons (w := 720) h3274 (SegSum.cons (w := 720) h3275 (SegSum.cons (w := 360) h3278 (SegSum.cons (w := 360) h3279 (SegSum.cons (w := 360) h3290 (SegSum.cons (w := 360) h3291 (SegSum.cons (w := 360) h3292 (SegSum.cons (w := 360) h3293 (SegSum.cons (w := 720) h3294 (SegSum.cons (w := 720) h3295 (SegSum.cons (w := 180) h3326 (SegSum.cons (w := 180) h3327 (SegSum.cons (w := 90) h3347 (SegSum.cons (w := 720) h3348 (SegSum.cons (w := 720) h3349 (SegSum.cons (w := 720) h3350 (SegSum.cons (w := 720) h3351 (SegSum.cons (w := 360) h3356 (SegSum.cons (w := 720) h3357 (SegSum.cons (w := 360) h3359 (SegSum.cons (w := 360) h3364 (SegSum.cons (w := 360) h3365 (SegSum.cons (w := 720) h3366 (SegSum.cons (w := 720) h3367 (SegSum.cons (w := 720) h3368 (SegSum.cons (w := 720) h3369 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S6
