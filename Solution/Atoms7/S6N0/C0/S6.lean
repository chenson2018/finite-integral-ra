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

theorem h3258 : P.leaf 36 3258 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3258) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3258) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3258 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3259 : P.CoversSplit 26 10 3259 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3259 : P.leaf 36 3259 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3259) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3259) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3259 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3262 : P.CoversSplit 26 10 3262 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3262 : P.leaf 36 3262 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3262) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3262) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3262 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3263 : P.CoversSplit 26 10 3263 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3263 : P.leaf 36 3263 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3263) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3263) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3263 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3272 : P.CoversSplit 26 10 3272 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3272 : P.leaf 36 3272 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3272) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3272) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3272 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3273 : P.CoversSplit 26 10 3273 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3273 : P.leaf 36 3273 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3273) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3273) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3273 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3274 : P.CoversSplit 26 10 3274 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3274 : P.leaf 36 3274 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3274) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3274) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3274 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3275 : P.CoversSplit 26 10 3275 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3275 : P.leaf 36 3275 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3275) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3275) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3275 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3278 : P.CoversSplit 26 10 3278 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3278 : P.leaf 36 3278 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3278) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3278) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3278 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3279 : P.CoversSplit 26 10 3279 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3279 : P.leaf 36 3279 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3279) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3279) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3279 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3290 : P.CoversSplit 26 10 3290 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3290 : P.leaf 36 3290 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3290) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3290) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3290 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3291 : P.CoversSplit 26 10 3291 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3291 : P.leaf 36 3291 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3291) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3291) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3291 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3292 : P.CoversSplit 26 10 3292 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3292 : P.leaf 36 3292 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3292) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3292) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3292 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3293 : P.CoversSplit 26 10 3293 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3293 : P.leaf 36 3293 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3293) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3293) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3293 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3294 : P.CoversSplit 26 10 3294 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3294 : P.leaf 36 3294 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3294) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3294) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3294 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3295 : P.CoversSplit 26 10 3295 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3295 : P.leaf 36 3295 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3295) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3295) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3295 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3326 : P.CoversSplit 26 10 3326 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3326 : P.leaf 36 3326 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3326) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3326) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3326 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3327 : P.CoversSplit 26 10 3327 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3327 : P.leaf 36 3327 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3327) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3327) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3327 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3347 : P.CoversSplit 26 10 3347 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 629, 636, 881, 922, 930, 979, 2008]) (ps := [(5, [558], [586]), (13, [510], [874])]) (by decide +kernel)

theorem h3347 : P.leaf 36 3347 = 64 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3347) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover3347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3348 : P.CoversSplit 26 10 3348 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3348 : P.leaf 36 3348 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3348) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3348) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3348 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3349 : P.CoversSplit 26 10 3349 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3349 : P.leaf 36 3349 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3349) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3349) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3349 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3350 : P.CoversSplit 26 10 3350 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3350 : P.leaf 36 3350 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3350) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3350) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3350 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3351 : P.CoversSplit 26 10 3351 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3351 : P.leaf 36 3351 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3351) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3351) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3351 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3356 : P.CoversSplit 26 10 3356 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3356 : P.leaf 36 3356 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3356) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3356) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3356 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3357 : P.CoversSplit 26 10 3357 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3357 : P.leaf 36 3357 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3357) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3357) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3357 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3359 : P.CoversSplit 26 10 3359 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3359 : P.leaf 36 3359 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3359) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3359) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3359 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3364 : P.CoversSplit 26 10 3364 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3364 : P.leaf 36 3364 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3364) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3364) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3364 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3365 : P.CoversSplit 26 10 3365 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3365 : P.leaf 36 3365 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3365) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3365) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3365 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3366 : P.CoversSplit 26 10 3366 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3366 : P.leaf 36 3366 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3366) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3366) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3366 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3367 : P.CoversSplit 26 10 3367 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3367 : P.leaf 36 3367 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3367) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3367) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3367 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3368 : P.CoversSplit 26 10 3368 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h3368 : P.leaf 36 3368 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3368) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3368) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3368 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3369 : P.CoversSplit 26 10 3369 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h3369 : P.leaf 36 3369 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3369) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3369) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3369 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3258, 720), (3259, 720), (3262, 360), (3263, 360), (3272, 180), (3273, 180), (3274, 720), (3275, 720), (3278, 360), (3279, 360), (3290, 360), (3291, 360), (3292, 360), (3293, 360), (3294, 720), (3295, 720), (3326, 180), (3327, 180), (3347, 90), (3348, 720), (3349, 720), (3350, 720), (3351, 720), (3356, 360), (3357, 720), (3359, 360), (3364, 360), (3365, 360), (3366, 720), (3367, 720), (3368, 720), (3369, 720)]

theorem segOK : checkSeg 20 perms 3258 3370 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3258 3370 15930 5760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5760)
    (SegSum.cons (w := 720) h3258 (SegSum.cons (w := 720) h3259 (SegSum.cons (w := 360) h3262 (SegSum.cons (w := 360) h3263 (SegSum.cons (w := 180) h3272 (SegSum.cons (w := 180) h3273 (SegSum.cons (w := 720) h3274 (SegSum.cons (w := 720) h3275 (SegSum.cons (w := 360) h3278 (SegSum.cons (w := 360) h3279 (SegSum.cons (w := 360) h3290 (SegSum.cons (w := 360) h3291 (SegSum.cons (w := 360) h3292 (SegSum.cons (w := 360) h3293 (SegSum.cons (w := 720) h3294 (SegSum.cons (w := 720) h3295 (SegSum.cons (w := 180) h3326 (SegSum.cons (w := 180) h3327 (SegSum.cons (w := 90) h3347 (SegSum.cons (w := 720) h3348 (SegSum.cons (w := 720) h3349 (SegSum.cons (w := 720) h3350 (SegSum.cons (w := 720) h3351 (SegSum.cons (w := 360) h3356 (SegSum.cons (w := 720) h3357 (SegSum.cons (w := 360) h3359 (SegSum.cons (w := 360) h3364 (SegSum.cons (w := 360) h3365 (SegSum.cons (w := 720) h3366 (SegSum.cons (w := 720) h3367 (SegSum.cons (w := 720) h3368 (SegSum.cons (w := 720) h3369 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S6
