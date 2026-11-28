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

namespace RACert.S6N0.C0.S7

open RACert RACert.Problem

theorem cover3370 : P.CoversSplit 26 10 3370 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h3370 : P.leaf 36 3370 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3370) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3370) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3370 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3371 : P.CoversSplit 26 10 3371 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h3371 : P.leaf 36 3371 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3371) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3371) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3371 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3372 : P.CoversSplit 26 10 3372 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3372 : P.leaf 36 3372 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3372) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3372) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3372 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3373 : P.CoversSplit 26 10 3373 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3373 : P.leaf 36 3373 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3373) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3373) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3373 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3374 : P.CoversSplit 26 10 3374 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3374 : P.leaf 36 3374 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3374) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3374) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3374 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3375 : P.CoversSplit 26 10 3375 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3375 : P.leaf 36 3375 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3375) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3375) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3375 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3382 : P.CoversSplit 26 10 3382 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3382 : P.leaf 36 3382 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3382) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3382) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3382 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3383 : P.CoversSplit 26 10 3383 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3383 : P.leaf 36 3383 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3383) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3383) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3383 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3384 : P.CoversSplit 26 10 3384 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h3384 : P.leaf 36 3384 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3384) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3384) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3384 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3385 : P.CoversSplit 26 10 3385 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h3385 : P.leaf 36 3385 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3385) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3385) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3385 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3386 : P.CoversSplit 26 10 3386 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h3386 : P.leaf 36 3386 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3386) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3386) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3386 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3387 : P.CoversSplit 26 10 3387 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem h3387 : P.leaf 36 3387 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3387) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3387) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3387 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3388 : P.CoversSplit 26 10 3388 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3388 : P.leaf 36 3388 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3388) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3388) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3388 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3389 : P.CoversSplit 26 10 3389 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3389 : P.leaf 36 3389 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3389) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3389) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3389 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3390 : P.CoversSplit 26 10 3390 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3390 : P.leaf 36 3390 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3390) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3390) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3390 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3391 : P.CoversSplit 26 10 3391 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3391 : P.leaf 36 3391 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3391) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3391) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3391 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6290 : P.CoversSplit 26 10 6290 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 587, 629, 636, 825, 922, 930, 972, 1315]) (ps := [(6, [559], [580]), (7, [467], [468])]) (by decide +kernel)

theorem h6290 : P.leaf 36 6290 = 1555 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 6290) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6290) (weight := fun _ => 1) (xs := [256, 276, 1023]) check rows elimOK (by decide) (by decide) cover6290 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3400 : P.leaf 36 3400 = 1555 :=
  orient6 (v := 6290) (by decide) (by decide +kernel) h6290

theorem cover3401 : P.CoversSplit 26 10 3401 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 930, 972, 979, 1322, 1665]) (ps := [(13, [867], [874])]) (by decide +kernel)

theorem h3401 : P.leaf 36 3401 = 1024 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3401) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3401) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover3401 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3402 : P.CoversSplit 26 10 3402 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem h3402 : P.leaf 36 3402 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3402) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3402) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3402 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3403 : P.CoversSplit 26 10 3403 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem h3403 : P.leaf 36 3403 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3403) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3403) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3403 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3404 : P.CoversSplit 26 10 3404 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3404 : P.leaf 36 3404 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3404) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3404) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3404 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3405 : P.CoversSplit 26 10 3405 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3405 : P.leaf 36 3405 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3405) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3405) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3405 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3406 : P.CoversSplit 26 10 3406 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3406 : P.leaf 36 3406 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3406) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3406) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3406 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3407 : P.CoversSplit 26 10 3407 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3407 : P.leaf 36 3407 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3407) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3407) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3407 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6326 : P.CoversSplit 26 10 6326 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000300000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [488, 489, 538, 587, 629, 636, 866, 930, 972, 1315]) (by decide +kernel)

theorem h6326 : P.leaf 36 6326 = 7345 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 6326) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6326) (weight := fun _ => 1) (xs := [320, 321, 340, 341, 1023]) check rows elimOK (by decide) (by decide) cover6326 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3418 : P.leaf 36 3418 = 7345 :=
  orient6 (v := 6326) (by decide) (by decide +kernel) h6326

theorem cover6327 : P.CoversSplit 26 10 6327 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000300000000002000020000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [488, 489, 538, 587, 629, 636, 922, 930, 972, 1265, 1315, 1658]) (ps := [(11, [922], [879])]) (by decide +kernel)

theorem h6327 : P.leaf 36 6327 = 16290 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 6327) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6327) (weight := fun _ => 1) (xs := [257, 277, 320, 321, 340, 341, 1023]) check rows elimOK (by decide) (by decide) cover6327 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3419 : P.leaf 36 3419 = 16290 :=
  orient6 (v := 6327) (by decide) (by decide +kernel) h6327

theorem cover3420 : P.CoversSplit 26 10 3420 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3420 : P.leaf 36 3420 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3420) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3420) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3420 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3421 : P.CoversSplit 26 10 3421 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3421 : P.leaf 36 3421 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3421) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3421) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3421 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3422 : P.CoversSplit 26 10 3422 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3422 : P.leaf 36 3422 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3422) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3422) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3422 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3423 : P.CoversSplit 26 10 3423 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3423 : P.leaf 36 3423 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3423) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3423) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3423 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3436 : P.CoversSplit 26 10 3436 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3436 : P.leaf 36 3436 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3436) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3436) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3436 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3437 : P.CoversSplit 26 10 3437 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3437 : P.leaf 36 3437 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3437) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3437) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3437 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3370, 720), (3371, 720), (3372, 720), (3373, 720), (3374, 720), (3375, 720), (3382, 360), (3383, 360), (3384, 720), (3385, 720), (3386, 720), (3387, 720), (3388, 720), (3389, 720), (3390, 720), (3391, 720), (3400, 180), (3401, 360), (3402, 720), (3403, 720), (3404, 720), (3405, 720), (3406, 720), (3407, 720), (3418, 360), (3419, 360), (3420, 720), (3421, 720), (3422, 720), (3423, 720), (3436, 360), (3437, 360)]

theorem segOK : checkSeg 20 perms 3370 3438 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3370 3438 19980 9157140 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9157140)
    (SegSum.cons (w := 720) h3370 (SegSum.cons (w := 720) h3371 (SegSum.cons (w := 720) h3372 (SegSum.cons (w := 720) h3373 (SegSum.cons (w := 720) h3374 (SegSum.cons (w := 720) h3375 (SegSum.cons (w := 360) h3382 (SegSum.cons (w := 360) h3383 (SegSum.cons (w := 720) h3384 (SegSum.cons (w := 720) h3385 (SegSum.cons (w := 720) h3386 (SegSum.cons (w := 720) h3387 (SegSum.cons (w := 720) h3388 (SegSum.cons (w := 720) h3389 (SegSum.cons (w := 720) h3390 (SegSum.cons (w := 720) h3391 (SegSum.cons (w := 180) h3400 (SegSum.cons (w := 360) h3401 (SegSum.cons (w := 720) h3402 (SegSum.cons (w := 720) h3403 (SegSum.cons (w := 720) h3404 (SegSum.cons (w := 720) h3405 (SegSum.cons (w := 720) h3406 (SegSum.cons (w := 720) h3407 (SegSum.cons (w := 360) h3418 (SegSum.cons (w := 360) h3419 (SegSum.cons (w := 720) h3420 (SegSum.cons (w := 720) h3421 (SegSum.cons (w := 720) h3422 (SegSum.cons (w := 720) h3423 (SegSum.cons (w := 360) h3436 (SegSum.cons (w := 360) h3437 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S7
