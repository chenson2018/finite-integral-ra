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

namespace RACert.S6N0.C0.S8

open RACert RACert.Problem

theorem cover3438 : P.CoversSplit 26 10 3438 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3438 : P.leaf 36 3438 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3438) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3438) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3438 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3439 : P.CoversSplit 26 10 3439 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3439 : P.leaf 36 3439 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3439) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3439) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3439 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3454 : P.CoversSplit 26 10 3454 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3454 : P.leaf 36 3454 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3454) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3454) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3454 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3455 : P.CoversSplit 26 10 3455 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3455 : P.leaf 36 3455 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3455) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3455) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3455 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3475 : P.CoversSplit 26 10 3475 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 481, 489, 530, 538, 629, 636, 881, 922, 930]) (ps := [(13, [510], [874])]) (by decide +kernel)

theorem h3475 : P.leaf 36 3475 = 8393 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3475) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3475) (weight := fun _ => 1) (xs := [256, 341, 1023]) check rows elimOK (by decide) (by decide) cover3475 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3476 : P.CoversSplit 26 10 3476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3476 : P.leaf 36 3476 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3476) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3476) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3476 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3477 : P.CoversSplit 26 10 3477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3477 : P.leaf 36 3477 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3477) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3477) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3477 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3478 : P.CoversSplit 26 10 3478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3478 : P.leaf 36 3478 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3478) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3478) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3478 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3479 : P.CoversSplit 26 10 3479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3479 : P.leaf 36 3479 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3479) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3479) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3479 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3480 : P.CoversSplit 26 10 3480 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3480 : P.leaf 36 3480 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3480) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3480) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3480 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3481 : P.CoversSplit 26 10 3481 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3481 : P.leaf 36 3481 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3481) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3481) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3481 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3482 : P.CoversSplit 26 10 3482 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3482 : P.leaf 36 3482 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3482) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3482) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3482 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3483 : P.CoversSplit 26 10 3483 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3483 : P.leaf 36 3483 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3483) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3483) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3483 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3484 : P.CoversSplit 26 10 3484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3484 : P.leaf 36 3484 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3484) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3484) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3484 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3485 : P.CoversSplit 26 10 3485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3485 : P.leaf 36 3485 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3485) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3485) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3485 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3486 : P.CoversSplit 26 10 3486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3486 : P.leaf 36 3486 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3486) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3486) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3486 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3487 : P.CoversSplit 26 10 3487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3487 : P.leaf 36 3487 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3487) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3487) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3487 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3492 : P.CoversSplit 26 10 3492 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3492 : P.leaf 36 3492 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3492) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3492) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3492 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3493 : P.CoversSplit 26 10 3493 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3493 : P.leaf 36 3493 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3493) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3493) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3493 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3494 : P.CoversSplit 26 10 3494 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3494 : P.leaf 36 3494 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3494) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3494) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3494 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3495 : P.CoversSplit 26 10 3495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3495 : P.leaf 36 3495 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3495) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3495) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3495 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3496 : P.CoversSplit 26 10 3496 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3496 : P.leaf 36 3496 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3496) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3496) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3496 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3497 : P.CoversSplit 26 10 3497 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3497 : P.leaf 36 3497 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3497) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3497) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3497 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3498 : P.CoversSplit 26 10 3498 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3498 : P.leaf 36 3498 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3498) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3498) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3498 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3499 : P.CoversSplit 26 10 3499 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3499 : P.leaf 36 3499 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3499) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3499) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3499 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3500 : P.CoversSplit 26 10 3500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3500 : P.leaf 36 3500 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3500) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3500) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3500 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3501 : P.CoversSplit 26 10 3501 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3501 : P.leaf 36 3501 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3501) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3501) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3501 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3502 : P.CoversSplit 26 10 3502 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3502 : P.leaf 36 3502 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3502) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3502) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3502 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3503 : P.CoversSplit 26 10 3503 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3503 : P.leaf 36 3503 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3503) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3503) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3503 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3510 : P.CoversSplit 26 10 3510 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3510 : P.leaf 36 3510 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3510) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3510) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3510 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3511 : P.CoversSplit 26 10 3511 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3511 : P.leaf 36 3511 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3511) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3511) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3511 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3512 : P.CoversSplit 26 10 3512 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3512 : P.leaf 36 3512 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3512) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3512) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3512 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3438, 720), (3439, 720), (3454, 360), (3455, 360), (3475, 180), (3476, 360), (3477, 720), (3478, 360), (3479, 720), (3480, 720), (3481, 720), (3482, 720), (3483, 720), (3484, 720), (3485, 720), (3486, 720), (3487, 720), (3492, 360), (3493, 360), (3494, 720), (3495, 720), (3496, 720), (3497, 720), (3498, 720), (3499, 720), (3500, 720), (3501, 720), (3502, 720), (3503, 720), (3510, 360), (3511, 360), (3512, 720)]

theorem segOK : checkSeg 20 perms 3438 3513 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3438 3513 19620 1510740 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1510740)
    (SegSum.cons (w := 720) h3438 (SegSum.cons (w := 720) h3439 (SegSum.cons (w := 360) h3454 (SegSum.cons (w := 360) h3455 (SegSum.cons (w := 180) h3475 (SegSum.cons (w := 360) h3476 (SegSum.cons (w := 720) h3477 (SegSum.cons (w := 360) h3478 (SegSum.cons (w := 720) h3479 (SegSum.cons (w := 720) h3480 (SegSum.cons (w := 720) h3481 (SegSum.cons (w := 720) h3482 (SegSum.cons (w := 720) h3483 (SegSum.cons (w := 720) h3484 (SegSum.cons (w := 720) h3485 (SegSum.cons (w := 720) h3486 (SegSum.cons (w := 720) h3487 (SegSum.cons (w := 360) h3492 (SegSum.cons (w := 360) h3493 (SegSum.cons (w := 720) h3494 (SegSum.cons (w := 720) h3495 (SegSum.cons (w := 720) h3496 (SegSum.cons (w := 720) h3497 (SegSum.cons (w := 720) h3498 (SegSum.cons (w := 720) h3499 (SegSum.cons (w := 720) h3500 (SegSum.cons (w := 720) h3501 (SegSum.cons (w := 720) h3502 (SegSum.cons (w := 720) h3503 (SegSum.cons (w := 360) h3510 (SegSum.cons (w := 360) h3511 (SegSum.cons (w := 720) h3512 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S8
