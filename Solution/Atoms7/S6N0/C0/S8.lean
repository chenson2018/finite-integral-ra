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

namespace RACert.S6N0.C0.S8

open RACert RACert.Problem

theorem cover3438 : P.CoversSplit 26 10 3438 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3438_0 : P.sumLeaves 26 3520512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3438) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3438 (by decide)
  decide +kernel

theorem h3438 : P.leaf 36 3438 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3438_0 (.nil)) (by decide) (by decide))

theorem cover3439 : P.CoversSplit 26 10 3439 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3439_0 : P.sumLeaves 26 3521536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3439) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3439 (by decide)
  decide +kernel

theorem h3439 : P.leaf 36 3439 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3439_0 (.nil)) (by decide) (by decide))

theorem cover3454 : P.CoversSplit 26 10 3454 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3454_0 : P.sumLeaves 26 3536896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3454) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3454 (by decide)
  decide +kernel

theorem h3454 : P.leaf 36 3454 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3454_0 (.nil)) (by decide) (by decide))

theorem cover3455 : P.CoversSplit 26 10 3455 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3455_0 : P.sumLeaves 26 3537920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3455) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3455 (by decide)
  decide +kernel

theorem h3455 : P.leaf 36 3455 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3455_0 (.nil)) (by decide) (by decide))

theorem cover3475 : P.CoversSplit 26 10 3475 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 489, 530, 538, 629, 636, 881, 922, 930]) (by decide +kernel)

theorem c3475_0 : P.sumLeaves 26 3558400 1024 = 8393 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3475) (lo := 0) (len := 1024) (W := 8393) check rows elimOK (by decide) (by decide) cover3475 (by decide)
  decide +kernel

theorem h3475 : P.leaf 36 3475 = 8393 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8393)]) (.cons c3475_0 (.nil)) (by decide) (by decide))

theorem cover3476 : P.CoversSplit 26 10 3476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3476_0 : P.sumLeaves 26 3559424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3476) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3476 (by decide)
  decide +kernel

theorem h3476 : P.leaf 36 3476 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3476_0 (.nil)) (by decide) (by decide))

theorem cover3477 : P.CoversSplit 26 10 3477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3477_0 : P.sumLeaves 26 3560448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3477) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3477 (by decide)
  decide +kernel

theorem h3477 : P.leaf 36 3477 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3477_0 (.nil)) (by decide) (by decide))

theorem cover3478 : P.CoversSplit 26 10 3478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3478_0 : P.sumLeaves 26 3561472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3478) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3478 (by decide)
  decide +kernel

theorem h3478 : P.leaf 36 3478 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3478_0 (.nil)) (by decide) (by decide))

theorem cover3479 : P.CoversSplit 26 10 3479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3479_0 : P.sumLeaves 26 3562496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3479) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3479 (by decide)
  decide +kernel

theorem h3479 : P.leaf 36 3479 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3479_0 (.nil)) (by decide) (by decide))

theorem cover3480 : P.CoversSplit 26 10 3480 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3480_0 : P.sumLeaves 26 3563520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3480) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3480 (by decide)
  decide +kernel

theorem h3480 : P.leaf 36 3480 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3480_0 (.nil)) (by decide) (by decide))

theorem cover3481 : P.CoversSplit 26 10 3481 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3481_0 : P.sumLeaves 26 3564544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3481) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3481 (by decide)
  decide +kernel

theorem h3481 : P.leaf 36 3481 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3481_0 (.nil)) (by decide) (by decide))

theorem cover3482 : P.CoversSplit 26 10 3482 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3482_0 : P.sumLeaves 26 3565568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3482) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3482 (by decide)
  decide +kernel

theorem h3482 : P.leaf 36 3482 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3482_0 (.nil)) (by decide) (by decide))

theorem cover3483 : P.CoversSplit 26 10 3483 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3483_0 : P.sumLeaves 26 3566592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3483) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3483 (by decide)
  decide +kernel

theorem h3483 : P.leaf 36 3483 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3483_0 (.nil)) (by decide) (by decide))

theorem cover3484 : P.CoversSplit 26 10 3484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3484_0 : P.sumLeaves 26 3567616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3484) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3484 (by decide)
  decide +kernel

theorem h3484 : P.leaf 36 3484 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3484_0 (.nil)) (by decide) (by decide))

theorem cover3485 : P.CoversSplit 26 10 3485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3485_0 : P.sumLeaves 26 3568640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3485) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3485 (by decide)
  decide +kernel

theorem h3485 : P.leaf 36 3485 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3485_0 (.nil)) (by decide) (by decide))

theorem cover3486 : P.CoversSplit 26 10 3486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3486_0 : P.sumLeaves 26 3569664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3486) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3486 (by decide)
  decide +kernel

theorem h3486 : P.leaf 36 3486 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3486_0 (.nil)) (by decide) (by decide))

theorem cover3487 : P.CoversSplit 26 10 3487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3487_0 : P.sumLeaves 26 3570688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3487) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3487 (by decide)
  decide +kernel

theorem h3487 : P.leaf 36 3487 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3487_0 (.nil)) (by decide) (by decide))

theorem cover3492 : P.CoversSplit 26 10 3492 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3492_0 : P.sumLeaves 26 3575808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3492) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3492 (by decide)
  decide +kernel

theorem h3492 : P.leaf 36 3492 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3492_0 (.nil)) (by decide) (by decide))

theorem cover3493 : P.CoversSplit 26 10 3493 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3493_0 : P.sumLeaves 26 3576832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3493) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3493 (by decide)
  decide +kernel

theorem h3493 : P.leaf 36 3493 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3493_0 (.nil)) (by decide) (by decide))

theorem cover3494 : P.CoversSplit 26 10 3494 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3494_0 : P.sumLeaves 26 3577856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3494) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3494 (by decide)
  decide +kernel

theorem h3494 : P.leaf 36 3494 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3494_0 (.nil)) (by decide) (by decide))

theorem cover3495 : P.CoversSplit 26 10 3495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3495_0 : P.sumLeaves 26 3578880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3495) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3495 (by decide)
  decide +kernel

theorem h3495 : P.leaf 36 3495 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3495_0 (.nil)) (by decide) (by decide))

theorem cover3496 : P.CoversSplit 26 10 3496 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3496_0 : P.sumLeaves 26 3579904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3496) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3496 (by decide)
  decide +kernel

theorem h3496 : P.leaf 36 3496 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3496_0 (.nil)) (by decide) (by decide))

theorem cover3497 : P.CoversSplit 26 10 3497 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3497_0 : P.sumLeaves 26 3580928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3497) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3497 (by decide)
  decide +kernel

theorem h3497 : P.leaf 36 3497 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3497_0 (.nil)) (by decide) (by decide))

theorem cover3498 : P.CoversSplit 26 10 3498 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3498_0 : P.sumLeaves 26 3581952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3498) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3498 (by decide)
  decide +kernel

theorem h3498 : P.leaf 36 3498 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3498_0 (.nil)) (by decide) (by decide))

theorem cover3499 : P.CoversSplit 26 10 3499 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3499_0 : P.sumLeaves 26 3582976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3499) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3499 (by decide)
  decide +kernel

theorem h3499 : P.leaf 36 3499 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3499_0 (.nil)) (by decide) (by decide))

theorem cover3500 : P.CoversSplit 26 10 3500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3500_0 : P.sumLeaves 26 3584000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3500) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3500 (by decide)
  decide +kernel

theorem h3500 : P.leaf 36 3500 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3500_0 (.nil)) (by decide) (by decide))

theorem cover3501 : P.CoversSplit 26 10 3501 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3501_0 : P.sumLeaves 26 3585024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3501) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3501 (by decide)
  decide +kernel

theorem h3501 : P.leaf 36 3501 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3501_0 (.nil)) (by decide) (by decide))

theorem cover3502 : P.CoversSplit 26 10 3502 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3502_0 : P.sumLeaves 26 3586048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3502) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3502 (by decide)
  decide +kernel

theorem h3502 : P.leaf 36 3502 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3502_0 (.nil)) (by decide) (by decide))

theorem cover3503 : P.CoversSplit 26 10 3503 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3503_0 : P.sumLeaves 26 3587072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3503) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3503 (by decide)
  decide +kernel

theorem h3503 : P.leaf 36 3503 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3503_0 (.nil)) (by decide) (by decide))

theorem cover3510 : P.CoversSplit 26 10 3510 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3510_0 : P.sumLeaves 26 3594240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3510) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3510 (by decide)
  decide +kernel

theorem h3510 : P.leaf 36 3510 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3510_0 (.nil)) (by decide) (by decide))

theorem cover3511 : P.CoversSplit 26 10 3511 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3511_0 : P.sumLeaves 26 3595264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3511) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3511 (by decide)
  decide +kernel

theorem h3511 : P.leaf 36 3511 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3511_0 (.nil)) (by decide) (by decide))

theorem cover3512 : P.CoversSplit 26 10 3512 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3512_0 : P.sumLeaves 26 3596288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3512) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3512 (by decide)
  decide +kernel

theorem h3512 : P.leaf 36 3512 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3512_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3438, 720), (3439, 720), (3454, 360), (3455, 360), (3475, 180), (3476, 360), (3477, 720), (3478, 360), (3479, 720), (3480, 720), (3481, 720), (3482, 720), (3483, 720), (3484, 720), (3485, 720), (3486, 720), (3487, 720), (3492, 360), (3493, 360), (3494, 720), (3495, 720), (3496, 720), (3497, 720), (3498, 720), (3499, 720), (3500, 720), (3501, 720), (3502, 720), (3503, 720), (3510, 360), (3511, 360), (3512, 720)]

theorem segOK : checkSeg 20 perms 3438 3513 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3438 3513 19620 1510740 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1510740)
    (SegSum.cons (w := 720) h3438 (SegSum.cons (w := 720) h3439 (SegSum.cons (w := 360) h3454 (SegSum.cons (w := 360) h3455 (SegSum.cons (w := 180) h3475 (SegSum.cons (w := 360) h3476 (SegSum.cons (w := 720) h3477 (SegSum.cons (w := 360) h3478 (SegSum.cons (w := 720) h3479 (SegSum.cons (w := 720) h3480 (SegSum.cons (w := 720) h3481 (SegSum.cons (w := 720) h3482 (SegSum.cons (w := 720) h3483 (SegSum.cons (w := 720) h3484 (SegSum.cons (w := 720) h3485 (SegSum.cons (w := 720) h3486 (SegSum.cons (w := 720) h3487 (SegSum.cons (w := 360) h3492 (SegSum.cons (w := 360) h3493 (SegSum.cons (w := 720) h3494 (SegSum.cons (w := 720) h3495 (SegSum.cons (w := 720) h3496 (SegSum.cons (w := 720) h3497 (SegSum.cons (w := 720) h3498 (SegSum.cons (w := 720) h3499 (SegSum.cons (w := 720) h3500 (SegSum.cons (w := 720) h3501 (SegSum.cons (w := 720) h3502 (SegSum.cons (w := 720) h3503 (SegSum.cons (w := 360) h3510 (SegSum.cons (w := 360) h3511 (SegSum.cons (w := 720) h3512 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S8
