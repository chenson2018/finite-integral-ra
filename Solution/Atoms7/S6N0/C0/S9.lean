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

namespace RACert.S6N0.C0.S9

open RACert RACert.Problem

theorem cover3513 : P.CoversSplit 26 10 3513 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3513_0 : P.sumLeaves 26 3597312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3513) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3513 (by decide)
  decide +kernel

theorem h3513 : P.leaf 36 3513 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3513_0 (.nil)) (by decide) (by decide))

theorem cover3514 : P.CoversSplit 26 10 3514 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3514_0 : P.sumLeaves 26 3598336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3514) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3514 (by decide)
  decide +kernel

theorem h3514 : P.leaf 36 3514 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3514_0 (.nil)) (by decide) (by decide))

theorem cover3515 : P.CoversSplit 26 10 3515 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3515_0 : P.sumLeaves 26 3599360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3515) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3515 (by decide)
  decide +kernel

theorem h3515 : P.leaf 36 3515 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3515_0 (.nil)) (by decide) (by decide))

theorem cover3516 : P.CoversSplit 26 10 3516 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3516_0 : P.sumLeaves 26 3600384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3516) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3516 (by decide)
  decide +kernel

theorem h3516 : P.leaf 36 3516 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3516_0 (.nil)) (by decide) (by decide))

theorem cover3517 : P.CoversSplit 26 10 3517 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3517_0 : P.sumLeaves 26 3601408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3517) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3517 (by decide)
  decide +kernel

theorem h3517 : P.leaf 36 3517 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3517_0 (.nil)) (by decide) (by decide))

theorem cover3518 : P.CoversSplit 26 10 3518 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3518_0 : P.sumLeaves 26 3602432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3518) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3518 (by decide)
  decide +kernel

theorem h3518 : P.leaf 36 3518 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3518_0 (.nil)) (by decide) (by decide))

theorem cover3519 : P.CoversSplit 26 10 3519 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3519_0 : P.sumLeaves 26 3603456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3519) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3519 (by decide)
  decide +kernel

theorem h3519 : P.leaf 36 3519 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3519_0 (.nil)) (by decide) (by decide))

theorem cover3528 : P.CoversSplit 26 10 3528 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3528_0 : P.sumLeaves 26 3612672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3528) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3528 (by decide)
  decide +kernel

theorem h3528 : P.leaf 36 3528 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3528_0 (.nil)) (by decide) (by decide))

theorem cover3529 : P.CoversSplit 26 10 3529 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3529_0 : P.sumLeaves 26 3613696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3529) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3529 (by decide)
  decide +kernel

theorem h3529 : P.leaf 36 3529 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3529_0 (.nil)) (by decide) (by decide))

theorem cover3530 : P.CoversSplit 26 10 3530 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3530_0 : P.sumLeaves 26 3614720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3530) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3530 (by decide)
  decide +kernel

theorem h3530 : P.leaf 36 3530 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3530_0 (.nil)) (by decide) (by decide))

theorem cover3531 : P.CoversSplit 26 10 3531 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3531_0 : P.sumLeaves 26 3615744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3531) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3531 (by decide)
  decide +kernel

theorem h3531 : P.leaf 36 3531 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3531_0 (.nil)) (by decide) (by decide))

theorem cover3532 : P.CoversSplit 26 10 3532 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3532_0 : P.sumLeaves 26 3616768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3532) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3532 (by decide)
  decide +kernel

theorem h3532 : P.leaf 36 3532 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3532_0 (.nil)) (by decide) (by decide))

theorem cover3533 : P.CoversSplit 26 10 3533 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3533_0 : P.sumLeaves 26 3617792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3533) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3533 (by decide)
  decide +kernel

theorem h3533 : P.leaf 36 3533 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3533_0 (.nil)) (by decide) (by decide))

theorem cover3534 : P.CoversSplit 26 10 3534 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3534_0 : P.sumLeaves 26 3618816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3534) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3534 (by decide)
  decide +kernel

theorem h3534 : P.leaf 36 3534 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3534_0 (.nil)) (by decide) (by decide))

theorem cover3535 : P.CoversSplit 26 10 3535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3535_0 : P.sumLeaves 26 3619840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3535) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3535 (by decide)
  decide +kernel

theorem h3535 : P.leaf 36 3535 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3535_0 (.nil)) (by decide) (by decide))

theorem cover3546 : P.CoversSplit 26 10 3546 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3546_0 : P.sumLeaves 26 3631104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3546) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3546 (by decide)
  decide +kernel

theorem h3546 : P.leaf 36 3546 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3546_0 (.nil)) (by decide) (by decide))

theorem cover3547 : P.CoversSplit 26 10 3547 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3547_0 : P.sumLeaves 26 3632128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3547) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3547 (by decide)
  decide +kernel

theorem h3547 : P.leaf 36 3547 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3547_0 (.nil)) (by decide) (by decide))

theorem cover3548 : P.CoversSplit 26 10 3548 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3548_0 : P.sumLeaves 26 3633152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3548) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3548 (by decide)
  decide +kernel

theorem h3548 : P.leaf 36 3548 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3548_0 (.nil)) (by decide) (by decide))

theorem cover3549 : P.CoversSplit 26 10 3549 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3549_0 : P.sumLeaves 26 3634176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3549) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3549 (by decide)
  decide +kernel

theorem h3549 : P.leaf 36 3549 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3549_0 (.nil)) (by decide) (by decide))

theorem cover3550 : P.CoversSplit 26 10 3550 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3550_0 : P.sumLeaves 26 3635200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3550) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3550 (by decide)
  decide +kernel

theorem h3550 : P.leaf 36 3550 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3550_0 (.nil)) (by decide) (by decide))

theorem cover3551 : P.CoversSplit 26 10 3551 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3551_0 : P.sumLeaves 26 3636224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3551) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3551 (by decide)
  decide +kernel

theorem h3551 : P.leaf 36 3551 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3551_0 (.nil)) (by decide) (by decide))

theorem cover3564 : P.CoversSplit 26 10 3564 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3564_0 : P.sumLeaves 26 3649536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3564) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3564 (by decide)
  decide +kernel

theorem h3564 : P.leaf 36 3564 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3564_0 (.nil)) (by decide) (by decide))

theorem cover3565 : P.CoversSplit 26 10 3565 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3565_0 : P.sumLeaves 26 3650560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3565) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3565 (by decide)
  decide +kernel

theorem h3565 : P.leaf 36 3565 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3565_0 (.nil)) (by decide) (by decide))

theorem cover3566 : P.CoversSplit 26 10 3566 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3566_0 : P.sumLeaves 26 3651584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3566) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3566 (by decide)
  decide +kernel

theorem h3566 : P.leaf 36 3566 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3566_0 (.nil)) (by decide) (by decide))

theorem cover3567 : P.CoversSplit 26 10 3567 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3567_0 : P.sumLeaves 26 3652608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3567) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3567 (by decide)
  decide +kernel

theorem h3567 : P.leaf 36 3567 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3567_0 (.nil)) (by decide) (by decide))

theorem cover3582 : P.CoversSplit 26 10 3582 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3582_0 : P.sumLeaves 26 3667968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3582) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3582 (by decide)
  decide +kernel

theorem h3582 : P.leaf 36 3582 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3582_0 (.nil)) (by decide) (by decide))

theorem cover3583 : P.CoversSplit 26 10 3583 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3583_0 : P.sumLeaves 26 3668992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3583) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3583 (by decide)
  decide +kernel

theorem h3583 : P.leaf 36 3583 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3583_0 (.nil)) (by decide) (by decide))

theorem cover3840 : P.CoversSplit 26 10 3840 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3840_0 : P.sumLeaves 26 3932160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3840) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3840 (by decide)
  decide +kernel

theorem h3840 : P.leaf 36 3840 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3840_0 (.nil)) (by decide) (by decide))

theorem cover3841 : P.CoversSplit 26 10 3841 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 608, 881, 922, 930, 979, 1658, 1665]) (by decide +kernel)

theorem c3841_0 : P.sumLeaves 26 3933184 1024 = 64 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3841) (lo := 0) (len := 1024) (W := 64) check rows elimOK (by decide) (by decide) cover3841 (by decide)
  decide +kernel

theorem h3841 : P.leaf 36 3841 = 64 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 64)]) (.cons c3841_0 (.nil)) (by decide) (by decide))

theorem cover3842 : P.CoversSplit 26 10 3842 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3842_0 : P.sumLeaves 26 3934208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3842) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3842 (by decide)
  decide +kernel

theorem h3842 : P.leaf 36 3842 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3842_0 (.nil)) (by decide) (by decide))

theorem cover3843 : P.CoversSplit 26 10 3843 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem c3843_0 : P.sumLeaves 26 3935232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3843) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3843 (by decide)
  decide +kernel

theorem h3843 : P.leaf 36 3843 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3843_0 (.nil)) (by decide) (by decide))

theorem cover3846 : P.CoversSplit 26 10 3846 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3846_0 : P.sumLeaves 26 3938304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3846) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3846 (by decide)
  decide +kernel

theorem h3846 : P.leaf 36 3846 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3846_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3513, 720), (3514, 720), (3515, 720), (3516, 720), (3517, 720), (3518, 720), (3519, 720), (3528, 360), (3529, 360), (3530, 720), (3531, 720), (3532, 720), (3533, 720), (3534, 720), (3535, 720), (3546, 360), (3547, 360), (3548, 720), (3549, 720), (3550, 720), (3551, 720), (3564, 360), (3565, 360), (3566, 720), (3567, 720), (3582, 360), (3583, 360), (3840, 45), (3841, 180), (3842, 360), (3843, 720), (3846, 180)]

theorem segOK : checkSeg 20 perms 3513 3847 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3513 3847 18045 11520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11520)
    (SegSum.cons (w := 720) h3513 (SegSum.cons (w := 720) h3514 (SegSum.cons (w := 720) h3515 (SegSum.cons (w := 720) h3516 (SegSum.cons (w := 720) h3517 (SegSum.cons (w := 720) h3518 (SegSum.cons (w := 720) h3519 (SegSum.cons (w := 360) h3528 (SegSum.cons (w := 360) h3529 (SegSum.cons (w := 720) h3530 (SegSum.cons (w := 720) h3531 (SegSum.cons (w := 720) h3532 (SegSum.cons (w := 720) h3533 (SegSum.cons (w := 720) h3534 (SegSum.cons (w := 720) h3535 (SegSum.cons (w := 360) h3546 (SegSum.cons (w := 360) h3547 (SegSum.cons (w := 720) h3548 (SegSum.cons (w := 720) h3549 (SegSum.cons (w := 720) h3550 (SegSum.cons (w := 720) h3551 (SegSum.cons (w := 360) h3564 (SegSum.cons (w := 360) h3565 (SegSum.cons (w := 720) h3566 (SegSum.cons (w := 720) h3567 (SegSum.cons (w := 360) h3582 (SegSum.cons (w := 360) h3583 (SegSum.cons (w := 45) h3840 (SegSum.cons (w := 180) h3841 (SegSum.cons (w := 360) h3842 (SegSum.cons (w := 720) h3843 (SegSum.cons (w := 180) h3846 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S9
