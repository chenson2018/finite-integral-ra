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

theorem c3370_0 : P.sumLeaves 26 3450880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3370) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3370 (by decide)
  decide +kernel

theorem h3370 : P.leaf 36 3370 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3370_0 (.nil)) (by decide) (by decide))

theorem cover3371 : P.CoversSplit 26 10 3371 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c3371_0 : P.sumLeaves 26 3451904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3371) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3371 (by decide)
  decide +kernel

theorem h3371 : P.leaf 36 3371 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3371_0 (.nil)) (by decide) (by decide))

theorem cover3372 : P.CoversSplit 26 10 3372 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3372_0 : P.sumLeaves 26 3452928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3372) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3372 (by decide)
  decide +kernel

theorem h3372 : P.leaf 36 3372 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3372_0 (.nil)) (by decide) (by decide))

theorem cover3373 : P.CoversSplit 26 10 3373 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3373_0 : P.sumLeaves 26 3453952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3373) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3373 (by decide)
  decide +kernel

theorem h3373 : P.leaf 36 3373 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3373_0 (.nil)) (by decide) (by decide))

theorem cover3374 : P.CoversSplit 26 10 3374 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3374_0 : P.sumLeaves 26 3454976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3374) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3374 (by decide)
  decide +kernel

theorem h3374 : P.leaf 36 3374 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3374_0 (.nil)) (by decide) (by decide))

theorem cover3375 : P.CoversSplit 26 10 3375 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3375_0 : P.sumLeaves 26 3456000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3375) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3375 (by decide)
  decide +kernel

theorem h3375 : P.leaf 36 3375 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3375_0 (.nil)) (by decide) (by decide))

theorem cover3382 : P.CoversSplit 26 10 3382 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3382_0 : P.sumLeaves 26 3463168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3382) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3382 (by decide)
  decide +kernel

theorem h3382 : P.leaf 36 3382 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3382_0 (.nil)) (by decide) (by decide))

theorem cover3383 : P.CoversSplit 26 10 3383 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3383_0 : P.sumLeaves 26 3464192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3383) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3383 (by decide)
  decide +kernel

theorem h3383 : P.leaf 36 3383 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3383_0 (.nil)) (by decide) (by decide))

theorem cover3384 : P.CoversSplit 26 10 3384 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c3384_0 : P.sumLeaves 26 3465216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3384) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3384 (by decide)
  decide +kernel

theorem h3384 : P.leaf 36 3384 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3384_0 (.nil)) (by decide) (by decide))

theorem cover3385 : P.CoversSplit 26 10 3385 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c3385_0 : P.sumLeaves 26 3466240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3385) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3385 (by decide)
  decide +kernel

theorem h3385 : P.leaf 36 3385 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3385_0 (.nil)) (by decide) (by decide))

theorem cover3386 : P.CoversSplit 26 10 3386 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c3386_0 : P.sumLeaves 26 3467264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3386) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3386 (by decide)
  decide +kernel

theorem h3386 : P.leaf 36 3386 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3386_0 (.nil)) (by decide) (by decide))

theorem cover3387 : P.CoversSplit 26 10 3387 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c3387_0 : P.sumLeaves 26 3468288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3387) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3387 (by decide)
  decide +kernel

theorem h3387 : P.leaf 36 3387 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3387_0 (.nil)) (by decide) (by decide))

theorem cover3388 : P.CoversSplit 26 10 3388 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3388_0 : P.sumLeaves 26 3469312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3388) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3388 (by decide)
  decide +kernel

theorem h3388 : P.leaf 36 3388 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3388_0 (.nil)) (by decide) (by decide))

theorem cover3389 : P.CoversSplit 26 10 3389 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3389_0 : P.sumLeaves 26 3470336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3389) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3389 (by decide)
  decide +kernel

theorem h3389 : P.leaf 36 3389 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3389_0 (.nil)) (by decide) (by decide))

theorem cover3390 : P.CoversSplit 26 10 3390 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3390_0 : P.sumLeaves 26 3471360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3390) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3390 (by decide)
  decide +kernel

theorem h3390 : P.leaf 36 3390 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3390_0 (.nil)) (by decide) (by decide))

theorem cover3391 : P.CoversSplit 26 10 3391 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3391_0 : P.sumLeaves 26 3472384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3391) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3391 (by decide)
  decide +kernel

theorem h3391 : P.leaf 36 3391 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3391_0 (.nil)) (by decide) (by decide))

theorem cover3400 : P.CoversSplit 26 10 3400 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000050000000000000000000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 930, 972, 979, 1322, 1665]) (by decide +kernel)

theorem c3400_0 : P.sumLeaves 26 3481600 1024 = 1555 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3400) (lo := 0) (len := 1024) (W := 1555) check rows elimOK (by decide) (by decide) cover3400 (by decide)
  decide +kernel

theorem h3400 : P.leaf 36 3400 = 1555 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1555)]) (.cons c3400_0 (.nil)) (by decide) (by decide))

theorem h3401 : P.leaf 36 3401 = 1024 := by
  exact leaf_contract_factors (k := 36) (b := 10) (H := 3401) (ss := [(37, 1, 482), (5, 1, 488), (20, 1, 580), (13, 1, 867), (12, 1, 825), (36, 1, 874), (6, 1, 433), (28, 1, 481), (30, 1, 481), (2, 1, 411), (3, 1, 418), (32, 1, 530), (9, 1, 572), (15, 1, 473), (19, 1, 522), (34, 1, 579), (4, 1, 425), (29, 1, 636), (18, 1, 879), (21, 1, 916), (31, 1, 979), (17, 1, 1217), (33, 1, 1322), (35, 1, 1665), (11, 1, 818), (16, 1, 1210)]) (ids := [5, 6, 8, 12, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 9, 10, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 10]) (W := 1024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover3402 : P.CoversSplit 26 10 3402 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem c3402_0 : P.sumLeaves 26 3483648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3402) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3402 (by decide)
  decide +kernel

theorem h3402 : P.leaf 36 3402 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3402_0 (.nil)) (by decide) (by decide))

theorem cover3403 : P.CoversSplit 26 10 3403 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem c3403_0 : P.sumLeaves 26 3484672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3403) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3403 (by decide)
  decide +kernel

theorem h3403 : P.leaf 36 3403 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3403_0 (.nil)) (by decide) (by decide))

theorem cover3404 : P.CoversSplit 26 10 3404 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3404_0 : P.sumLeaves 26 3485696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3404) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3404 (by decide)
  decide +kernel

theorem h3404 : P.leaf 36 3404 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3404_0 (.nil)) (by decide) (by decide))

theorem cover3405 : P.CoversSplit 26 10 3405 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3405_0 : P.sumLeaves 26 3486720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3405) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3405 (by decide)
  decide +kernel

theorem h3405 : P.leaf 36 3405 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3405_0 (.nil)) (by decide) (by decide))

theorem cover3406 : P.CoversSplit 26 10 3406 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3406_0 : P.sumLeaves 26 3487744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3406) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3406 (by decide)
  decide +kernel

theorem h3406 : P.leaf 36 3406 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3406_0 (.nil)) (by decide) (by decide))

theorem cover3407 : P.CoversSplit 26 10 3407 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3407_0 : P.sumLeaves 26 3488768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3407) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3407 (by decide)
  decide +kernel

theorem h3407 : P.leaf 36 3407 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3407_0 (.nil)) (by decide) (by decide))

theorem cover3418 : P.CoversSplit 26 10 3418 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000050000000000000000000005000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 922, 930, 979, 1322, 1665]) (by decide +kernel)

theorem c3418_0 : P.sumLeaves 26 3500032 1024 = 7345 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3418) (lo := 0) (len := 1024) (W := 7345) check rows elimOK (by decide) (by decide) cover3418 (by decide)
  decide +kernel

theorem h3418 : P.leaf 36 3418 = 7345 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7345)]) (.cons c3418_0 (.nil)) (by decide) (by decide))

theorem cover3419 : P.CoversSplit 26 10 3419 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000050000000000000000000005000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 922, 930, 979, 1322, 1665]) (by decide +kernel)

theorem c3419_0 : P.sumLeaves 26 3501056 1024 = 16290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3419) (lo := 0) (len := 1024) (W := 16290) check rows elimOK (by decide) (by decide) cover3419 (by decide)
  decide +kernel

theorem h3419 : P.leaf 36 3419 = 16290 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16290)]) (.cons c3419_0 (.nil)) (by decide) (by decide))

theorem cover3420 : P.CoversSplit 26 10 3420 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3420_0 : P.sumLeaves 26 3502080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3420) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3420 (by decide)
  decide +kernel

theorem h3420 : P.leaf 36 3420 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3420_0 (.nil)) (by decide) (by decide))

theorem cover3421 : P.CoversSplit 26 10 3421 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3421_0 : P.sumLeaves 26 3503104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3421) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3421 (by decide)
  decide +kernel

theorem h3421 : P.leaf 36 3421 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3421_0 (.nil)) (by decide) (by decide))

theorem cover3422 : P.CoversSplit 26 10 3422 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3422_0 : P.sumLeaves 26 3504128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3422) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3422 (by decide)
  decide +kernel

theorem h3422 : P.leaf 36 3422 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3422_0 (.nil)) (by decide) (by decide))

theorem cover3423 : P.CoversSplit 26 10 3423 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3423_0 : P.sumLeaves 26 3505152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3423) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3423 (by decide)
  decide +kernel

theorem h3423 : P.leaf 36 3423 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3423_0 (.nil)) (by decide) (by decide))

theorem cover3436 : P.CoversSplit 26 10 3436 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3436_0 : P.sumLeaves 26 3518464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3436) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3436 (by decide)
  decide +kernel

theorem h3436 : P.leaf 36 3436 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3436_0 (.nil)) (by decide) (by decide))

theorem cover3437 : P.CoversSplit 26 10 3437 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3437_0 : P.sumLeaves 26 3519488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3437) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3437 (by decide)
  decide +kernel

theorem h3437 : P.leaf 36 3437 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3437_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3370, 720), (3371, 720), (3372, 720), (3373, 720), (3374, 720), (3375, 720), (3382, 360), (3383, 360), (3384, 720), (3385, 720), (3386, 720), (3387, 720), (3388, 720), (3389, 720), (3390, 720), (3391, 720), (3400, 180), (3401, 360), (3402, 720), (3403, 720), (3404, 720), (3405, 720), (3406, 720), (3407, 720), (3418, 360), (3419, 360), (3420, 720), (3421, 720), (3422, 720), (3423, 720), (3436, 360), (3437, 360)]

theorem segOK : checkSeg 20 perms 3370 3438 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3370 3438 19980 9157140 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9157140)
    (SegSum.cons (w := 720) h3370 (SegSum.cons (w := 720) h3371 (SegSum.cons (w := 720) h3372 (SegSum.cons (w := 720) h3373 (SegSum.cons (w := 720) h3374 (SegSum.cons (w := 720) h3375 (SegSum.cons (w := 360) h3382 (SegSum.cons (w := 360) h3383 (SegSum.cons (w := 720) h3384 (SegSum.cons (w := 720) h3385 (SegSum.cons (w := 720) h3386 (SegSum.cons (w := 720) h3387 (SegSum.cons (w := 720) h3388 (SegSum.cons (w := 720) h3389 (SegSum.cons (w := 720) h3390 (SegSum.cons (w := 720) h3391 (SegSum.cons (w := 180) h3400 (SegSum.cons (w := 360) h3401 (SegSum.cons (w := 720) h3402 (SegSum.cons (w := 720) h3403 (SegSum.cons (w := 720) h3404 (SegSum.cons (w := 720) h3405 (SegSum.cons (w := 720) h3406 (SegSum.cons (w := 720) h3407 (SegSum.cons (w := 360) h3418 (SegSum.cons (w := 360) h3419 (SegSum.cons (w := 720) h3420 (SegSum.cons (w := 720) h3421 (SegSum.cons (w := 720) h3422 (SegSum.cons (w := 720) h3423 (SegSum.cons (w := 360) h3436 (SegSum.cons (w := 360) h3437 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S7
