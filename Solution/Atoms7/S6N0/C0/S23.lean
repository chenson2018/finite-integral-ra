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

namespace RACert.S6N0.C0.S23

open RACert RACert.Problem

theorem cover13526 : P.CoversSplit 26 10 13526 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13526_0 : P.sumLeaves 26 13850624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13526) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13526 (by decide)
  decide +kernel

theorem h13526 : P.leaf 36 13526 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13526_0 (.nil)) (by decide) (by decide))

theorem cover13527 : P.CoversSplit 26 10 13527 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13527_0 : P.sumLeaves 26 13851648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13527) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13527 (by decide)
  decide +kernel

theorem h13527 : P.leaf 36 13527 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13527_0 (.nil)) (by decide) (by decide))

theorem cover13532 : P.CoversSplit 26 10 13532 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13532_0 : P.sumLeaves 26 13856768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13532) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13532 (by decide)
  decide +kernel

theorem h13532 : P.leaf 36 13532 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13532_0 (.nil)) (by decide) (by decide))

theorem cover13533 : P.CoversSplit 26 10 13533 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13533_0 : P.sumLeaves 26 13857792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13533) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13533 (by decide)
  decide +kernel

theorem h13533 : P.leaf 36 13533 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13533_0 (.nil)) (by decide) (by decide))

theorem cover13535 : P.CoversSplit 26 10 13535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13535_0 : P.sumLeaves 26 13859840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13535) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13535 (by decide)
  decide +kernel

theorem h13535 : P.leaf 36 13535 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13535_0 (.nil)) (by decide) (by decide))

theorem cover13542 : P.CoversSplit 26 10 13542 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13542_0 : P.sumLeaves 26 13867008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13542) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13542 (by decide)
  decide +kernel

theorem h13542 : P.leaf 36 13542 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13542_0 (.nil)) (by decide) (by decide))

theorem cover13543 : P.CoversSplit 26 10 13543 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13543_0 : P.sumLeaves 26 13868032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13543) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13543 (by decide)
  decide +kernel

theorem h13543 : P.leaf 36 13543 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13543_0 (.nil)) (by decide) (by decide))

theorem cover13544 : P.CoversSplit 26 10 13544 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13544_0 : P.sumLeaves 26 13869056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13544) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13544 (by decide)
  decide +kernel

theorem h13544 : P.leaf 36 13544 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13544_0 (.nil)) (by decide) (by decide))

theorem cover13545 : P.CoversSplit 26 10 13545 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13545_0 : P.sumLeaves 26 13870080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13545) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13545 (by decide)
  decide +kernel

theorem h13545 : P.leaf 36 13545 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13545_0 (.nil)) (by decide) (by decide))

theorem cover13546 : P.CoversSplit 26 10 13546 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13546_0 : P.sumLeaves 26 13871104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13546) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13546 (by decide)
  decide +kernel

theorem h13546 : P.leaf 36 13546 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13546_0 (.nil)) (by decide) (by decide))

theorem cover13547 : P.CoversSplit 26 10 13547 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13547_0 : P.sumLeaves 26 13872128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13547) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13547 (by decide)
  decide +kernel

theorem h13547 : P.leaf 36 13547 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13547_0 (.nil)) (by decide) (by decide))

theorem cover13550 : P.CoversSplit 26 10 13550 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13550_0 : P.sumLeaves 26 13875200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13550) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13550 (by decide)
  decide +kernel

theorem h13550 : P.leaf 36 13550 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13550_0 (.nil)) (by decide) (by decide))

theorem cover13551 : P.CoversSplit 26 10 13551 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13551_0 : P.sumLeaves 26 13876224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13551) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13551 (by decide)
  decide +kernel

theorem h13551 : P.leaf 36 13551 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13551_0 (.nil)) (by decide) (by decide))

theorem cover13558 : P.CoversSplit 26 10 13558 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13558_0 : P.sumLeaves 26 13883392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13558) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13558 (by decide)
  decide +kernel

theorem h13558 : P.leaf 36 13558 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13558_0 (.nil)) (by decide) (by decide))

theorem cover13559 : P.CoversSplit 26 10 13559 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13559_0 : P.sumLeaves 26 13884416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13559) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13559 (by decide)
  decide +kernel

theorem h13559 : P.leaf 36 13559 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13559_0 (.nil)) (by decide) (by decide))

theorem cover13560 : P.CoversSplit 26 10 13560 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13560_0 : P.sumLeaves 26 13885440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13560) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13560 (by decide)
  decide +kernel

theorem h13560 : P.leaf 36 13560 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13560_0 (.nil)) (by decide) (by decide))

theorem cover13561 : P.CoversSplit 26 10 13561 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13561_0 : P.sumLeaves 26 13886464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13561) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13561 (by decide)
  decide +kernel

theorem h13561 : P.leaf 36 13561 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13561_0 (.nil)) (by decide) (by decide))

theorem cover13562 : P.CoversSplit 26 10 13562 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13562_0 : P.sumLeaves 26 13887488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13562) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13562 (by decide)
  decide +kernel

theorem h13562 : P.leaf 36 13562 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13562_0 (.nil)) (by decide) (by decide))

theorem cover13563 : P.CoversSplit 26 10 13563 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13563_0 : P.sumLeaves 26 13888512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13563) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13563 (by decide)
  decide +kernel

theorem h13563 : P.leaf 36 13563 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13563_0 (.nil)) (by decide) (by decide))

theorem cover13564 : P.CoversSplit 26 10 13564 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13564_0 : P.sumLeaves 26 13889536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13564) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13564 (by decide)
  decide +kernel

theorem h13564 : P.leaf 36 13564 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13564_0 (.nil)) (by decide) (by decide))

theorem cover13565 : P.CoversSplit 26 10 13565 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13565_0 : P.sumLeaves 26 13890560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13565) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13565 (by decide)
  decide +kernel

theorem h13565 : P.leaf 36 13565 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13565_0 (.nil)) (by decide) (by decide))

theorem cover13566 : P.CoversSplit 26 10 13566 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13566_0 : P.sumLeaves 26 13891584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13566) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13566 (by decide)
  decide +kernel

theorem h13566 : P.leaf 36 13566 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13566_0 (.nil)) (by decide) (by decide))

theorem cover13567 : P.CoversSplit 26 10 13567 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13567_0 : P.sumLeaves 26 13892608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13567) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13567 (by decide)
  decide +kernel

theorem h13567 : P.leaf 36 13567 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13567_0 (.nil)) (by decide) (by decide))

theorem cover13619 : P.CoversSplit 26 10 13619 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13619_0 : P.sumLeaves 26 13945856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13619) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13619 (by decide)
  decide +kernel

theorem h13619 : P.leaf 36 13619 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13619_0 (.nil)) (by decide) (by decide))

theorem cover13620 : P.CoversSplit 26 10 13620 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13620_0 : P.sumLeaves 26 13946880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13620) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13620 (by decide)
  decide +kernel

theorem h13620 : P.leaf 36 13620 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13620_0 (.nil)) (by decide) (by decide))

theorem cover13621 : P.CoversSplit 26 10 13621 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13621_0 : P.sumLeaves 26 13947904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13621) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13621 (by decide)
  decide +kernel

theorem h13621 : P.leaf 36 13621 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13621_0 (.nil)) (by decide) (by decide))

theorem cover13623 : P.CoversSplit 26 10 13623 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13623_0 : P.sumLeaves 26 13949952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13623) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13623 (by decide)
  decide +kernel

theorem h13623 : P.leaf 36 13623 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13623_0 (.nil)) (by decide) (by decide))

theorem cover13628 : P.CoversSplit 26 10 13628 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13628_0 : P.sumLeaves 26 13955072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13628) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13628 (by decide)
  decide +kernel

theorem h13628 : P.leaf 36 13628 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13628_0 (.nil)) (by decide) (by decide))

theorem cover13629 : P.CoversSplit 26 10 13629 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13629_0 : P.sumLeaves 26 13956096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13629) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13629 (by decide)
  decide +kernel

theorem h13629 : P.leaf 36 13629 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13629_0 (.nil)) (by decide) (by decide))

theorem cover13631 : P.CoversSplit 26 10 13631 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13631_0 : P.sumLeaves 26 13958144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13631) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13631 (by decide)
  decide +kernel

theorem h13631 : P.leaf 36 13631 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13631_0 (.nil)) (by decide) (by decide))

theorem cover13666 : P.CoversSplit 26 10 13666 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13666_0 : P.sumLeaves 26 13993984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13666) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13666 (by decide)
  decide +kernel

theorem h13666 : P.leaf 36 13666 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13666_0 (.nil)) (by decide) (by decide))

theorem cover13667 : P.CoversSplit 26 10 13667 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13667_0 : P.sumLeaves 26 13995008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13667) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13667 (by decide)
  decide +kernel

theorem h13667 : P.leaf 36 13667 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13667_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13526, 360), (13527, 360), (13532, 180), (13533, 360), (13535, 180), (13542, 360), (13543, 360), (13544, 360), (13545, 360), (13546, 720), (13547, 720), (13550, 360), (13551, 360), (13558, 720), (13559, 720), (13560, 720), (13561, 720), (13562, 720), (13563, 720), (13564, 720), (13565, 720), (13566, 720), (13567, 720), (13619, 90), (13620, 360), (13621, 720), (13623, 360), (13628, 180), (13629, 360), (13631, 180), (13666, 360), (13667, 720)]

theorem segOK : checkSeg 20 perms 13526 13668 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13526 13668 15570 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h13526 (SegSum.cons (w := 360) h13527 (SegSum.cons (w := 180) h13532 (SegSum.cons (w := 360) h13533 (SegSum.cons (w := 180) h13535 (SegSum.cons (w := 360) h13542 (SegSum.cons (w := 360) h13543 (SegSum.cons (w := 360) h13544 (SegSum.cons (w := 360) h13545 (SegSum.cons (w := 720) h13546 (SegSum.cons (w := 720) h13547 (SegSum.cons (w := 360) h13550 (SegSum.cons (w := 360) h13551 (SegSum.cons (w := 720) h13558 (SegSum.cons (w := 720) h13559 (SegSum.cons (w := 720) h13560 (SegSum.cons (w := 720) h13561 (SegSum.cons (w := 720) h13562 (SegSum.cons (w := 720) h13563 (SegSum.cons (w := 720) h13564 (SegSum.cons (w := 720) h13565 (SegSum.cons (w := 720) h13566 (SegSum.cons (w := 720) h13567 (SegSum.cons (w := 90) h13619 (SegSum.cons (w := 360) h13620 (SegSum.cons (w := 720) h13621 (SegSum.cons (w := 360) h13623 (SegSum.cons (w := 180) h13628 (SegSum.cons (w := 360) h13629 (SegSum.cons (w := 180) h13631 (SegSum.cons (w := 360) h13666 (SegSum.cons (w := 720) h13667 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S23
