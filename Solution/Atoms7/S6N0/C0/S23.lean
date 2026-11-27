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

namespace RACert.S6N0.C0.S23

open RACert RACert.Problem

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

theorem cover13668 : P.CoversSplit 26 10 13668 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13668_0 : P.sumLeaves 26 13996032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13668) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13668 (by decide)
  decide +kernel

theorem h13668 : P.leaf 36 13668 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13668_0 (.nil)) (by decide) (by decide))

theorem cover13669 : P.CoversSplit 26 10 13669 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13669_0 : P.sumLeaves 26 13997056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13669) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13669 (by decide)
  decide +kernel

theorem h13669 : P.leaf 36 13669 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13669_0 (.nil)) (by decide) (by decide))

theorem cover13670 : P.CoversSplit 26 10 13670 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13670_0 : P.sumLeaves 26 13998080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13670) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13670 (by decide)
  decide +kernel

theorem h13670 : P.leaf 36 13670 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13670_0 (.nil)) (by decide) (by decide))

theorem cover13671 : P.CoversSplit 26 10 13671 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13671_0 : P.sumLeaves 26 13999104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13671) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13671 (by decide)
  decide +kernel

theorem h13671 : P.leaf 36 13671 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13671_0 (.nil)) (by decide) (by decide))

theorem cover13672 : P.CoversSplit 26 10 13672 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13672_0 : P.sumLeaves 26 14000128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13672) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13672 (by decide)
  decide +kernel

theorem h13672 : P.leaf 36 13672 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13672_0 (.nil)) (by decide) (by decide))

theorem cover13673 : P.CoversSplit 26 10 13673 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13673_0 : P.sumLeaves 26 14001152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13673) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13673 (by decide)
  decide +kernel

theorem h13673 : P.leaf 36 13673 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13673_0 (.nil)) (by decide) (by decide))

theorem cover13674 : P.CoversSplit 26 10 13674 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13674_0 : P.sumLeaves 26 14002176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13674) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13674 (by decide)
  decide +kernel

theorem h13674 : P.leaf 36 13674 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13674_0 (.nil)) (by decide) (by decide))

theorem cover13675 : P.CoversSplit 26 10 13675 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13675_0 : P.sumLeaves 26 14003200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13675) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13675 (by decide)
  decide +kernel

theorem h13675 : P.leaf 36 13675 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13675_0 (.nil)) (by decide) (by decide))

theorem cover13676 : P.CoversSplit 26 10 13676 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13676_0 : P.sumLeaves 26 14004224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13676) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13676 (by decide)
  decide +kernel

theorem h13676 : P.leaf 36 13676 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13676_0 (.nil)) (by decide) (by decide))

theorem cover13677 : P.CoversSplit 26 10 13677 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13677_0 : P.sumLeaves 26 14005248 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13677) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13677 (by decide)
  decide +kernel

theorem h13677 : P.leaf 36 13677 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13677_0 (.nil)) (by decide) (by decide))

theorem cover13678 : P.CoversSplit 26 10 13678 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13678_0 : P.sumLeaves 26 14006272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13678) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13678 (by decide)
  decide +kernel

theorem h13678 : P.leaf 36 13678 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13678_0 (.nil)) (by decide) (by decide))

theorem cover13679 : P.CoversSplit 26 10 13679 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13679_0 : P.sumLeaves 26 14007296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13679) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13679 (by decide)
  decide +kernel

theorem h13679 : P.leaf 36 13679 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13679_0 (.nil)) (by decide) (by decide))

theorem cover13683 : P.CoversSplit 26 10 13683 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13683_0 : P.sumLeaves 26 14011392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13683) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13683 (by decide)
  decide +kernel

theorem h13683 : P.leaf 36 13683 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13683_0 (.nil)) (by decide) (by decide))

theorem cover13684 : P.CoversSplit 26 10 13684 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13684_0 : P.sumLeaves 26 14012416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13684) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13684 (by decide)
  decide +kernel

theorem h13684 : P.leaf 36 13684 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13684_0 (.nil)) (by decide) (by decide))

theorem cover13685 : P.CoversSplit 26 10 13685 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13685_0 : P.sumLeaves 26 14013440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13685) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13685 (by decide)
  decide +kernel

theorem h13685 : P.leaf 36 13685 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13685_0 (.nil)) (by decide) (by decide))

theorem cover13686 : P.CoversSplit 26 10 13686 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13686_0 : P.sumLeaves 26 14014464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13686) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13686 (by decide)
  decide +kernel

theorem h13686 : P.leaf 36 13686 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13686_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13561, 720), (13562, 720), (13563, 720), (13564, 720), (13565, 720), (13566, 720), (13567, 720), (13619, 90), (13620, 360), (13621, 720), (13623, 360), (13628, 180), (13629, 360), (13631, 180), (13666, 360), (13667, 720), (13668, 720), (13669, 720), (13670, 720), (13671, 720), (13672, 720), (13673, 720), (13674, 720), (13675, 720), (13676, 720), (13677, 720), (13678, 720), (13679, 720), (13683, 360), (13684, 720), (13685, 720), (13686, 720)]

theorem segOK : checkSeg 20 perms 13561 13687 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13561 13687 19530 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h13561 (SegSum.cons (w := 720) h13562 (SegSum.cons (w := 720) h13563 (SegSum.cons (w := 720) h13564 (SegSum.cons (w := 720) h13565 (SegSum.cons (w := 720) h13566 (SegSum.cons (w := 720) h13567 (SegSum.cons (w := 90) h13619 (SegSum.cons (w := 360) h13620 (SegSum.cons (w := 720) h13621 (SegSum.cons (w := 360) h13623 (SegSum.cons (w := 180) h13628 (SegSum.cons (w := 360) h13629 (SegSum.cons (w := 180) h13631 (SegSum.cons (w := 360) h13666 (SegSum.cons (w := 720) h13667 (SegSum.cons (w := 720) h13668 (SegSum.cons (w := 720) h13669 (SegSum.cons (w := 720) h13670 (SegSum.cons (w := 720) h13671 (SegSum.cons (w := 720) h13672 (SegSum.cons (w := 720) h13673 (SegSum.cons (w := 720) h13674 (SegSum.cons (w := 720) h13675 (SegSum.cons (w := 720) h13676 (SegSum.cons (w := 720) h13677 (SegSum.cons (w := 720) h13678 (SegSum.cons (w := 720) h13679 (SegSum.cons (w := 360) h13683 (SegSum.cons (w := 720) h13684 (SegSum.cons (w := 720) h13685 (SegSum.cons (w := 720) h13686 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S23
