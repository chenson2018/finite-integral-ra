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

namespace RACert.S6N0.C0.S24

open RACert RACert.Problem

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

theorem cover13687 : P.CoversSplit 26 10 13687 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13687_0 : P.sumLeaves 26 14015488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13687) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13687 (by decide)
  decide +kernel

theorem h13687 : P.leaf 36 13687 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13687_0 (.nil)) (by decide) (by decide))

theorem cover13688 : P.CoversSplit 26 10 13688 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13688_0 : P.sumLeaves 26 14016512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13688) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13688 (by decide)
  decide +kernel

theorem h13688 : P.leaf 36 13688 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13688_0 (.nil)) (by decide) (by decide))

theorem cover13689 : P.CoversSplit 26 10 13689 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13689_0 : P.sumLeaves 26 14017536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13689) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13689 (by decide)
  decide +kernel

theorem h13689 : P.leaf 36 13689 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13689_0 (.nil)) (by decide) (by decide))

theorem cover13690 : P.CoversSplit 26 10 13690 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13690_0 : P.sumLeaves 26 14018560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13690) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13690 (by decide)
  decide +kernel

theorem h13690 : P.leaf 36 13690 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13690_0 (.nil)) (by decide) (by decide))

theorem cover13691 : P.CoversSplit 26 10 13691 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13691_0 : P.sumLeaves 26 14019584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13691) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13691 (by decide)
  decide +kernel

theorem h13691 : P.leaf 36 13691 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13691_0 (.nil)) (by decide) (by decide))

theorem cover13692 : P.CoversSplit 26 10 13692 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13692_0 : P.sumLeaves 26 14020608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13692) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13692 (by decide)
  decide +kernel

theorem h13692 : P.leaf 36 13692 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13692_0 (.nil)) (by decide) (by decide))

theorem cover13693 : P.CoversSplit 26 10 13693 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13693_0 : P.sumLeaves 26 14021632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13693) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13693 (by decide)
  decide +kernel

theorem h13693 : P.leaf 36 13693 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13693_0 (.nil)) (by decide) (by decide))

theorem cover13694 : P.CoversSplit 26 10 13694 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13694_0 : P.sumLeaves 26 14022656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13694) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13694 (by decide)
  decide +kernel

theorem h13694 : P.leaf 36 13694 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13694_0 (.nil)) (by decide) (by decide))

theorem cover13695 : P.CoversSplit 26 10 13695 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13695_0 : P.sumLeaves 26 14023680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13695) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13695 (by decide)
  decide +kernel

theorem h13695 : P.leaf 36 13695 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13695_0 (.nil)) (by decide) (by decide))

theorem cover13792 : P.CoversSplit 26 10 13792 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13792_0 : P.sumLeaves 26 14123008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13792) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13792 (by decide)
  decide +kernel

theorem h13792 : P.leaf 36 13792 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13792_0 (.nil)) (by decide) (by decide))

theorem cover13793 : P.CoversSplit 26 10 13793 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13793_0 : P.sumLeaves 26 14124032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13793) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13793 (by decide)
  decide +kernel

theorem h13793 : P.leaf 36 13793 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13793_0 (.nil)) (by decide) (by decide))

theorem cover13795 : P.CoversSplit 26 10 13795 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13795_0 : P.sumLeaves 26 14126080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13795) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13795 (by decide)
  decide +kernel

theorem h13795 : P.leaf 36 13795 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13795_0 (.nil)) (by decide) (by decide))

theorem cover13796 : P.CoversSplit 26 10 13796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13796_0 : P.sumLeaves 26 14127104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13796) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13796 (by decide)
  decide +kernel

theorem h13796 : P.leaf 36 13796 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13796_0 (.nil)) (by decide) (by decide))

theorem cover13797 : P.CoversSplit 26 10 13797 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13797_0 : P.sumLeaves 26 14128128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13797) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13797 (by decide)
  decide +kernel

theorem h13797 : P.leaf 36 13797 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13797_0 (.nil)) (by decide) (by decide))

theorem cover13798 : P.CoversSplit 26 10 13798 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13798_0 : P.sumLeaves 26 14129152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13798) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13798 (by decide)
  decide +kernel

theorem h13798 : P.leaf 36 13798 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13798_0 (.nil)) (by decide) (by decide))

theorem cover13799 : P.CoversSplit 26 10 13799 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13799_0 : P.sumLeaves 26 14130176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13799) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13799 (by decide)
  decide +kernel

theorem h13799 : P.leaf 36 13799 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13799_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13668, 720), (13669, 720), (13670, 720), (13671, 720), (13672, 720), (13673, 720), (13674, 720), (13675, 720), (13676, 720), (13677, 720), (13678, 720), (13679, 720), (13683, 360), (13684, 720), (13685, 720), (13686, 720), (13687, 720), (13688, 720), (13689, 720), (13690, 720), (13691, 720), (13692, 720), (13693, 720), (13694, 720), (13695, 720), (13792, 360), (13793, 720), (13795, 360), (13796, 720), (13797, 720), (13798, 720), (13799, 720)]

theorem segOK : checkSeg 20 perms 13668 13804 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13668 13804 21960 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h13668 (SegSum.cons (w := 720) h13669 (SegSum.cons (w := 720) h13670 (SegSum.cons (w := 720) h13671 (SegSum.cons (w := 720) h13672 (SegSum.cons (w := 720) h13673 (SegSum.cons (w := 720) h13674 (SegSum.cons (w := 720) h13675 (SegSum.cons (w := 720) h13676 (SegSum.cons (w := 720) h13677 (SegSum.cons (w := 720) h13678 (SegSum.cons (w := 720) h13679 (SegSum.cons (w := 360) h13683 (SegSum.cons (w := 720) h13684 (SegSum.cons (w := 720) h13685 (SegSum.cons (w := 720) h13686 (SegSum.cons (w := 720) h13687 (SegSum.cons (w := 720) h13688 (SegSum.cons (w := 720) h13689 (SegSum.cons (w := 720) h13690 (SegSum.cons (w := 720) h13691 (SegSum.cons (w := 720) h13692 (SegSum.cons (w := 720) h13693 (SegSum.cons (w := 720) h13694 (SegSum.cons (w := 720) h13695 (SegSum.cons (w := 360) h13792 (SegSum.cons (w := 720) h13793 (SegSum.cons (w := 360) h13795 (SegSum.cons (w := 720) h13796 (SegSum.cons (w := 720) h13797 (SegSum.cons (w := 720) h13798 (SegSum.cons (w := 720) h13799 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S24
