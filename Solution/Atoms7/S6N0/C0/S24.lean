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

namespace RACert.S6N0.C0.S24

open RACert RACert.Problem

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

theorem cover13804 : P.CoversSplit 26 10 13804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13804_0 : P.sumLeaves 26 14135296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13804) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13804 (by decide)
  decide +kernel

theorem h13804 : P.leaf 36 13804 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13804_0 (.nil)) (by decide) (by decide))

theorem cover13805 : P.CoversSplit 26 10 13805 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13805_0 : P.sumLeaves 26 14136320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13805) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13805 (by decide)
  decide +kernel

theorem h13805 : P.leaf 36 13805 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13805_0 (.nil)) (by decide) (by decide))

theorem cover13807 : P.CoversSplit 26 10 13807 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13807_0 : P.sumLeaves 26 14138368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13807) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13807 (by decide)
  decide +kernel

theorem h13807 : P.leaf 36 13807 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13807_0 (.nil)) (by decide) (by decide))

theorem cover13808 : P.CoversSplit 26 10 13808 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13808_0 : P.sumLeaves 26 14139392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13808) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13808 (by decide)
  decide +kernel

theorem h13808 : P.leaf 36 13808 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13808_0 (.nil)) (by decide) (by decide))

theorem cover13809 : P.CoversSplit 26 10 13809 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13809_0 : P.sumLeaves 26 14140416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13809) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13809 (by decide)
  decide +kernel

theorem h13809 : P.leaf 36 13809 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13809_0 (.nil)) (by decide) (by decide))

theorem cover13811 : P.CoversSplit 26 10 13811 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c13811_0 : P.sumLeaves 26 14142464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13811) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13811 (by decide)
  decide +kernel

theorem h13811 : P.leaf 36 13811 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13811_0 (.nil)) (by decide) (by decide))

theorem cover13812 : P.CoversSplit 26 10 13812 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13812_0 : P.sumLeaves 26 14143488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13812) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13812 (by decide)
  decide +kernel

theorem h13812 : P.leaf 36 13812 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13812_0 (.nil)) (by decide) (by decide))

theorem cover13813 : P.CoversSplit 26 10 13813 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13813_0 : P.sumLeaves 26 14144512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13813) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13813 (by decide)
  decide +kernel

theorem h13813 : P.leaf 36 13813 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13813_0 (.nil)) (by decide) (by decide))

theorem cover13814 : P.CoversSplit 26 10 13814 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13814_0 : P.sumLeaves 26 14145536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13814) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13814 (by decide)
  decide +kernel

theorem h13814 : P.leaf 36 13814 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13814_0 (.nil)) (by decide) (by decide))

theorem cover13815 : P.CoversSplit 26 10 13815 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13815_0 : P.sumLeaves 26 14146560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13815) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13815 (by decide)
  decide +kernel

theorem h13815 : P.leaf 36 13815 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13815_0 (.nil)) (by decide) (by decide))

theorem cover13820 : P.CoversSplit 26 10 13820 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13820_0 : P.sumLeaves 26 14151680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13820) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13820 (by decide)
  decide +kernel

theorem h13820 : P.leaf 36 13820 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13820_0 (.nil)) (by decide) (by decide))

theorem cover13821 : P.CoversSplit 26 10 13821 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13821_0 : P.sumLeaves 26 14152704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13821) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13821 (by decide)
  decide +kernel

theorem h13821 : P.leaf 36 13821 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13821_0 (.nil)) (by decide) (by decide))

theorem cover13823 : P.CoversSplit 26 10 13823 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13823_0 : P.sumLeaves 26 14154752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13823) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13823 (by decide)
  decide +kernel

theorem h13823 : P.leaf 36 13823 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13823_0 (.nil)) (by decide) (by decide))

theorem cover13906 : P.CoversSplit 26 10 13906 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [467]) (by decide +kernel)

theorem c13906_0 : P.sumLeaves 26 14239744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13906) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13906 (by decide)
  decide +kernel

theorem h13906 : P.leaf 36 13906 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13906_0 (.nil)) (by decide) (by decide))

theorem cover13907 : P.CoversSplit 26 10 13907 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13907_0 : P.sumLeaves 26 14240768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13907) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13907 (by decide)
  decide +kernel

theorem h13907 : P.leaf 36 13907 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13907_0 (.nil)) (by decide) (by decide))

theorem cover13910 : P.CoversSplit 26 10 13910 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c13910_0 : P.sumLeaves 26 14243840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13910) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13910 (by decide)
  decide +kernel

theorem h13910 : P.leaf 36 13910 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13910_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13687, 720), (13688, 720), (13689, 720), (13690, 720), (13691, 720), (13692, 720), (13693, 720), (13694, 720), (13695, 720), (13792, 360), (13793, 720), (13795, 360), (13796, 720), (13797, 720), (13798, 720), (13799, 720), (13804, 360), (13805, 720), (13807, 360), (13808, 360), (13809, 720), (13811, 360), (13812, 720), (13813, 720), (13814, 720), (13815, 720), (13820, 360), (13821, 720), (13823, 360), (13906, 720), (13907, 720), (13910, 720)]

theorem segOK : checkSeg 20 perms 13687 13911 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13687 13911 20160 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h13687 (SegSum.cons (w := 720) h13688 (SegSum.cons (w := 720) h13689 (SegSum.cons (w := 720) h13690 (SegSum.cons (w := 720) h13691 (SegSum.cons (w := 720) h13692 (SegSum.cons (w := 720) h13693 (SegSum.cons (w := 720) h13694 (SegSum.cons (w := 720) h13695 (SegSum.cons (w := 360) h13792 (SegSum.cons (w := 720) h13793 (SegSum.cons (w := 360) h13795 (SegSum.cons (w := 720) h13796 (SegSum.cons (w := 720) h13797 (SegSum.cons (w := 720) h13798 (SegSum.cons (w := 720) h13799 (SegSum.cons (w := 360) h13804 (SegSum.cons (w := 720) h13805 (SegSum.cons (w := 360) h13807 (SegSum.cons (w := 360) h13808 (SegSum.cons (w := 720) h13809 (SegSum.cons (w := 360) h13811 (SegSum.cons (w := 720) h13812 (SegSum.cons (w := 720) h13813 (SegSum.cons (w := 720) h13814 (SegSum.cons (w := 720) h13815 (SegSum.cons (w := 360) h13820 (SegSum.cons (w := 720) h13821 (SegSum.cons (w := 360) h13823 (SegSum.cons (w := 720) h13906 (SegSum.cons (w := 720) h13907 (SegSum.cons (w := 720) h13910 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S24
