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

namespace RACert.S6N0.C0.S30

open RACert RACert.Problem

theorem cover15741 : P.CoversSplit 26 10 15741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15741_0 : P.sumLeaves 26 16118784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15741) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15741 (by decide)
  decide +kernel

theorem h15741 : P.leaf 36 15741 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15741_0 (.nil)) (by decide) (by decide))

theorem cover15742 : P.CoversSplit 26 10 15742 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15742_0 : P.sumLeaves 26 16119808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15742) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15742 (by decide)
  decide +kernel

theorem h15742 : P.leaf 36 15742 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15742_0 (.nil)) (by decide) (by decide))

theorem cover15743 : P.CoversSplit 26 10 15743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15743_0 : P.sumLeaves 26 16120832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15743) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15743 (by decide)
  decide +kernel

theorem h15743 : P.leaf 36 15743 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15743_0 (.nil)) (by decide) (by decide))

theorem cover15795 : P.CoversSplit 26 10 15795 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15795_0 : P.sumLeaves 26 16174080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15795) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15795 (by decide)
  decide +kernel

theorem h15795 : P.leaf 36 15795 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15795_0 (.nil)) (by decide) (by decide))

theorem cover15796 : P.CoversSplit 26 10 15796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15796_0 : P.sumLeaves 26 16175104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15796) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15796 (by decide)
  decide +kernel

theorem h15796 : P.leaf 36 15796 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15796_0 (.nil)) (by decide) (by decide))

theorem cover15797 : P.CoversSplit 26 10 15797 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15797_0 : P.sumLeaves 26 16176128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15797) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15797 (by decide)
  decide +kernel

theorem h15797 : P.leaf 36 15797 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15797_0 (.nil)) (by decide) (by decide))

theorem cover15799 : P.CoversSplit 26 10 15799 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15799_0 : P.sumLeaves 26 16178176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15799) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15799 (by decide)
  decide +kernel

theorem h15799 : P.leaf 36 15799 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15799_0 (.nil)) (by decide) (by decide))

theorem cover15800 : P.CoversSplit 26 10 15800 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15800_0 : P.sumLeaves 26 16179200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15800) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15800 (by decide)
  decide +kernel

theorem h15800 : P.leaf 36 15800 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15800_0 (.nil)) (by decide) (by decide))

theorem cover15801 : P.CoversSplit 26 10 15801 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15801_0 : P.sumLeaves 26 16180224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15801) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15801 (by decide)
  decide +kernel

theorem h15801 : P.leaf 36 15801 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15801_0 (.nil)) (by decide) (by decide))

theorem cover15803 : P.CoversSplit 26 10 15803 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15803_0 : P.sumLeaves 26 16182272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15803) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15803 (by decide)
  decide +kernel

theorem h15803 : P.leaf 36 15803 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15803_0 (.nil)) (by decide) (by decide))

theorem cover15804 : P.CoversSplit 26 10 15804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15804_0 : P.sumLeaves 26 16183296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15804) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15804 (by decide)
  decide +kernel

theorem h15804 : P.leaf 36 15804 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15804_0 (.nil)) (by decide) (by decide))

theorem cover15805 : P.CoversSplit 26 10 15805 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15805_0 : P.sumLeaves 26 16184320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15805) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15805 (by decide)
  decide +kernel

theorem h15805 : P.leaf 36 15805 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15805_0 (.nil)) (by decide) (by decide))

theorem cover15807 : P.CoversSplit 26 10 15807 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15807_0 : P.sumLeaves 26 16186368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15807) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15807 (by decide)
  decide +kernel

theorem h15807 : P.leaf 36 15807 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15807_0 (.nil)) (by decide) (by decide))

theorem cover15827 : P.CoversSplit 26 10 15827 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15827_0 : P.sumLeaves 26 16206848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15827) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15827 (by decide)
  decide +kernel

theorem h15827 : P.leaf 36 15827 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15827_0 (.nil)) (by decide) (by decide))

theorem cover15828 : P.CoversSplit 26 10 15828 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15828_0 : P.sumLeaves 26 16207872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15828) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15828 (by decide)
  decide +kernel

theorem h15828 : P.leaf 36 15828 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15828_0 (.nil)) (by decide) (by decide))

theorem cover15829 : P.CoversSplit 26 10 15829 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15829_0 : P.sumLeaves 26 16208896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15829) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15829 (by decide)
  decide +kernel

theorem h15829 : P.leaf 36 15829 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15829_0 (.nil)) (by decide) (by decide))

theorem cover15830 : P.CoversSplit 26 10 15830 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15830_0 : P.sumLeaves 26 16209920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15830) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15830 (by decide)
  decide +kernel

theorem h15830 : P.leaf 36 15830 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15830_0 (.nil)) (by decide) (by decide))

theorem cover15831 : P.CoversSplit 26 10 15831 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15831_0 : P.sumLeaves 26 16210944 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15831) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15831 (by decide)
  decide +kernel

theorem h15831 : P.leaf 36 15831 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15831_0 (.nil)) (by decide) (by decide))

theorem cover15836 : P.CoversSplit 26 10 15836 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15836_0 : P.sumLeaves 26 16216064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15836) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15836 (by decide)
  decide +kernel

theorem h15836 : P.leaf 36 15836 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15836_0 (.nil)) (by decide) (by decide))

theorem cover15837 : P.CoversSplit 26 10 15837 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15837_0 : P.sumLeaves 26 16217088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15837) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15837 (by decide)
  decide +kernel

theorem h15837 : P.leaf 36 15837 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15837_0 (.nil)) (by decide) (by decide))

theorem cover15839 : P.CoversSplit 26 10 15839 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15839_0 : P.sumLeaves 26 16219136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15839) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15839 (by decide)
  decide +kernel

theorem h15839 : P.leaf 36 15839 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15839_0 (.nil)) (by decide) (by decide))

theorem cover15842 : P.CoversSplit 26 10 15842 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15842_0 : P.sumLeaves 26 16222208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15842) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15842 (by decide)
  decide +kernel

theorem h15842 : P.leaf 36 15842 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15842_0 (.nil)) (by decide) (by decide))

theorem cover15843 : P.CoversSplit 26 10 15843 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15843_0 : P.sumLeaves 26 16223232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15843) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15843 (by decide)
  decide +kernel

theorem h15843 : P.leaf 36 15843 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15843_0 (.nil)) (by decide) (by decide))

theorem cover15844 : P.CoversSplit 26 10 15844 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15844_0 : P.sumLeaves 26 16224256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15844) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15844 (by decide)
  decide +kernel

theorem h15844 : P.leaf 36 15844 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15844_0 (.nil)) (by decide) (by decide))

theorem cover15845 : P.CoversSplit 26 10 15845 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15845_0 : P.sumLeaves 26 16225280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15845) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15845 (by decide)
  decide +kernel

theorem h15845 : P.leaf 36 15845 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15845_0 (.nil)) (by decide) (by decide))

theorem cover15846 : P.CoversSplit 26 10 15846 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15846_0 : P.sumLeaves 26 16226304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15846) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15846 (by decide)
  decide +kernel

theorem h15846 : P.leaf 36 15846 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15846_0 (.nil)) (by decide) (by decide))

theorem cover15847 : P.CoversSplit 26 10 15847 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15847_0 : P.sumLeaves 26 16227328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15847) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15847 (by decide)
  decide +kernel

theorem h15847 : P.leaf 36 15847 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15847_0 (.nil)) (by decide) (by decide))

theorem cover15848 : P.CoversSplit 26 10 15848 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15848_0 : P.sumLeaves 26 16228352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15848) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15848 (by decide)
  decide +kernel

theorem h15848 : P.leaf 36 15848 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15848_0 (.nil)) (by decide) (by decide))

theorem cover15849 : P.CoversSplit 26 10 15849 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15849_0 : P.sumLeaves 26 16229376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15849) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15849 (by decide)
  decide +kernel

theorem h15849 : P.leaf 36 15849 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15849_0 (.nil)) (by decide) (by decide))

theorem cover15850 : P.CoversSplit 26 10 15850 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15850_0 : P.sumLeaves 26 16230400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15850) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15850 (by decide)
  decide +kernel

theorem h15850 : P.leaf 36 15850 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15850_0 (.nil)) (by decide) (by decide))

theorem cover15851 : P.CoversSplit 26 10 15851 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15851_0 : P.sumLeaves 26 16231424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15851) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15851 (by decide)
  decide +kernel

theorem h15851 : P.leaf 36 15851 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15851_0 (.nil)) (by decide) (by decide))

theorem cover15852 : P.CoversSplit 26 10 15852 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15852_0 : P.sumLeaves 26 16232448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15852) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15852 (by decide)
  decide +kernel

theorem h15852 : P.leaf 36 15852 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15852_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(15741, 360), (15742, 360), (15743, 360), (15795, 180), (15796, 360), (15797, 720), (15799, 360), (15800, 360), (15801, 720), (15803, 360), (15804, 360), (15805, 720), (15807, 360), (15827, 180), (15828, 720), (15829, 720), (15830, 720), (15831, 720), (15836, 360), (15837, 720), (15839, 360), (15842, 360), (15843, 720), (15844, 720), (15845, 720), (15846, 720), (15847, 720), (15848, 720), (15849, 720), (15850, 720), (15851, 720), (15852, 720)]

theorem segOK : checkSeg 20 perms 15741 15853 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 15741 15853 17640 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h15741 (SegSum.cons (w := 360) h15742 (SegSum.cons (w := 360) h15743 (SegSum.cons (w := 180) h15795 (SegSum.cons (w := 360) h15796 (SegSum.cons (w := 720) h15797 (SegSum.cons (w := 360) h15799 (SegSum.cons (w := 360) h15800 (SegSum.cons (w := 720) h15801 (SegSum.cons (w := 360) h15803 (SegSum.cons (w := 360) h15804 (SegSum.cons (w := 720) h15805 (SegSum.cons (w := 360) h15807 (SegSum.cons (w := 180) h15827 (SegSum.cons (w := 720) h15828 (SegSum.cons (w := 720) h15829 (SegSum.cons (w := 720) h15830 (SegSum.cons (w := 720) h15831 (SegSum.cons (w := 360) h15836 (SegSum.cons (w := 720) h15837 (SegSum.cons (w := 360) h15839 (SegSum.cons (w := 360) h15842 (SegSum.cons (w := 720) h15843 (SegSum.cons (w := 720) h15844 (SegSum.cons (w := 720) h15845 (SegSum.cons (w := 720) h15846 (SegSum.cons (w := 720) h15847 (SegSum.cons (w := 720) h15848 (SegSum.cons (w := 720) h15849 (SegSum.cons (w := 720) h15850 (SegSum.cons (w := 720) h15851 (SegSum.cons (w := 720) h15852 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S30
