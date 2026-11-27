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

namespace RACert.S6N0.C0.S31

open RACert RACert.Problem

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

theorem cover15853 : P.CoversSplit 26 10 15853 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15853_0 : P.sumLeaves 26 16233472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15853) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15853 (by decide)
  decide +kernel

theorem h15853 : P.leaf 36 15853 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15853_0 (.nil)) (by decide) (by decide))

theorem cover15854 : P.CoversSplit 26 10 15854 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15854_0 : P.sumLeaves 26 16234496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15854) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15854 (by decide)
  decide +kernel

theorem h15854 : P.leaf 36 15854 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15854_0 (.nil)) (by decide) (by decide))

theorem cover15855 : P.CoversSplit 26 10 15855 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15855_0 : P.sumLeaves 26 16235520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15855) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15855 (by decide)
  decide +kernel

theorem h15855 : P.leaf 36 15855 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15855_0 (.nil)) (by decide) (by decide))

theorem cover15859 : P.CoversSplit 26 10 15859 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15859_0 : P.sumLeaves 26 16239616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15859) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15859 (by decide)
  decide +kernel

theorem h15859 : P.leaf 36 15859 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15859_0 (.nil)) (by decide) (by decide))

theorem cover15860 : P.CoversSplit 26 10 15860 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15860_0 : P.sumLeaves 26 16240640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15860) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15860 (by decide)
  decide +kernel

theorem h15860 : P.leaf 36 15860 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15860_0 (.nil)) (by decide) (by decide))

theorem cover15861 : P.CoversSplit 26 10 15861 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15861_0 : P.sumLeaves 26 16241664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15861) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15861 (by decide)
  decide +kernel

theorem h15861 : P.leaf 36 15861 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15861_0 (.nil)) (by decide) (by decide))

theorem cover15862 : P.CoversSplit 26 10 15862 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15862_0 : P.sumLeaves 26 16242688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15862) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15862 (by decide)
  decide +kernel

theorem h15862 : P.leaf 36 15862 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15862_0 (.nil)) (by decide) (by decide))

theorem cover15863 : P.CoversSplit 26 10 15863 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15863_0 : P.sumLeaves 26 16243712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15863) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15863 (by decide)
  decide +kernel

theorem h15863 : P.leaf 36 15863 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15863_0 (.nil)) (by decide) (by decide))

theorem cover15864 : P.CoversSplit 26 10 15864 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15864_0 : P.sumLeaves 26 16244736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15864) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15864 (by decide)
  decide +kernel

theorem h15864 : P.leaf 36 15864 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15864_0 (.nil)) (by decide) (by decide))

theorem cover15865 : P.CoversSplit 26 10 15865 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15865_0 : P.sumLeaves 26 16245760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15865) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15865 (by decide)
  decide +kernel

theorem h15865 : P.leaf 36 15865 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15865_0 (.nil)) (by decide) (by decide))

theorem cover15866 : P.CoversSplit 26 10 15866 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15866_0 : P.sumLeaves 26 16246784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15866) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15866 (by decide)
  decide +kernel

theorem h15866 : P.leaf 36 15866 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15866_0 (.nil)) (by decide) (by decide))

theorem cover15867 : P.CoversSplit 26 10 15867 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15867_0 : P.sumLeaves 26 16247808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15867) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15867 (by decide)
  decide +kernel

theorem h15867 : P.leaf 36 15867 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15867_0 (.nil)) (by decide) (by decide))

theorem cover15868 : P.CoversSplit 26 10 15868 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15868_0 : P.sumLeaves 26 16248832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15868) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15868 (by decide)
  decide +kernel

theorem h15868 : P.leaf 36 15868 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15868_0 (.nil)) (by decide) (by decide))

theorem cover15869 : P.CoversSplit 26 10 15869 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15869_0 : P.sumLeaves 26 16249856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15869) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15869 (by decide)
  decide +kernel

theorem h15869 : P.leaf 36 15869 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15869_0 (.nil)) (by decide) (by decide))

theorem cover15870 : P.CoversSplit 26 10 15870 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15870_0 : P.sumLeaves 26 16250880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15870) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15870 (by decide)
  decide +kernel

theorem h15870 : P.leaf 36 15870 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15870_0 (.nil)) (by decide) (by decide))

theorem cover15871 : P.CoversSplit 26 10 15871 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15871_0 : P.sumLeaves 26 16251904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15871) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem h15871 : P.leaf 36 15871 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15871_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(15830, 720), (15831, 720), (15836, 360), (15837, 720), (15839, 360), (15842, 360), (15843, 720), (15844, 720), (15845, 720), (15846, 720), (15847, 720), (15848, 720), (15849, 720), (15850, 720), (15851, 720), (15852, 720), (15853, 720), (15854, 720), (15855, 720), (15859, 360), (15860, 720), (15861, 720), (15862, 720), (15863, 720), (15864, 720), (15865, 720), (15866, 720), (15867, 720), (15868, 720), (15869, 720), (15870, 720), (15871, 720)]

theorem segOK : checkSeg 20 perms 15830 16176 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 15830 16176 21600 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h15830 (SegSum.cons (w := 720) h15831 (SegSum.cons (w := 360) h15836 (SegSum.cons (w := 720) h15837 (SegSum.cons (w := 360) h15839 (SegSum.cons (w := 360) h15842 (SegSum.cons (w := 720) h15843 (SegSum.cons (w := 720) h15844 (SegSum.cons (w := 720) h15845 (SegSum.cons (w := 720) h15846 (SegSum.cons (w := 720) h15847 (SegSum.cons (w := 720) h15848 (SegSum.cons (w := 720) h15849 (SegSum.cons (w := 720) h15850 (SegSum.cons (w := 720) h15851 (SegSum.cons (w := 720) h15852 (SegSum.cons (w := 720) h15853 (SegSum.cons (w := 720) h15854 (SegSum.cons (w := 720) h15855 (SegSum.cons (w := 360) h15859 (SegSum.cons (w := 720) h15860 (SegSum.cons (w := 720) h15861 (SegSum.cons (w := 720) h15862 (SegSum.cons (w := 720) h15863 (SegSum.cons (w := 720) h15864 (SegSum.cons (w := 720) h15865 (SegSum.cons (w := 720) h15866 (SegSum.cons (w := 720) h15867 (SegSum.cons (w := 720) h15868 (SegSum.cons (w := 720) h15869 (SegSum.cons (w := 720) h15870 (SegSum.cons (w := 720) h15871 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S31
