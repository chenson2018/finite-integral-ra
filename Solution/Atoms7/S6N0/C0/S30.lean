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

theorem h15741 : P.leaf 36 15741 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15741) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15741) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15741 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15742 : P.CoversSplit 26 10 15742 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15742 : P.leaf 36 15742 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15742) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15742) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15742 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15743 : P.CoversSplit 26 10 15743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15743 : P.leaf 36 15743 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15743) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15743) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15743 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15795 : P.CoversSplit 26 10 15795 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h15795 : P.leaf 36 15795 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15795) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15795) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15795 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15796 : P.CoversSplit 26 10 15796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15796 : P.leaf 36 15796 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15796) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15796) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15796 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15797 : P.CoversSplit 26 10 15797 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15797 : P.leaf 36 15797 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15797) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15797) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15797 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15799 : P.CoversSplit 26 10 15799 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15799 : P.leaf 36 15799 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15799) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15799) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15799 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15800 : P.CoversSplit 26 10 15800 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15800 : P.leaf 36 15800 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15800) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15800) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15800 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15801 : P.CoversSplit 26 10 15801 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15801 : P.leaf 36 15801 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15801) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15801) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15801 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15803 : P.CoversSplit 26 10 15803 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15803 : P.leaf 36 15803 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15803) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15803) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15803 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15804 : P.CoversSplit 26 10 15804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15804 : P.leaf 36 15804 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15804) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15804) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15804 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15805 : P.CoversSplit 26 10 15805 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15805 : P.leaf 36 15805 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15805) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15805) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15805 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15807 : P.CoversSplit 26 10 15807 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15807 : P.leaf 36 15807 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15807) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15807) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15807 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15827 : P.CoversSplit 26 10 15827 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h15827 : P.leaf 36 15827 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15827) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15827) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15827 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15828 : P.CoversSplit 26 10 15828 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15828 : P.leaf 36 15828 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15828) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15828) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15828 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15829 : P.CoversSplit 26 10 15829 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15829 : P.leaf 36 15829 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15829) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15829) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15829 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15830 : P.CoversSplit 26 10 15830 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15830 : P.leaf 36 15830 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15830) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15830) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15830 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15831 : P.CoversSplit 26 10 15831 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15831 : P.leaf 36 15831 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15831) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15831) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15831 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15836 : P.CoversSplit 26 10 15836 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15836 : P.leaf 36 15836 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15836) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15836) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15836 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15837 : P.CoversSplit 26 10 15837 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15837 : P.leaf 36 15837 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15837) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15837) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15837 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15839 : P.CoversSplit 26 10 15839 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15839 : P.leaf 36 15839 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15839) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15839) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15839 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15842 : P.CoversSplit 26 10 15842 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h15842 : P.leaf 36 15842 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15842) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15842) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15842 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15843 : P.CoversSplit 26 10 15843 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h15843 : P.leaf 36 15843 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15843) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15843) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15843 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15844 : P.CoversSplit 26 10 15844 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15844 : P.leaf 36 15844 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15844) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15844) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15844 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15845 : P.CoversSplit 26 10 15845 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15845 : P.leaf 36 15845 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15845) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15845) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15845 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15846 : P.CoversSplit 26 10 15846 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15846 : P.leaf 36 15846 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15846) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15846) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15846 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15847 : P.CoversSplit 26 10 15847 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15847 : P.leaf 36 15847 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15847) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15847) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15847 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15848 : P.CoversSplit 26 10 15848 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15848 : P.leaf 36 15848 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15848) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15848) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15848 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15849 : P.CoversSplit 26 10 15849 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15849 : P.leaf 36 15849 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15849) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15849) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15849 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15850 : P.CoversSplit 26 10 15850 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15850 : P.leaf 36 15850 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15850) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15850) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15850 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15851 : P.CoversSplit 26 10 15851 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15851 : P.leaf 36 15851 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15851) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15851) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15851 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15852 : P.CoversSplit 26 10 15852 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15852 : P.leaf 36 15852 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15852) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15852) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15852 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(15741, 360), (15742, 360), (15743, 360), (15795, 180), (15796, 360), (15797, 720), (15799, 360), (15800, 360), (15801, 720), (15803, 360), (15804, 360), (15805, 720), (15807, 360), (15827, 180), (15828, 720), (15829, 720), (15830, 720), (15831, 720), (15836, 360), (15837, 720), (15839, 360), (15842, 360), (15843, 720), (15844, 720), (15845, 720), (15846, 720), (15847, 720), (15848, 720), (15849, 720), (15850, 720), (15851, 720), (15852, 720)]

theorem segOK : checkSeg 20 perms 15741 15853 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 15741 15853 17640 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h15741 (SegSum.cons (w := 360) h15742 (SegSum.cons (w := 360) h15743 (SegSum.cons (w := 180) h15795 (SegSum.cons (w := 360) h15796 (SegSum.cons (w := 720) h15797 (SegSum.cons (w := 360) h15799 (SegSum.cons (w := 360) h15800 (SegSum.cons (w := 720) h15801 (SegSum.cons (w := 360) h15803 (SegSum.cons (w := 360) h15804 (SegSum.cons (w := 720) h15805 (SegSum.cons (w := 360) h15807 (SegSum.cons (w := 180) h15827 (SegSum.cons (w := 720) h15828 (SegSum.cons (w := 720) h15829 (SegSum.cons (w := 720) h15830 (SegSum.cons (w := 720) h15831 (SegSum.cons (w := 360) h15836 (SegSum.cons (w := 720) h15837 (SegSum.cons (w := 360) h15839 (SegSum.cons (w := 360) h15842 (SegSum.cons (w := 720) h15843 (SegSum.cons (w := 720) h15844 (SegSum.cons (w := 720) h15845 (SegSum.cons (w := 720) h15846 (SegSum.cons (w := 720) h15847 (SegSum.cons (w := 720) h15848 (SegSum.cons (w := 720) h15849 (SegSum.cons (w := 720) h15850 (SegSum.cons (w := 720) h15851 (SegSum.cons (w := 720) h15852 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S30
