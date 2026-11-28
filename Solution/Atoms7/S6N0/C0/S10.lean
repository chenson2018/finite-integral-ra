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

namespace RACert.S6N0.C0.S10

open RACert RACert.Problem

theorem cover3847 : P.CoversSplit 26 10 3847 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3847 : P.leaf 36 3847 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3847) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3847) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3847 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover10572 : P.CoversSplit 26 10 10572 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h10572 : P.leaf 36 10572 = 2512 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 10572) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 10572) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover10572 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3849 : P.leaf 36 3849 = 2512 :=
  orient72 (v := 10572) (by decide) (by decide +kernel) h10572

theorem cover3851 : P.CoversSplit 26 10 3851 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem h3851 : P.leaf 36 3851 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3851) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3851) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3851 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3855 : P.CoversSplit 26 10 3855 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3855 : P.leaf 36 3855 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3855) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3855) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3855 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3858 : P.CoversSplit 26 10 3858 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3858 : P.leaf 36 3858 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3858) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3858) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3858 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3859 : P.CoversSplit 26 10 3859 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3859 : P.leaf 36 3859 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3859) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3859) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3859 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3860 : P.CoversSplit 26 10 3860 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3860 : P.leaf 36 3860 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3860) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3860) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3860 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3861 : P.CoversSplit 26 10 3861 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3861 : P.leaf 36 3861 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3861) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3861) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3861 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3862 : P.CoversSplit 26 10 3862 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3862 : P.leaf 36 3862 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3862) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3862) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3862 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3863 : P.CoversSplit 26 10 3863 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3863 : P.leaf 36 3863 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3863) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3863) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3863 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3864 : P.CoversSplit 26 10 3864 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [480]) (by decide +kernel)

theorem h3864 : P.leaf 36 3864 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3864) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3864) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3864 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3865 : P.CoversSplit 26 10 3865 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [480]) (by decide +kernel)

theorem h3865 : P.leaf 36 3865 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3865) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3865) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3865 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3866 : P.CoversSplit 26 10 3866 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3866 : P.leaf 36 3866 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3866) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3866) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3866 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3867 : P.CoversSplit 26 10 3867 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3867 : P.leaf 36 3867 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3867) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3867) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3867 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3868 : P.CoversSplit 26 10 3868 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3868 : P.leaf 36 3868 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3868) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3868) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3868 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3869 : P.CoversSplit 26 10 3869 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h3869 : P.leaf 36 3869 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3869) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3869) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3869 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3870 : P.CoversSplit 26 10 3870 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3870 : P.leaf 36 3870 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3870) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3870) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3870 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3871 : P.CoversSplit 26 10 3871 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3871 : P.leaf 36 3871 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3871) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3871) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3871 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3894 : P.CoversSplit 26 10 3894 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem h3894 : P.leaf 36 3894 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3894) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3894) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3894 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3895 : P.CoversSplit 26 10 3895 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3895 : P.leaf 36 3895 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3895) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3895) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3895 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3896 : P.CoversSplit 26 10 3896 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h3896 : P.leaf 36 3896 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3896) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3896) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3896 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3897 : P.CoversSplit 26 10 3897 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h3897 : P.leaf 36 3897 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3897) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3897) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3897 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3898 : P.CoversSplit 26 10 3898 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3898 : P.leaf 36 3898 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3898) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3898) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3898 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3899 : P.CoversSplit 26 10 3899 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3899 : P.leaf 36 3899 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3899) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3899) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3899 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3902 : P.CoversSplit 26 10 3902 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3902 : P.leaf 36 3902 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3902) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3902) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3902 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3903 : P.CoversSplit 26 10 3903 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3903 : P.leaf 36 3903 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3903) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3903) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3903 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6546 : P.CoversSplit 26 10 6546 0x8000000000000000000000000000000000000000000000001000000000000001000000000000000000000000000000000000000000000000000001000000000100000000000000000000000000000000000000000000000000000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 481, 489, 530, 538, 629, 636, 922, 930, 972, 979, 1315, 1322]) (ps := [(7, [467, 468], [467, 468])]) (by decide +kernel)

theorem h6546 : P.leaf 36 6546 = 36780 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 6546) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6546) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6546) (weight := rowWeight keep0 twice0) (xs := [256, 276, 512, 552, 768, 828, 1023]) check rows elimOK (by decide) (by decide) cover6546 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3912 : P.leaf 36 3912 = 36780 :=
  orient6 (v := 6546) (by decide) (by decide +kernel) h6546

theorem cover6547 : P.CoversSplit 26 10 6547 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 489, 530, 538, 629, 636, 922, 930]) (by decide +kernel)

theorem h6547 : P.leaf 36 6547 = 83056 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 6547) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6547) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6547) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover6547 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3913 : P.leaf 36 3913 = 83056 :=
  orient6 (v := 6547) (by decide) (by decide +kernel) h6547

theorem cover3914 : P.CoversSplit 26 10 3914 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem h3914 : P.leaf 36 3914 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3914) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3914) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3914 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3915 : P.CoversSplit 26 10 3915 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem h3915 : P.leaf 36 3915 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3915) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3915) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3915 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3918 : P.CoversSplit 26 10 3918 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3918 : P.leaf 36 3918 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3918) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3918) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3918 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3919 : P.CoversSplit 26 10 3919 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h3919 : P.leaf 36 3919 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3919) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3919) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3919 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3847, 360), (3849, 180), (3851, 360), (3855, 180), (3858, 360), (3859, 360), (3860, 360), (3861, 360), (3862, 720), (3863, 720), (3864, 720), (3865, 720), (3866, 720), (3867, 720), (3868, 720), (3869, 720), (3870, 720), (3871, 720), (3894, 180), (3895, 180), (3896, 360), (3897, 360), (3898, 720), (3899, 720), (3902, 360), (3903, 360), (3912, 90), (3913, 180), (3914, 720), (3915, 720), (3918, 360), (3919, 360)]

theorem segOK : checkSeg 20 perms 3847 3930 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3847 3930 15390 18712440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18712440)
    (SegSum.cons (w := 360) h3847 (SegSum.cons (w := 180) h3849 (SegSum.cons (w := 360) h3851 (SegSum.cons (w := 180) h3855 (SegSum.cons (w := 360) h3858 (SegSum.cons (w := 360) h3859 (SegSum.cons (w := 360) h3860 (SegSum.cons (w := 360) h3861 (SegSum.cons (w := 720) h3862 (SegSum.cons (w := 720) h3863 (SegSum.cons (w := 720) h3864 (SegSum.cons (w := 720) h3865 (SegSum.cons (w := 720) h3866 (SegSum.cons (w := 720) h3867 (SegSum.cons (w := 720) h3868 (SegSum.cons (w := 720) h3869 (SegSum.cons (w := 720) h3870 (SegSum.cons (w := 720) h3871 (SegSum.cons (w := 180) h3894 (SegSum.cons (w := 180) h3895 (SegSum.cons (w := 360) h3896 (SegSum.cons (w := 360) h3897 (SegSum.cons (w := 720) h3898 (SegSum.cons (w := 720) h3899 (SegSum.cons (w := 360) h3902 (SegSum.cons (w := 360) h3903 (SegSum.cons (w := 90) h3912 (SegSum.cons (w := 180) h3913 (SegSum.cons (w := 720) h3914 (SegSum.cons (w := 720) h3915 (SegSum.cons (w := 360) h3918 (SegSum.cons (w := 360) h3919 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S10
