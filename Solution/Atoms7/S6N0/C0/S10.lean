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

namespace RACert.S6N0.C0.S10

open RACert RACert.Problem

theorem cover3847 : P.CoversSplit 26 10 3847 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3847_0 : P.sumLeaves 26 3939328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3847) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3847 (by decide)
  decide +kernel

theorem h3847 : P.leaf 36 3847 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3847_0 (.nil)) (by decide) (by decide))

theorem cover3849 : P.CoversSplit 26 10 3849 0x8000000000000000000000000000000000000000000000000000000000000000000004000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 566, 579, 881, 922, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem c3849_0 : P.sumLeaves 26 3941376 1024 = 2512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3849) (lo := 0) (len := 1024) (W := 2512) check rows elimOK (by decide) (by decide) cover3849 (by decide)
  decide +kernel

theorem h3849 : P.leaf 36 3849 = 2512 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2512)]) (.cons c3849_0 (.nil)) (by decide) (by decide))

theorem cover3851 : P.CoversSplit 26 10 3851 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem c3851_0 : P.sumLeaves 26 3943424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3851) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3851 (by decide)
  decide +kernel

theorem h3851 : P.leaf 36 3851 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3851_0 (.nil)) (by decide) (by decide))

theorem cover3855 : P.CoversSplit 26 10 3855 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3855_0 : P.sumLeaves 26 3947520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3855) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3855 (by decide)
  decide +kernel

theorem h3855 : P.leaf 36 3855 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3855_0 (.nil)) (by decide) (by decide))

theorem cover3858 : P.CoversSplit 26 10 3858 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3858_0 : P.sumLeaves 26 3950592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3858) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3858 (by decide)
  decide +kernel

theorem h3858 : P.leaf 36 3858 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3858_0 (.nil)) (by decide) (by decide))

theorem cover3859 : P.CoversSplit 26 10 3859 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3859_0 : P.sumLeaves 26 3951616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3859) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3859 (by decide)
  decide +kernel

theorem h3859 : P.leaf 36 3859 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3859_0 (.nil)) (by decide) (by decide))

theorem cover3860 : P.CoversSplit 26 10 3860 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3860_0 : P.sumLeaves 26 3952640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3860) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3860 (by decide)
  decide +kernel

theorem h3860 : P.leaf 36 3860 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3860_0 (.nil)) (by decide) (by decide))

theorem cover3861 : P.CoversSplit 26 10 3861 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3861_0 : P.sumLeaves 26 3953664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3861) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3861 (by decide)
  decide +kernel

theorem h3861 : P.leaf 36 3861 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3861_0 (.nil)) (by decide) (by decide))

theorem cover3862 : P.CoversSplit 26 10 3862 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3862_0 : P.sumLeaves 26 3954688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3862) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3862 (by decide)
  decide +kernel

theorem h3862 : P.leaf 36 3862 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3862_0 (.nil)) (by decide) (by decide))

theorem cover3863 : P.CoversSplit 26 10 3863 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3863_0 : P.sumLeaves 26 3955712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3863) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3863 (by decide)
  decide +kernel

theorem h3863 : P.leaf 36 3863 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3863_0 (.nil)) (by decide) (by decide))

theorem cover3864 : P.CoversSplit 26 10 3864 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [480]) (by decide +kernel)

theorem c3864_0 : P.sumLeaves 26 3956736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3864) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3864 (by decide)
  decide +kernel

theorem h3864 : P.leaf 36 3864 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3864_0 (.nil)) (by decide) (by decide))

theorem cover3865 : P.CoversSplit 26 10 3865 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [480]) (by decide +kernel)

theorem c3865_0 : P.sumLeaves 26 3957760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3865) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3865 (by decide)
  decide +kernel

theorem h3865 : P.leaf 36 3865 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3865_0 (.nil)) (by decide) (by decide))

theorem cover3866 : P.CoversSplit 26 10 3866 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3866_0 : P.sumLeaves 26 3958784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3866) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3866 (by decide)
  decide +kernel

theorem h3866 : P.leaf 36 3866 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3866_0 (.nil)) (by decide) (by decide))

theorem cover3867 : P.CoversSplit 26 10 3867 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3867_0 : P.sumLeaves 26 3959808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3867) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3867 (by decide)
  decide +kernel

theorem h3867 : P.leaf 36 3867 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3867_0 (.nil)) (by decide) (by decide))

theorem cover3868 : P.CoversSplit 26 10 3868 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3868_0 : P.sumLeaves 26 3960832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3868) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3868 (by decide)
  decide +kernel

theorem h3868 : P.leaf 36 3868 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3868_0 (.nil)) (by decide) (by decide))

theorem cover3869 : P.CoversSplit 26 10 3869 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3869_0 : P.sumLeaves 26 3961856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3869) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3869 (by decide)
  decide +kernel

theorem h3869 : P.leaf 36 3869 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3869_0 (.nil)) (by decide) (by decide))

theorem cover3870 : P.CoversSplit 26 10 3870 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3870_0 : P.sumLeaves 26 3962880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3870) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3870 (by decide)
  decide +kernel

theorem h3870 : P.leaf 36 3870 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3870_0 (.nil)) (by decide) (by decide))

theorem cover3871 : P.CoversSplit 26 10 3871 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3871_0 : P.sumLeaves 26 3963904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3871) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3871 (by decide)
  decide +kernel

theorem h3871 : P.leaf 36 3871 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3871_0 (.nil)) (by decide) (by decide))

theorem cover3894 : P.CoversSplit 26 10 3894 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3894_0 : P.sumLeaves 26 3987456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3894) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3894 (by decide)
  decide +kernel

theorem h3894 : P.leaf 36 3894 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3894_0 (.nil)) (by decide) (by decide))

theorem cover3895 : P.CoversSplit 26 10 3895 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3895_0 : P.sumLeaves 26 3988480 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3895) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3895 (by decide)
  decide +kernel

theorem h3895 : P.leaf 36 3895 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3895_0 (.nil)) (by decide) (by decide))

theorem cover3896 : P.CoversSplit 26 10 3896 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c3896_0 : P.sumLeaves 26 3989504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3896) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3896 (by decide)
  decide +kernel

theorem h3896 : P.leaf 36 3896 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3896_0 (.nil)) (by decide) (by decide))

theorem cover3897 : P.CoversSplit 26 10 3897 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c3897_0 : P.sumLeaves 26 3990528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3897) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3897 (by decide)
  decide +kernel

theorem h3897 : P.leaf 36 3897 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3897_0 (.nil)) (by decide) (by decide))

theorem cover3898 : P.CoversSplit 26 10 3898 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3898_0 : P.sumLeaves 26 3991552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3898) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3898 (by decide)
  decide +kernel

theorem h3898 : P.leaf 36 3898 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3898_0 (.nil)) (by decide) (by decide))

theorem cover3899 : P.CoversSplit 26 10 3899 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3899_0 : P.sumLeaves 26 3992576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3899) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3899 (by decide)
  decide +kernel

theorem h3899 : P.leaf 36 3899 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3899_0 (.nil)) (by decide) (by decide))

theorem cover3902 : P.CoversSplit 26 10 3902 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3902_0 : P.sumLeaves 26 3995648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3902) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3902 (by decide)
  decide +kernel

theorem h3902 : P.leaf 36 3902 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3902_0 (.nil)) (by decide) (by decide))

theorem cover3903 : P.CoversSplit 26 10 3903 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3903_0 : P.sumLeaves 26 3996672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3903) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3903 (by decide)
  decide +kernel

theorem h3903 : P.leaf 36 3903 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3903_0 (.nil)) (by decide) (by decide))

theorem cover3912 : P.CoversSplit 26 10 3912 0xa0a00000a0a000000000000000000000a0a00000a000000000000000000000005050050550500500000005050000050050500505500005000000000000000000a0a00000a00000000000000000000000000000000000000000000000000000005050050550000500000005050000050000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 922, 930, 972, 979, 1265, 1665]) (by decide +kernel)

theorem c3912_0 : P.sumLeaves 26 4005888 1024 = 36780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3912) (lo := 0) (len := 1024) (W := 36780) check rows elimOK (by decide) (by decide) cover3912 (by decide)
  decide +kernel

theorem h3912 : P.leaf 36 3912 = 36780 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 36780)]) (.cons c3912_0 (.nil)) (by decide) (by decide))

theorem cover3913 : P.CoversSplit 26 10 3913 0xa0a00000a0a000000000000000000000a0a00000a000000000000000000000000000050500000500000005050000050000000505000005000000000000000000a0a00000a00000000000000000000000000000000000000000000000000000000000050500000500000005050000050000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 922, 930, 972, 979, 1665]) (by decide +kernel)

theorem c3913_0 : P.sumLeaves 26 4006912 1024 = 83056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3913) (lo := 0) (len := 1024) (W := 83056) check rows elimOK (by decide) (by decide) cover3913 (by decide)
  decide +kernel

theorem h3913 : P.leaf 36 3913 = 83056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 83056)]) (.cons c3913_0 (.nil)) (by decide) (by decide))

theorem cover3914 : P.CoversSplit 26 10 3914 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem c3914_0 : P.sumLeaves 26 4007936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3914) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3914 (by decide)
  decide +kernel

theorem h3914 : P.leaf 36 3914 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3914_0 (.nil)) (by decide) (by decide))

theorem cover3915 : P.CoversSplit 26 10 3915 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [529]) (by decide +kernel)

theorem c3915_0 : P.sumLeaves 26 4008960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3915) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3915 (by decide)
  decide +kernel

theorem h3915 : P.leaf 36 3915 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3915_0 (.nil)) (by decide) (by decide))

theorem cover3918 : P.CoversSplit 26 10 3918 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3918_0 : P.sumLeaves 26 4012032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3918) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3918 (by decide)
  decide +kernel

theorem h3918 : P.leaf 36 3918 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3918_0 (.nil)) (by decide) (by decide))

theorem cover3919 : P.CoversSplit 26 10 3919 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem c3919_0 : P.sumLeaves 26 4013056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3919) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3919 (by decide)
  decide +kernel

theorem h3919 : P.leaf 36 3919 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3919_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3847, 360), (3849, 180), (3851, 360), (3855, 180), (3858, 360), (3859, 360), (3860, 360), (3861, 360), (3862, 720), (3863, 720), (3864, 720), (3865, 720), (3866, 720), (3867, 720), (3868, 720), (3869, 720), (3870, 720), (3871, 720), (3894, 180), (3895, 180), (3896, 360), (3897, 360), (3898, 720), (3899, 720), (3902, 360), (3903, 360), (3912, 90), (3913, 180), (3914, 720), (3915, 720), (3918, 360), (3919, 360)]

theorem segOK : checkSeg 20 perms 3847 3930 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3847 3930 15390 18712440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18712440)
    (SegSum.cons (w := 360) h3847 (SegSum.cons (w := 180) h3849 (SegSum.cons (w := 360) h3851 (SegSum.cons (w := 180) h3855 (SegSum.cons (w := 360) h3858 (SegSum.cons (w := 360) h3859 (SegSum.cons (w := 360) h3860 (SegSum.cons (w := 360) h3861 (SegSum.cons (w := 720) h3862 (SegSum.cons (w := 720) h3863 (SegSum.cons (w := 720) h3864 (SegSum.cons (w := 720) h3865 (SegSum.cons (w := 720) h3866 (SegSum.cons (w := 720) h3867 (SegSum.cons (w := 720) h3868 (SegSum.cons (w := 720) h3869 (SegSum.cons (w := 720) h3870 (SegSum.cons (w := 720) h3871 (SegSum.cons (w := 180) h3894 (SegSum.cons (w := 180) h3895 (SegSum.cons (w := 360) h3896 (SegSum.cons (w := 360) h3897 (SegSum.cons (w := 720) h3898 (SegSum.cons (w := 720) h3899 (SegSum.cons (w := 360) h3902 (SegSum.cons (w := 360) h3903 (SegSum.cons (w := 90) h3912 (SegSum.cons (w := 180) h3913 (SegSum.cons (w := 720) h3914 (SegSum.cons (w := 720) h3915 (SegSum.cons (w := 360) h3918 (SegSum.cons (w := 360) h3919 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S10
