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

theorem c3912_0 : P.sumLeaves 26 4005888 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3912) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3912 (by decide)
  decide +kernel

theorem contract3912_1 : P.leaf 32 62594 = 752 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 62594) (ss := [(4, 1, 425), (20, 1, 425), (9, 7, 466), (28, 7, 467), (8, 7, 472), (2, 1, 482), (3, 1, 531), (7, 0, 579), (13, 0, 458), (18, 0, 465), (21, 0, 473), (11, 1, 817), (30, 0, 922), (32, 0, 922), (26, 5, 629), (16, 1, 1209)]) (ids := [3, 4, 8, 10, 12, 13, 15, 17, 20, 21, 22, 25, 27, 29, 31, 23]) (cs := [1, 1, 1, 2, 3, 0, 0, 0, 4, 1, 5, 0, 6, 7, 1, 8, 0, 9, 1, 0, 10, 11, 12, 17, 2, 13, 0, 14, 0, 15, 0, 16]) (bs := [15, 1]) (W := 752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3912_1 : P.sumLeaves 26 4006016 64 = 752 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62594) rows (by decide) (by decide)).symm.trans contract3912_1

theorem contract3912_2 : P.leaf 32 62595 = 3888 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 62595) (ss := [(9, 7, 466), (28, 7, 467), (8, 7, 472), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (21, 13, 867), (13, 0, 874), (7, 0, 811), (18, 0, 465), (20, 1, 1665)]) (ids := [4, 8, 9, 10, 12, 13, 14, 15, 17, 20, 21, 22, 25, 27, 28, 29, 30, 31, 23, 24]) (cs := [1, 1, 1, 1, 2, 0, 0, 0, 3, 4, 5, 0, 6, 7, 8, 9, 0, 10, 1, 0, 11, 12, 13, 20, 21, 14, 0, 15, 16, 17, 18, 19]) (bs := [18, 2]) (W := 3888) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3912_2 : P.sumLeaves 26 4006080 64 = 3888 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62595) rows (by decide) (by decide)).symm.trans contract3912_2

theorem c3912_3 : P.sumLeaves 26 4006144 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3912) (lo := 256) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover3912 (by decide)
  decide +kernel

theorem contract3912_4 : P.leaf 32 62599 = 640 := by
  exact leaf_contract_factors (k := 32) (b := 11) (H := 62599) (ss := [(9, 7, 466), (28, 7, 467), (8, 7, 472), (7, 1, 481), (30, 1, 481), (2, 1, 482), (14, 1, 465), (15, 1, 473), (32, 1, 530), (3, 1, 531), (10, 1, 458), (19, 1, 522), (4, 1, 580), (11, 1, 459), (16, 1, 515), (13, 1, 811), (12, 1, 460), (18, 1, 860), (17, 1, 516), (21, 1, 867), (20, 1, 572)]) (ids := [3, 20, 25, 27, 29, 31, 4, 21, 22, 23, 24]) (cs := [1, 1, 1, 2, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 10, 11, 12, 4, 1, 5, 1, 6, 1, 7]) (bs := [6, 5]) (W := 640) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3912_4 : P.sumLeaves 26 4006336 64 = 640 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62599) rows (by decide) (by decide)).symm.trans contract3912_4

theorem c3912_5 : P.sumLeaves 26 4006400 128 = 4640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3912) (lo := 512) (len := 128) (W := 4640) check rows elimOK (by decide) (by decide) cover3912 (by decide)
  decide +kernel

theorem contract3912_6 : P.leaf 32 62602 = 2132 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 62602) (ss := [(4, 1, 425), (20, 1, 425), (9, 7, 466), (28, 7, 467), (8, 7, 472), (7, 0, 579), (13, 0, 458), (18, 0, 465), (21, 0, 473), (11, 1, 817), (30, 0, 922), (32, 0, 922), (26, 1, 629), (16, 1, 1209)]) (ids := [0, 1, 3, 4, 8, 10, 12, 13, 15, 17, 20, 21, 22, 25, 27, 29, 31, 23]) (cs := [2, 3, 1, 4, 5, 0, 0, 0, 6, 1, 7, 0, 8, 9, 1, 10, 0, 11, 1, 0, 12, 13, 14, 19, 1, 15, 0, 16, 0, 17, 0, 18]) (bs := [17, 1]) (W := 2132) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3912_6 : P.sumLeaves 26 4006528 64 = 2132 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62602) rows (by decide) (by decide)).symm.trans contract3912_6

theorem c3912_7 : P.sumLeaves 26 4006592 128 = 21400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3912) (lo := 704) (len := 128) (W := 21400) check rows elimOK (by decide) (by decide) cover3912 (by decide)
  decide +kernel

theorem contract3912_8 : P.leaf 32 62605 = 640 := by
  exact leaf_contract_factors (k := 32) (b := 11) (H := 62605) (ss := [(9, 7, 466), (28, 7, 467), (8, 7, 472), (2, 1, 475), (7, 1, 481), (14, 1, 465), (15, 1, 473), (30, 1, 481), (3, 1, 524), (10, 1, 458), (19, 1, 522), (32, 1, 530), (5, 1, 586), (12, 1, 460), (17, 1, 516), (20, 1, 572), (13, 1, 811), (11, 1, 459), (18, 1, 860), (16, 1, 515), (21, 1, 867)]) (ids := [2, 20, 25, 27, 29, 31, 4, 21, 22, 23, 24]) (cs := [1, 1, 2, 1, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 10, 11, 12, 4, 1, 5, 1, 6, 1, 7]) (bs := [6, 5]) (W := 640) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3912_8 : P.sumLeaves 26 4006720 64 = 640 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62605) rows (by decide) (by decide)).symm.trans contract3912_8

theorem c3912_9 : P.sumLeaves 26 4006784 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3912) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover3912 (by decide)
  decide +kernel

theorem contract3912_10 : P.leaf 32 62607 = 2688 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 62607) (ss := [(9, 7, 466), (28, 7, 467), (8, 7, 472), (7, 1, 481), (30, 1, 481), (32, 1, 530), (10, 1, 811), (13, 1, 811), (11, 1, 459), (12, 1, 460), (14, 1, 860), (18, 1, 860), (16, 1, 515), (17, 1, 516), (21, 1, 867), (15, 1, 473), (19, 1, 522), (20, 1, 572)]) (ids := [0, 1, 2, 3, 4, 20, 25, 27, 29, 31, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 12, 13, 14, 15, 8, 1, 9, 1, 10, 1, 11]) (bs := [10, 4]) (W := 2688) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3912_10 : P.sumLeaves 26 4006848 64 = 2688 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62607) rows (by decide) (by decide)).symm.trans contract3912_10

theorem h3912 : P.leaf 36 3912 = 36780 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 752), (64, 3888), (192, 0), (64, 640), (128, 4640), (64, 2132), (128, 21400), (64, 640), (64, 0), (64, 2688)]) (.cons c3912_0 (.cons c3912_1 (.cons c3912_2 (.cons c3912_3 (.cons c3912_4 (.cons c3912_5 (.cons c3912_6 (.cons c3912_7 (.cons c3912_8 (.cons c3912_9 (.cons c3912_10 (.nil)))))))))))) (by decide) (by decide))

theorem cover3913 : P.CoversSplit 26 10 3913 0xa0a00000a0a000000000000000000000a0a00000a000000000000000000000000000050500000500000005050000050000000505000005000000000000000000a0a00000a00000000000000000000000000000000000000000000000000000000000050500000500000005050000050000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 922, 930, 972, 979, 1665]) (by decide +kernel)

theorem c3913_0 : P.sumLeaves 26 4006912 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3913) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover3913 (by decide)
  decide +kernel

theorem contract3913_1 : P.leaf 32 62610 = 752 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 62610) (ss := [(4, 1, 425), (20, 1, 425), (2, 1, 482), (3, 1, 531), (28, 0, 579), (32, 0, 481), (30, 0, 530), (26, 5, 629), (11, 1, 817), (13, 1, 867), (12, 7, 825), (18, 1, 879), (16, 1, 1209), (17, 8, 1217), (21, 9, 1609)]) (ids := [3, 4, 5, 6, 7, 8, 12, 13, 17, 20, 21, 22, 25, 27, 29, 31, 23]) (cs := [1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 4, 1, 8, 9, 1, 5, 1, 10, 1, 6, 11, 12, 13, 18, 2, 14, 0, 15, 0, 16, 0, 17]) (bs := [16, 1]) (W := 752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3913_1 : P.sumLeaves 26 4007040 64 = 752 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62610) rows (by decide) (by decide)).symm.trans contract3913_1

theorem contract3913_2 : P.leaf 32 62611 = 688 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 62611) (ss := [(2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (13, 1, 867), (11, 1, 818), (12, 7, 825), (18, 1, 879), (28, 0, 972), (32, 0, 481), (30, 0, 530), (9, 0, 579), (19, 0, 473), (21, 0, 473), (15, 0, 522), (16, 1, 1210), (17, 8, 1217), (20, 1, 1665)]) (ids := [4, 5, 6, 8, 12, 20, 21, 22, 25, 27, 29, 31, 23, 24]) (cs := [1, 1, 1, 1, 2, 3, 4, 0, 5, 1, 3, 1, 6, 0, 1, 4, 1, 0, 1, 0, 7, 8, 9, 14, 15, 10, 0, 11, 0, 12, 0, 13]) (bs := [12, 2]) (W := 688) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3913_2 : P.sumLeaves 26 4007104 64 = 688 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62611) rows (by decide) (by decide)).symm.trans contract3913_2

theorem c3913_3 : P.sumLeaves 26 4007168 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3913) (lo := 256) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover3913 (by decide)
  decide +kernel

theorem contract3913_4 : P.leaf 32 62615 = 11392 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 62615) (ss := [(28, 1, 481), (30, 1, 481), (2, 1, 482), (32, 1, 530), (3, 1, 531), (4, 1, 580), (13, 1, 867), (11, 1, 818), (18, 1, 879), (16, 1, 1210), (20, 1, 1665), (9, 1, 572), (15, 1, 473), (19, 1, 522), (21, 1, 916)]) (ids := [3, 5, 6, 8, 10, 12, 15, 20, 21, 22, 25, 27, 29, 31, 4, 23, 24]) (cs := [1, 1, 1, 2, 16, 3, 4, 1, 5, 1, 6, 1, 7, 1, 1, 8, 1, 1, 1, 1, 9, 10, 11, 17, 18, 12, 1, 13, 1, 14, 1, 15]) (bs := [14, 3]) (W := 11392) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3913_4 : P.sumLeaves 26 4007360 64 = 11392 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62615) rows (by decide) (by decide)).symm.trans contract3913_4

theorem c3913_5 : P.sumLeaves 26 4007424 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3913) (lo := 512) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover3913 (by decide)
  decide +kernel

theorem contract3913_6 : P.leaf 32 62617 = 1064 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 62617) (ss := [(2, 1, 475), (3, 1, 524), (5, 1, 586), (13, 1, 867), (12, 1, 825), (18, 1, 879), (28, 0, 972), (32, 0, 481), (30, 0, 530), (9, 0, 579), (19, 0, 473), (21, 0, 473), (15, 0, 522), (11, 7, 818), (16, 8, 1210), (17, 1, 1217)]) (ids := [2, 4, 5, 6, 8, 12, 18, 20, 21, 22, 23, 25, 27, 29, 31, 24]) (cs := [1, 1, 2, 1, 3, 4, 5, 0, 6, 4, 1, 1, 7, 0, 5, 1, 1, 0, 8, 0, 9, 10, 11, 12, 17, 13, 0, 14, 0, 15, 0, 16]) (bs := [15, 1]) (W := 1064) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3913_6 : P.sumLeaves 26 4007488 64 = 1064 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62617) rows (by decide) (by decide)).symm.trans contract3913_6

theorem contract3913_7 : P.leaf 32 62618 = 7056 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 62618) (ss := [(4, 1, 425), (20, 1, 425), (28, 0, 579), (32, 0, 481), (30, 0, 530), (26, 1, 629), (11, 1, 817), (13, 1, 867), (12, 1, 825), (5, 1, 509), (18, 1, 879), (16, 1, 1209), (17, 1, 1217)]) (ids := [0, 1, 4, 5, 6, 7, 8, 12, 13, 17, 19, 20, 21, 22, 25, 27, 29, 31, 23]) (cs := [2, 3, 1, 1, 4, 5, 6, 7, 8, 1, 1, 1, 9, 10, 1, 1, 1, 11, 1, 12, 13, 14, 15, 20, 1, 16, 0, 17, 0, 18, 0, 19]) (bs := [18, 1]) (W := 7056) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3913_7 : P.sumLeaves 26 4007552 64 = 7056 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62618) rows (by decide) (by decide)).symm.trans contract3913_7

theorem contract3913_8 : P.leaf 32 62619 = 10584 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 62619) (ss := [(13, 1, 867), (11, 1, 818), (12, 1, 825), (18, 1, 879), (28, 0, 972), (32, 0, 481), (5, 1, 509), (30, 0, 530), (9, 0, 579), (19, 0, 473), (21, 0, 473), (4, 1, 508), (15, 0, 522), (16, 1, 1210), (17, 1, 1217)]) (ids := [0, 1, 4, 5, 6, 8, 12, 20, 21, 22, 25, 27, 29, 31, 18, 23, 24]) (cs := [2, 3, 1, 1, 4, 5, 6, 0, 7, 1, 1, 1, 8, 0, 1, 1, 1, 0, 16, 0, 9, 10, 11, 17, 18, 12, 0, 13, 0, 14, 0, 15]) (bs := [14, 2, 1]) (W := 10584) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3913_8 : P.sumLeaves 26 4007616 64 = 10584 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 62619) rows (by decide) (by decide)).symm.trans contract3913_8

theorem c3913_9 : P.sumLeaves 26 4007680 256 = 51520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3913) (lo := 768) (len := 256) (W := 51520) check rows elimOK (by decide) (by decide) cover3913 (by decide)
  decide +kernel

theorem h3913 : P.leaf 36 3913 = 83056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 752), (64, 688), (192, 0), (64, 11392), (64, 0), (64, 1064), (64, 7056), (64, 10584), (256, 51520)]) (.cons c3913_0 (.cons c3913_1 (.cons c3913_2 (.cons c3913_3 (.cons c3913_4 (.cons c3913_5 (.cons c3913_6 (.cons c3913_7 (.cons c3913_8 (.cons c3913_9 (.nil))))))))))) (by decide) (by decide))

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
