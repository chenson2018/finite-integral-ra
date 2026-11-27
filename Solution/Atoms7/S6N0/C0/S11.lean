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

namespace RACert.S6N0.C0.S11

open RACert RACert.Problem

theorem cover3930 : P.CoversSplit 26 10 3930 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3930_0 : P.sumLeaves 26 4024320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3930) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3930 (by decide)
  decide +kernel

theorem h3930 : P.leaf 36 3930 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3930_0 (.nil)) (by decide) (by decide))

theorem cover3931 : P.CoversSplit 26 10 3931 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3931_0 : P.sumLeaves 26 4025344 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3931) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3931 (by decide)
  decide +kernel

theorem h3931 : P.leaf 36 3931 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3931_0 (.nil)) (by decide) (by decide))

theorem cover3932 : P.CoversSplit 26 10 3932 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3932_0 : P.sumLeaves 26 4026368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3932) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3932 (by decide)
  decide +kernel

theorem h3932 : P.leaf 36 3932 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3932_0 (.nil)) (by decide) (by decide))

theorem cover3933 : P.CoversSplit 26 10 3933 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3933_0 : P.sumLeaves 26 4027392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3933) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3933 (by decide)
  decide +kernel

theorem h3933 : P.leaf 36 3933 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3933_0 (.nil)) (by decide) (by decide))

theorem cover3934 : P.CoversSplit 26 10 3934 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3934_0 : P.sumLeaves 26 4028416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3934) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3934 (by decide)
  decide +kernel

theorem h3934 : P.leaf 36 3934 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3934_0 (.nil)) (by decide) (by decide))

theorem cover3935 : P.CoversSplit 26 10 3935 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3935_0 : P.sumLeaves 26 4029440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3935) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3935 (by decide)
  decide +kernel

theorem h3935 : P.leaf 36 3935 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3935_0 (.nil)) (by decide) (by decide))

theorem cover3966 : P.CoversSplit 26 10 3966 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3966_0 : P.sumLeaves 26 4061184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3966) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3966 (by decide)
  decide +kernel

theorem h3966 : P.leaf 36 3966 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3966_0 (.nil)) (by decide) (by decide))

theorem cover3967 : P.CoversSplit 26 10 3967 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3967_0 : P.sumLeaves 26 4062208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3967) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3967 (by decide)
  decide +kernel

theorem h3967 : P.leaf 36 3967 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3967_0 (.nil)) (by decide) (by decide))

theorem cover3968 : P.CoversSplit 26 10 3968 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3968_0 : P.sumLeaves 26 4063232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3968) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3968 (by decide)
  decide +kernel

theorem h3968 : P.leaf 36 3968 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3968_0 (.nil)) (by decide) (by decide))

theorem cover3969 : P.CoversSplit 26 10 3969 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 881, 922, 930, 979, 1658, 1665]) (ps := [(13, [510], [972])]) (by decide +kernel)

theorem c3969_0 : P.sumLeaves 26 4064256 1024 = 64 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3969) (lo := 0) (len := 1024) (W := 64) check rows elimOK (by decide) (by decide) cover3969 (by decide)
  decide +kernel

theorem h3969 : P.leaf 36 3969 = 64 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 64)]) (.cons c3969_0 (.nil)) (by decide) (by decide))

theorem cover3970 : P.CoversSplit 26 10 3970 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3970_0 : P.sumLeaves 26 4065280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3970) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3970 (by decide)
  decide +kernel

theorem h3970 : P.leaf 36 3970 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3970_0 (.nil)) (by decide) (by decide))

theorem cover3971 : P.CoversSplit 26 10 3971 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3971_0 : P.sumLeaves 26 4066304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3971) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3971 (by decide)
  decide +kernel

theorem h3971 : P.leaf 36 3971 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3971_0 (.nil)) (by decide) (by decide))

theorem cover3974 : P.CoversSplit 26 10 3974 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3974_0 : P.sumLeaves 26 4069376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3974) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3974 (by decide)
  decide +kernel

theorem h3974 : P.leaf 36 3974 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3974_0 (.nil)) (by decide) (by decide))

theorem cover3975 : P.CoversSplit 26 10 3975 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3975_0 : P.sumLeaves 26 4070400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3975) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3975 (by decide)
  decide +kernel

theorem h3975 : P.leaf 36 3975 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3975_0 (.nil)) (by decide) (by decide))

theorem cover3976 : P.CoversSplit 26 10 3976 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3976_0 : P.sumLeaves 26 4071424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3976) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3976 (by decide)
  decide +kernel

theorem h3976 : P.leaf 36 3976 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3976_0 (.nil)) (by decide) (by decide))

theorem cover3977 : P.CoversSplit 26 10 3977 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3977_0 : P.sumLeaves 26 4072448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3977) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3977 (by decide)
  decide +kernel

theorem h3977 : P.leaf 36 3977 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3977_0 (.nil)) (by decide) (by decide))

theorem cover3978 : P.CoversSplit 26 10 3978 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3978_0 : P.sumLeaves 26 4073472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3978) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3978 (by decide)
  decide +kernel

theorem h3978 : P.leaf 36 3978 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3978_0 (.nil)) (by decide) (by decide))

theorem cover3979 : P.CoversSplit 26 10 3979 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3979_0 : P.sumLeaves 26 4074496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3979) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3979 (by decide)
  decide +kernel

theorem h3979 : P.leaf 36 3979 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3979_0 (.nil)) (by decide) (by decide))

theorem cover3982 : P.CoversSplit 26 10 3982 0xee000000000000000e0000000000000000000000000000000000000000000000aa000a00000000000a000a0000000000000000000000000000000000000000000000000000000000000000000000000000c800000000000000080000000000000000000000000000000000000000000000880008000000000008000800000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 530, 881, 972, 1265, 1273, 1315, 1322, 1665]) (ps := [(8, [530], [538]), (13, [972], [874])]) (by decide +kernel)

theorem c3982_0 : P.sumLeaves 26 4077568 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3982) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover3982 (by decide)
  decide +kernel

theorem contract3982_1 : P.leaf 32 63722 = 0 := by
  exact leaf_contract_zero (ss := [(33, 1, 468), (3, 1, 486), (21, 13, 867), (13, 0, 874), (7, 1, 818), (18, 0, 879), (14, 0, 517), (16, 0, 465), (17, 0, 465), (8, 0, 860), (9, 1, 522), (28, 1, 530), (20, 12, 866), (12, 11, 872), (31, 1, 881)]) (q := 1209) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3982_1 : P.sumLeaves 26 4078208 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 63722) rows (by decide) (by decide)).symm.trans contract3982_1

theorem contract3982_2 : P.leaf 32 63723 = 0 := by
  exact leaf_contract_zero (ss := [(33, 1, 468), (3, 1, 486), (21, 13, 867), (13, 0, 874), (7, 1, 818), (18, 0, 879), (14, 0, 517), (16, 0, 465), (17, 0, 465), (8, 0, 860), (9, 1, 522), (28, 1, 530), (12, 1, 866), (11, 1, 872), (31, 1, 881)]) (q := 1209) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3982_2 : P.sumLeaves 26 4078272 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 63723) rows (by decide) (by decide)).symm.trans contract3982_2

theorem c3982_3 : P.sumLeaves 26 4078336 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3982) (lo := 768) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover3982 (by decide)
  decide +kernel

theorem contract3982_4 : P.leaf 32 63727 = 7168 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 63727) (ss := [(33, 1, 468), (3, 1, 486), (21, 13, 867), (13, 1, 874), (10, 1, 811), (18, 1, 879), (6, 1, 419), (8, 1, 465), (14, 1, 465), (2, 1, 409), (4, 1, 417), (5, 1, 418), (16, 1, 515), (17, 1, 516), (29, 1, 538), (31, 1, 881), (19, 1, 1259), (20, 1, 1258), (32, 1, 1265)]) (ids := [5, 9, 10, 7, 13, 20, 21, 22, 23, 24, 25, 26, 28]) (cs := [1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7, 8, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1]) (bs := [3, 10]) (W := 7168) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3982_4 : P.sumLeaves 26 4078528 64 = 7168 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 63727) rows (by decide) (by decide)).symm.trans contract3982_4

theorem h3982 : P.leaf 36 3982 = 7168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 0), (64, 0), (192, 0), (64, 7168)]) (.cons c3982_0 (.cons c3982_1 (.cons c3982_2 (.cons c3982_3 (.cons c3982_4 (.nil)))))) (by decide) (by decide))

theorem cover3983 : P.CoversSplit 26 10 3983 0xcc000000000000000c0000000000000000000000000000000000000000000000000008000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 566, 881, 972, 1265, 1273, 1315, 1322, 1665]) (ps := [(18, [879], [1315])]) (by decide +kernel)

theorem c3983_0 : P.sumLeaves 26 4078592 960 = 14232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3983) (lo := 0) (len := 960) (W := 14232) check rows elimOK (by decide) (by decide) cover3983 (by decide)
  decide +kernel

theorem contract3983_1 : P.leaf 32 63743 = 87296 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 63743) (ss := [(3, 1, 523), (33, 1, 536), (13, 1, 867), (18, 1, 879), (31, 1, 881), (29, 1, 538), (8, 1, 517), (14, 1, 860), (16, 1, 1210), (17, 1, 1217), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 7, 8, 9, 10, 13, 17, 18, 19, 20, 21, 23, 26, 28, 22, 24, 25]) (cs := [2, 1, 3, 4, 5, 6, 1, 7, 8, 9, 10, 1, 1, 11, 1, 1, 1, 12, 13, 14, 15, 16, 20, 17, 21, 22, 18, 1, 19, 1, 1, 1]) (bs := [18, 3]) (W := 87296) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3983_1 : P.sumLeaves 26 4079552 64 = 87296 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 63743) rows (by decide) (by decide)).symm.trans contract3983_1

theorem h3983 : P.leaf 36 3983 = 101528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 14232), (64, 87296)]) (.cons c3983_0 (.cons c3983_1 (.nil))) (by decide) (by decide))

theorem cover3986 : P.CoversSplit 26 10 3986 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3986_0 : P.sumLeaves 26 4081664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3986) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3986 (by decide)
  decide +kernel

theorem h3986 : P.leaf 36 3986 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3986_0 (.nil)) (by decide) (by decide))

theorem cover3987 : P.CoversSplit 26 10 3987 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3987_0 : P.sumLeaves 26 4082688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3987) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3987 (by decide)
  decide +kernel

theorem h3987 : P.leaf 36 3987 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3987_0 (.nil)) (by decide) (by decide))

theorem cover3988 : P.CoversSplit 26 10 3988 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3988_0 : P.sumLeaves 26 4083712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3988) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3988 (by decide)
  decide +kernel

theorem h3988 : P.leaf 36 3988 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3988_0 (.nil)) (by decide) (by decide))

theorem cover3989 : P.CoversSplit 26 10 3989 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3989_0 : P.sumLeaves 26 4084736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3989) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3989 (by decide)
  decide +kernel

theorem h3989 : P.leaf 36 3989 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3989_0 (.nil)) (by decide) (by decide))

theorem cover3990 : P.CoversSplit 26 10 3990 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c3990_0 : P.sumLeaves 26 4085760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3990) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3990 (by decide)
  decide +kernel

theorem h3990 : P.leaf 36 3990 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3990_0 (.nil)) (by decide) (by decide))

theorem cover3991 : P.CoversSplit 26 10 3991 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3991_0 : P.sumLeaves 26 4086784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3991) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3991 (by decide)
  decide +kernel

theorem h3991 : P.leaf 36 3991 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3991_0 (.nil)) (by decide) (by decide))

theorem cover3992 : P.CoversSplit 26 10 3992 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3992_0 : P.sumLeaves 26 4087808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3992) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3992 (by decide)
  decide +kernel

theorem h3992 : P.leaf 36 3992 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3992_0 (.nil)) (by decide) (by decide))

theorem cover3993 : P.CoversSplit 26 10 3993 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3993_0 : P.sumLeaves 26 4088832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3993) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3993 (by decide)
  decide +kernel

theorem h3993 : P.leaf 36 3993 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3993_0 (.nil)) (by decide) (by decide))

theorem cover3994 : P.CoversSplit 26 10 3994 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3994_0 : P.sumLeaves 26 4089856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3994) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3994 (by decide)
  decide +kernel

theorem h3994 : P.leaf 36 3994 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3994_0 (.nil)) (by decide) (by decide))

theorem cover3995 : P.CoversSplit 26 10 3995 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c3995_0 : P.sumLeaves 26 4090880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3995) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3995 (by decide)
  decide +kernel

theorem h3995 : P.leaf 36 3995 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3995_0 (.nil)) (by decide) (by decide))

theorem cover3996 : P.CoversSplit 26 10 3996 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3996_0 : P.sumLeaves 26 4091904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3996) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3996 (by decide)
  decide +kernel

theorem h3996 : P.leaf 36 3996 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3996_0 (.nil)) (by decide) (by decide))

theorem cover3997 : P.CoversSplit 26 10 3997 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3997_0 : P.sumLeaves 26 4092928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3997) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem h3997 : P.leaf 36 3997 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3997_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3930, 360), (3931, 360), (3932, 360), (3933, 360), (3934, 720), (3935, 720), (3966, 180), (3967, 180), (3968, 180), (3969, 180), (3970, 720), (3971, 720), (3974, 360), (3975, 360), (3976, 360), (3977, 360), (3978, 720), (3979, 720), (3982, 360), (3983, 360), (3986, 360), (3987, 360), (3988, 360), (3989, 360), (3990, 720), (3991, 720), (3992, 720), (3993, 720), (3994, 720), (3995, 720), (3996, 720), (3997, 720)]

theorem segOK : checkSeg 20 perms 3930 3998 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3930 3998 15840 39142080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 39142080)
    (SegSum.cons (w := 360) h3930 (SegSum.cons (w := 360) h3931 (SegSum.cons (w := 360) h3932 (SegSum.cons (w := 360) h3933 (SegSum.cons (w := 720) h3934 (SegSum.cons (w := 720) h3935 (SegSum.cons (w := 180) h3966 (SegSum.cons (w := 180) h3967 (SegSum.cons (w := 180) h3968 (SegSum.cons (w := 180) h3969 (SegSum.cons (w := 720) h3970 (SegSum.cons (w := 720) h3971 (SegSum.cons (w := 360) h3974 (SegSum.cons (w := 360) h3975 (SegSum.cons (w := 360) h3976 (SegSum.cons (w := 360) h3977 (SegSum.cons (w := 720) h3978 (SegSum.cons (w := 720) h3979 (SegSum.cons (w := 360) h3982 (SegSum.cons (w := 360) h3983 (SegSum.cons (w := 360) h3986 (SegSum.cons (w := 360) h3987 (SegSum.cons (w := 360) h3988 (SegSum.cons (w := 360) h3989 (SegSum.cons (w := 720) h3990 (SegSum.cons (w := 720) h3991 (SegSum.cons (w := 720) h3992 (SegSum.cons (w := 720) h3993 (SegSum.cons (w := 720) h3994 (SegSum.cons (w := 720) h3995 (SegSum.cons (w := 720) h3996 (SegSum.cons (w := 720) h3997 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S11
