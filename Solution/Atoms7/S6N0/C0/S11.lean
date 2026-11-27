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

theorem cover3969 : P.CoversSplit 26 10 3969 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 881, 922, 930, 979, 1658, 1665]) (by decide +kernel)

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

theorem cover3982 : P.CoversSplit 26 10 3982 0xff000000000000000f0000000000000000000000000000000000000000000000fa000a00000000000a000a0000000000000000000000000000000000000000000000000000000000000000000000000000c800000000000000080000000000000000000000000000000000000000000000c80008000000000008000800000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 530, 881, 972, 1265, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c3982_0 : P.sumLeaves 26 4077568 1024 = 7168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3982) (lo := 0) (len := 1024) (W := 7168) check rows elimOK (by decide) (by decide) cover3982 (by decide)
  decide +kernel

theorem h3982 : P.leaf 36 3982 = 7168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7168)]) (.cons c3982_0 (.nil)) (by decide) (by decide))

theorem cover3983 : P.CoversSplit 26 10 3983 0xcc000000000000000c0000000000000000000000000000000000000000000000c80008000000000008000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 566, 881, 972, 1265, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c3983_0 : P.sumLeaves 26 4078592 1024 = 101528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3983) (lo := 0) (len := 1024) (W := 101528) check rows elimOK (by decide) (by decide) cover3983 (by decide)
  decide +kernel

theorem h3983 : P.leaf 36 3983 = 101528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 101528)]) (.cons c3983_0 (.nil)) (by decide) (by decide))

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
