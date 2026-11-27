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

namespace RACert.S6N0.C0.S12

open RACert RACert.Problem

theorem cover3998 : P.CoversSplit 26 10 3998 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c3998_0 : P.sumLeaves 26 4093952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3998) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3998 (by decide)
  decide +kernel

theorem h3998 : P.leaf 36 3998 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3998_0 (.nil)) (by decide) (by decide))

theorem cover3999 : P.CoversSplit 26 10 3999 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c3999_0 : P.sumLeaves 26 4094976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3999) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem h3999 : P.leaf 36 3999 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3999_0 (.nil)) (by decide) (by decide))

theorem cover4022 : P.CoversSplit 26 10 4022 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [468]) (by decide +kernel)

theorem c4022_0 : P.sumLeaves 26 4118528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4022) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4022 (by decide)
  decide +kernel

theorem h4022 : P.leaf 36 4022 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4022_0 (.nil)) (by decide) (by decide))

theorem cover4023 : P.CoversSplit 26 10 4023 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4023_0 : P.sumLeaves 26 4119552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4023) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4023 (by decide)
  decide +kernel

theorem h4023 : P.leaf 36 4023 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4023_0 (.nil)) (by decide) (by decide))

theorem cover4024 : P.CoversSplit 26 10 4024 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4024_0 : P.sumLeaves 26 4120576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4024) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4024 (by decide)
  decide +kernel

theorem h4024 : P.leaf 36 4024 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4024_0 (.nil)) (by decide) (by decide))

theorem cover4025 : P.CoversSplit 26 10 4025 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4025_0 : P.sumLeaves 26 4121600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4025) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4025 (by decide)
  decide +kernel

theorem h4025 : P.leaf 36 4025 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4025_0 (.nil)) (by decide) (by decide))

theorem cover4026 : P.CoversSplit 26 10 4026 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c4026_0 : P.sumLeaves 26 4122624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4026) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4026 (by decide)
  decide +kernel

theorem h4026 : P.leaf 36 4026 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4026_0 (.nil)) (by decide) (by decide))

theorem cover4027 : P.CoversSplit 26 10 4027 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c4027_0 : P.sumLeaves 26 4123648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4027) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4027 (by decide)
  decide +kernel

theorem h4027 : P.leaf 36 4027 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4027_0 (.nil)) (by decide) (by decide))

theorem cover4030 : P.CoversSplit 26 10 4030 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c4030_0 : P.sumLeaves 26 4126720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4030) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4030 (by decide)
  decide +kernel

theorem h4030 : P.leaf 36 4030 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4030_0 (.nil)) (by decide) (by decide))

theorem cover4031 : P.CoversSplit 26 10 4031 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c4031_0 : P.sumLeaves 26 4127744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4031) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4031 (by decide)
  decide +kernel

theorem h4031 : P.leaf 36 4031 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4031_0 (.nil)) (by decide) (by decide))

theorem cover4040 : P.CoversSplit 26 10 4040 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4040_0 : P.sumLeaves 26 4136960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4040) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4040 (by decide)
  decide +kernel

theorem h4040 : P.leaf 36 4040 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4040_0 (.nil)) (by decide) (by decide))

theorem cover4041 : P.CoversSplit 26 10 4041 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4041_0 : P.sumLeaves 26 4137984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4041) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4041 (by decide)
  decide +kernel

theorem h4041 : P.leaf 36 4041 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4041_0 (.nil)) (by decide) (by decide))

theorem cover4042 : P.CoversSplit 26 10 4042 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c4042_0 : P.sumLeaves 26 4139008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4042) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4042 (by decide)
  decide +kernel

theorem h4042 : P.leaf 36 4042 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4042_0 (.nil)) (by decide) (by decide))

theorem cover4043 : P.CoversSplit 26 10 4043 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c4043_0 : P.sumLeaves 26 4140032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4043) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4043 (by decide)
  decide +kernel

theorem h4043 : P.leaf 36 4043 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4043_0 (.nil)) (by decide) (by decide))

theorem cover4046 : P.CoversSplit 26 10 4046 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c4046_0 : P.sumLeaves 26 4143104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4046) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4046 (by decide)
  decide +kernel

theorem h4046 : P.leaf 36 4046 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4046_0 (.nil)) (by decide) (by decide))

theorem cover4047 : P.CoversSplit 26 10 4047 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c4047_0 : P.sumLeaves 26 4144128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4047) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4047 (by decide)
  decide +kernel

theorem h4047 : P.leaf 36 4047 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4047_0 (.nil)) (by decide) (by decide))

theorem cover4058 : P.CoversSplit 26 10 4058 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c4058_0 : P.sumLeaves 26 4155392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4058) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4058 (by decide)
  decide +kernel

theorem h4058 : P.leaf 36 4058 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4058_0 (.nil)) (by decide) (by decide))

theorem cover4059 : P.CoversSplit 26 10 4059 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c4059_0 : P.sumLeaves 26 4156416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4059) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4059 (by decide)
  decide +kernel

theorem h4059 : P.leaf 36 4059 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4059_0 (.nil)) (by decide) (by decide))

theorem cover4060 : P.CoversSplit 26 10 4060 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4060_0 : P.sumLeaves 26 4157440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4060) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4060 (by decide)
  decide +kernel

theorem h4060 : P.leaf 36 4060 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4060_0 (.nil)) (by decide) (by decide))

theorem cover4061 : P.CoversSplit 26 10 4061 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c4061_0 : P.sumLeaves 26 4158464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4061) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4061 (by decide)
  decide +kernel

theorem h4061 : P.leaf 36 4061 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4061_0 (.nil)) (by decide) (by decide))

theorem cover4062 : P.CoversSplit 26 10 4062 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c4062_0 : P.sumLeaves 26 4159488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4062) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4062 (by decide)
  decide +kernel

theorem h4062 : P.leaf 36 4062 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4062_0 (.nil)) (by decide) (by decide))

theorem cover4063 : P.CoversSplit 26 10 4063 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c4063_0 : P.sumLeaves 26 4160512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4063) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover4063 (by decide)
  decide +kernel

theorem h4063 : P.leaf 36 4063 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c4063_0 (.nil)) (by decide) (by decide))

theorem cover4094 : P.CoversSplit 26 10 4094 0xfffafffafff8aa88fffafafafff8aa88fffafffaffc8aa8888888888888888880000000000000000000000000000000000000000000000000000000000000000fffafffaffc8aa88fffafafaffc8aa88ccc8ccc8cc00880088888888880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 881, 922, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c4094_0 : P.sumLeaves 26 4192256 486 = 6809412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4094) (lo := 0) (len := 486) (W := 6809412) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_1 : P.sumLeaves 26 4192742 434 = 11850052 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4094) (lo := 486) (len := 434) (W := 11850052) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_2 : P.sumLeaves 26 4193176 104 = 14059568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4094) (lo := 920) (len := 104) (W := 14059568) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem h4094 : P.leaf 36 4094 = 32719032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(486, 6809412), (434, 11850052), (104, 14059568)]) (.cons c4094_0 (.cons c4094_1 (.cons c4094_2 (.nil)))) (by decide) (by decide))

theorem cover4095 : P.CoversSplit 26 10 4095 0xfffafffafff8aa88fffafafafff8aa88fffafffaffc8aa888888888888888888fafaaaaafaf8aa88aaaaaaaaaaa8aa88fafaaaaafac8aa888888888888888888fffafffaffc8aa88fffafafaffc8aa88ccc8ccc8ccc888888888888888888888fafaaaaafac8aa88aaaaaaaaaa88aa88c8c88888c8c888888888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 922, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c4095_0 : P.sumLeaves 26 4193280 253 = 9240832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4095) (lo := 0) (len := 253) (W := 9240832) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_1 : P.sumLeaves 26 4193533 219 = 114844512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4095) (lo := 253) (len := 219) (W := 114844512) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_2 : P.sumLeaves 26 4193752 193 = 161229316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4095) (lo := 472) (len := 193) (W := 161229316) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_3 : P.sumLeaves 26 4193945 207 = 180820762 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4095) (lo := 665) (len := 207) (W := 180820762) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_4 : P.sumLeaves 26 4194152 132 = 189577928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4095) (lo := 872) (len := 132) (W := 189577928) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_5 : P.sumLeaves 26 4194284 20 = 95312780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 4095) (lo := 1004) (len := 20) (W := 95312780) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem h4095 : P.leaf 36 4095 = 751026130 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(253, 9240832), (219, 114844512), (193, 161229316), (207, 180820762), (132, 189577928), (20, 95312780)]) (.cons c4095_0 (.cons c4095_1 (.cons c4095_2 (.cons c4095_3 (.cons c4095_4 (.cons c4095_5 (.nil))))))) (by decide) (by decide))

theorem cover7294 : P.CoversSplit 26 10 7294 0x8000000000000001000000000000000000000000000000000000000000000001000004000000000100000400000000010000000000000000000000000000000100000000002000010000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c7294_0 : P.sumLeaves 26 7469056 1024 = 257784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7294) (lo := 0) (len := 1024) (W := 257784) check rows elimOK (by decide) (by decide) cover7294 (by decide)
  decide +kernel

theorem h7294 : P.leaf 36 7294 = 257784 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 257784)]) (.cons c7294_0 (.nil)) (by decide) (by decide))

theorem cover7295 : P.CoversSplit 26 10 7295 0x8000000000000001000000000000000000000000000000000000000000000001000004000000000100000400000000010000000000000000000000000000000100000000002000010000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c7295_0 : P.sumLeaves 26 7470080 1024 = 530568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7295) (lo := 0) (len := 1024) (W := 530568) check rows elimOK (by decide) (by decide) cover7295 (by decide)
  decide +kernel

theorem h7295 : P.leaf 36 7295 = 530568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 530568)]) (.cons c7295_0 (.nil)) (by decide) (by decide))

theorem cover7350 : P.CoversSplit 26 10 7350 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000300000000003000020000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [488, 489, 538, 587, 629, 636, 922, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c7350_0 : P.sumLeaves 26 7526400 1024 = 21106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7350) (lo := 0) (len := 1024) (W := 21106) check rows elimOK (by decide) (by decide) cover7350 (by decide)
  decide +kernel

theorem h7350 : P.leaf 36 7350 = 21106 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21106)]) (.cons c7350_0 (.nil)) (by decide) (by decide))

theorem cover7351 : P.CoversSplit 26 10 7351 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000300000000003000020000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [488, 489, 538, 587, 629, 636, 922, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c7351_0 : P.sumLeaves 26 7527424 1024 = 36401 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7351) (lo := 0) (len := 1024) (W := 36401) check rows elimOK (by decide) (by decide) cover7351 (by decide)
  decide +kernel

theorem h7351 : P.leaf 36 7351 = 36401 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 36401)]) (.cons c7351_0 (.nil)) (by decide) (by decide))

theorem cover7352 : P.CoversSplit 26 10 7352 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7352_0 : P.sumLeaves 26 7528448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7352) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7352 (by decide)
  decide +kernel

theorem h7352 : P.leaf 36 7352 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7352_0 (.nil)) (by decide) (by decide))

theorem cover7353 : P.CoversSplit 26 10 7353 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7353_0 : P.sumLeaves 26 7529472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7353) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7353 (by decide)
  decide +kernel

theorem h7353 : P.leaf 36 7353 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7353_0 (.nil)) (by decide) (by decide))

theorem cover7354 : P.CoversSplit 26 10 7354 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7354_0 : P.sumLeaves 26 7530496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7354) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7354 (by decide)
  decide +kernel

theorem h7354 : P.leaf 36 7354 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7354_0 (.nil)) (by decide) (by decide))

theorem cover7355 : P.CoversSplit 26 10 7355 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7355_0 : P.sumLeaves 26 7531520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7355) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7355 (by decide)
  decide +kernel

theorem h7355 : P.leaf 36 7355 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7355_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3998, 720), (3999, 720), (4022, 180), (4023, 180), (4024, 360), (4025, 360), (4026, 720), (4027, 720), (4030, 360), (4031, 360), (4040, 180), (4041, 180), (4042, 720), (4043, 720), (4046, 360), (4047, 360), (4058, 360), (4059, 360), (4060, 360), (4061, 360), (4062, 720), (4063, 720), (4094, 180), (4095, 180), (7294, 20), (7295, 20), (7350, 180), (7351, 180), (7352, 360), (7353, 360), (7354, 720), (7355, 720)]

theorem segOK : checkSeg 20 perms 3998 7358 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 3998 7358 13000 141100247460 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 141100247460)
    (SegSum.cons (w := 720) h3998 (SegSum.cons (w := 720) h3999 (SegSum.cons (w := 180) h4022 (SegSum.cons (w := 180) h4023 (SegSum.cons (w := 360) h4024 (SegSum.cons (w := 360) h4025 (SegSum.cons (w := 720) h4026 (SegSum.cons (w := 720) h4027 (SegSum.cons (w := 360) h4030 (SegSum.cons (w := 360) h4031 (SegSum.cons (w := 180) h4040 (SegSum.cons (w := 180) h4041 (SegSum.cons (w := 720) h4042 (SegSum.cons (w := 720) h4043 (SegSum.cons (w := 360) h4046 (SegSum.cons (w := 360) h4047 (SegSum.cons (w := 360) h4058 (SegSum.cons (w := 360) h4059 (SegSum.cons (w := 360) h4060 (SegSum.cons (w := 360) h4061 (SegSum.cons (w := 720) h4062 (SegSum.cons (w := 720) h4063 (SegSum.cons (w := 180) h4094 (SegSum.cons (w := 180) h4095 (SegSum.cons (w := 20) h7294 (SegSum.cons (w := 20) h7295 (SegSum.cons (w := 180) h7350 (SegSum.cons (w := 180) h7351 (SegSum.cons (w := 360) h7352 (SegSum.cons (w := 360) h7353 (SegSum.cons (w := 720) h7354 (SegSum.cons (w := 720) h7355 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S12
