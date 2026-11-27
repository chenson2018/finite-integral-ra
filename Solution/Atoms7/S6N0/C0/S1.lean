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

namespace RACert.S6N0.C0.S1

open RACert RACert.Problem

theorem cover511 : P.CoversSplit 26 10 511 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c511_0 : P.sumLeaves 26 523264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 511) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem h511 : P.leaf 36 511 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c511_0 (.nil)) (by decide) (by decide))

theorem cover1023 : P.CoversSplit 26 10 1023 0xfff8faf8ffc88888faf8aaa8fac88888ffc8fac8ccc888888888888888888888faf8aaa8fac88888aaa8aaa8aa888888fac8aa88c8c888888888888888888888ffc8fac8ccc88888fac8aa88c8c88888ccc8c8c8ccc888888888888888888888fac8aa88c8c88888aa88aa8888888888c8c88888c8c888888888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 922, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f1023 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (1047552 + i)

theorem c1023_0 : rowSum f1023 0 423 = 51053231 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem c1023_1 : rowSum f1023 423 565 = 105905016 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem c1023_2 : rowSum f1023 988 36 = 23566924 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem sum1023 : rowSum f1023 0 1024 = 180525171 :=
  rowSum_append (F := f1023) (lo := 0) (n := 423) (m := 601) (A := 51053231) (B := 129471940) c1023_0 (rowSum_append (F := f1023) (lo := 423) (n := 565) (m := 36) (A := 105905016) (B := 23566924) c1023_1 (c1023_2))

theorem h1023 : P.leaf 36 1023 = 180525171 :=
  leaf_weighted (k := 26) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1023) (by decide) (by decide +kernel)) sum1023

theorem cover1043 : P.CoversSplit 26 10 1043 0x8000000000000000000000000000000000000000000000000000000000000001800000000000000000000400000000000000000000000000000000000000000180000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

noncomputable def f1043 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (1068032 + i)

theorem c1043_0 : rowSum f1043 0 1024 = 749280 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1043) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1043 (by decide)
  decide +kernel

theorem sum1043 : rowSum f1043 0 1024 = 749280 :=
  c1043_0

theorem h1043 : P.leaf 36 1043 = 749280 :=
  leaf_weighted (k := 26) (d := 10) (H := 1043) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1043) (by decide) (by decide +kernel)) sum1043

theorem cover1044 : P.CoversSplit 26 10 1044 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 972, 979, 1265, 1273, 2008]) (by decide +kernel)

theorem c1044_0 : P.sumLeaves 26 1069056 1024 = 1412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1044) (lo := 0) (len := 1024) (W := 1412) check rows elimOK (by decide) (by decide) cover1044 (by decide)
  decide +kernel

theorem h1044 : P.leaf 36 1044 = 1412 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1412)]) (.cons c1044_0 (.nil)) (by decide) (by decide))

theorem cover1045 : P.CoversSplit 26 10 1045 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem c1045_0 : P.sumLeaves 26 1070080 1024 = 4080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1045) (lo := 0) (len := 1024) (W := 4080) check rows elimOK (by decide) (by decide) cover1045 (by decide)
  decide +kernel

theorem h1045 : P.leaf 36 1045 = 4080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4080)]) (.cons c1045_0 (.nil)) (by decide) (by decide))

theorem cover1047 : P.CoversSplit 26 10 1047 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem c1047_0 : P.sumLeaves 26 1072128 1024 = 11040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1047) (lo := 0) (len := 1024) (W := 11040) check rows elimOK (by decide) (by decide) cover1047 (by decide)
  decide +kernel

theorem h1047 : P.leaf 36 1047 = 11040 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11040)]) (.cons c1047_0 (.nil)) (by decide) (by decide))

theorem cover1052 : P.CoversSplit 26 10 1052 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881, 972, 979, 1265, 1273]) (ps := [(3, [479, 486], [479, 486])]) (by decide +kernel)

noncomputable def f1052 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (1077248 + i)

theorem c1052_0 : rowSum f1052 0 1024 = 2724 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1052) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1052 (by decide)
  decide +kernel

theorem sum1052 : rowSum f1052 0 1024 = 2724 :=
  c1052_0

theorem h1052 : P.leaf 36 1052 = 2724 :=
  leaf_weighted (k := 26) (d := 10) (H := 1052) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1052) (by decide) (by decide +kernel)) sum1052

theorem cover1053 : P.CoversSplit 26 10 1053 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881]) (ps := [(4, [480, 487], [480, 487])]) (by decide +kernel)

noncomputable def f1053 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (1078272 + i)

theorem c1053_0 : rowSum f1053 0 1024 = 5332 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1053) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1053 (by decide)
  decide +kernel

theorem sum1053 : rowSum f1053 0 1024 = 5332 :=
  c1053_0

theorem h1053 : P.leaf 36 1053 = 5332 :=
  leaf_weighted (k := 26) (d := 10) (H := 1053) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1053) (by decide) (by decide +kernel)) sum1053

theorem cover1055 : P.CoversSplit 26 10 1055 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881]) (by decide +kernel)

noncomputable def f1055 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (1080320 + i)

theorem c1055_0 : rowSum f1055 0 1024 = 12268 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1055) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1055 (by decide)
  decide +kernel

theorem sum1055 : rowSum f1055 0 1024 = 12268 :=
  c1055_0

theorem h1055 : P.leaf 36 1055 = 12268 :=
  leaf_weighted (k := 26) (d := 10) (H := 1055) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1055) (by decide) (by decide +kernel)) sum1055

theorem cover1062 : P.CoversSplit 26 10 1062 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 523, 538, 579, 587, 629, 636, 922, 930, 1265, 2008]) (by decide +kernel)

theorem c1062_0 : P.sumLeaves 26 1087488 1024 = 2368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1062) (lo := 0) (len := 1024) (W := 2368) check rows elimOK (by decide) (by decide) cover1062 (by decide)
  decide +kernel

theorem h1062 : P.leaf 36 1062 = 2368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2368)]) (.cons c1062_0 (.nil)) (by decide) (by decide))

theorem cover1063 : P.CoversSplit 26 10 1063 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 523, 538, 579, 587, 629, 636, 881, 922, 1265, 2008]) (by decide +kernel)

theorem c1063_0 : P.sumLeaves 26 1088512 1024 = 25680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1063) (lo := 0) (len := 1024) (W := 25680) check rows elimOK (by decide) (by decide) cover1063 (by decide)
  decide +kernel

theorem h1063 : P.leaf 36 1063 = 25680 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25680)]) (.cons c1063_0 (.nil)) (by decide) (by decide))

theorem cover1064 : P.CoversSplit 26 10 1064 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c1064_0 : P.sumLeaves 26 1089536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1064) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1064 (by decide)
  decide +kernel

theorem h1064 : P.leaf 36 1064 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1064_0 (.nil)) (by decide) (by decide))

theorem cover1065 : P.CoversSplit 26 10 1065 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem c1065_0 : P.sumLeaves 26 1090560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1065) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1065 (by decide)
  decide +kernel

theorem h1065 : P.leaf 36 1065 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1065_0 (.nil)) (by decide) (by decide))

theorem cover1066 : P.CoversSplit 26 10 1066 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1066_0 : P.sumLeaves 26 1091584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1066) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1066 (by decide)
  decide +kernel

theorem h1066 : P.leaf 36 1066 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1066_0 (.nil)) (by decide) (by decide))

theorem cover1067 : P.CoversSplit 26 10 1067 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1067_0 : P.sumLeaves 26 1092608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1067) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1067 (by decide)
  decide +kernel

theorem h1067 : P.leaf 36 1067 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1067_0 (.nil)) (by decide) (by decide))

theorem cover1070 : P.CoversSplit 26 10 1070 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1070_0 : P.sumLeaves 26 1095680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1070) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1070 (by decide)
  decide +kernel

theorem h1070 : P.leaf 36 1070 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1070_0 (.nil)) (by decide) (by decide))

theorem cover1071 : P.CoversSplit 26 10 1071 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1071_0 : P.sumLeaves 26 1096704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1071) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1071 (by decide)
  decide +kernel

theorem h1071 : P.leaf 36 1071 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1071_0 (.nil)) (by decide) (by decide))

theorem cover1078 : P.CoversSplit 26 10 1078 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 587, 629, 636, 873, 922, 930, 1265, 2008]) (by decide +kernel)

theorem c1078_0 : P.sumLeaves 26 1103872 1024 = 22952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1078) (lo := 0) (len := 1024) (W := 22952) check rows elimOK (by decide) (by decide) cover1078 (by decide)
  decide +kernel

theorem h1078 : P.leaf 36 1078 = 22952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22952)]) (.cons c1078_0 (.nil)) (by decide) (by decide))

theorem cover1079 : P.CoversSplit 26 10 1079 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 587, 629, 636, 873, 881, 922, 1265, 2008]) (by decide +kernel)

theorem c1079_0 : P.sumLeaves 26 1104896 1024 = 99824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1079) (lo := 0) (len := 1024) (W := 99824) check rows elimOK (by decide) (by decide) cover1079 (by decide)
  decide +kernel

theorem h1079 : P.leaf 36 1079 = 99824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 99824)]) (.cons c1079_0 (.nil)) (by decide) (by decide))

theorem cover1082 : P.CoversSplit 26 10 1082 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1082_0 : P.sumLeaves 26 1107968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1082) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1082 (by decide)
  decide +kernel

theorem h1082 : P.leaf 36 1082 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1082_0 (.nil)) (by decide) (by decide))

theorem cover1083 : P.CoversSplit 26 10 1083 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1083_0 : P.sumLeaves 26 1108992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1083) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1083 (by decide)
  decide +kernel

theorem h1083 : P.leaf 36 1083 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1083_0 (.nil)) (by decide) (by decide))

theorem cover1084 : P.CoversSplit 26 10 1084 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1084_0 : P.sumLeaves 26 1110016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1084) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1084 (by decide)
  decide +kernel

theorem h1084 : P.leaf 36 1084 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1084_0 (.nil)) (by decide) (by decide))

theorem cover1085 : P.CoversSplit 26 10 1085 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1085_0 : P.sumLeaves 26 1111040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1085) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1085 (by decide)
  decide +kernel

theorem h1085 : P.leaf 36 1085 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1085_0 (.nil)) (by decide) (by decide))

theorem cover1086 : P.CoversSplit 26 10 1086 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1086_0 : P.sumLeaves 26 1112064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1086) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1086 (by decide)
  decide +kernel

theorem h1086 : P.leaf 36 1086 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1086_0 (.nil)) (by decide) (by decide))

theorem cover1087 : P.CoversSplit 26 10 1087 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1087_0 : P.sumLeaves 26 1113088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1087) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1087 (by decide)
  decide +kernel

theorem h1087 : P.leaf 36 1087 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1087_0 (.nil)) (by decide) (by decide))

theorem cover1132 : P.CoversSplit 26 10 1132 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1132_0 : P.sumLeaves 26 1159168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1132) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1132 (by decide)
  decide +kernel

theorem h1132 : P.leaf 36 1132 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1132_0 (.nil)) (by decide) (by decide))

theorem cover1133 : P.CoversSplit 26 10 1133 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1133_0 : P.sumLeaves 26 1160192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1133) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1133 (by decide)
  decide +kernel

theorem h1133 : P.leaf 36 1133 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1133_0 (.nil)) (by decide) (by decide))

theorem cover1134 : P.CoversSplit 26 10 1134 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1134_0 : P.sumLeaves 26 1161216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1134) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1134 (by decide)
  decide +kernel

theorem h1134 : P.leaf 36 1134 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1134_0 (.nil)) (by decide) (by decide))

theorem cover1135 : P.CoversSplit 26 10 1135 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1135_0 : P.sumLeaves 26 1162240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1135) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1135 (by decide)
  decide +kernel

theorem h1135 : P.leaf 36 1135 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1135_0 (.nil)) (by decide) (by decide))

theorem cover1150 : P.CoversSplit 26 10 1150 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1150_0 : P.sumLeaves 26 1177600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1150) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1150 (by decide)
  decide +kernel

theorem h1150 : P.leaf 36 1150 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1150_0 (.nil)) (by decide) (by decide))

theorem cover1151 : P.CoversSplit 26 10 1151 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1151_0 : P.sumLeaves 26 1178624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1151) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1151 (by decide)
  decide +kernel

theorem h1151 : P.leaf 36 1151 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1151_0 (.nil)) (by decide) (by decide))

theorem cover1188 : P.CoversSplit 26 10 1188 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 873, 972, 979, 1315, 1658, 2008]) (by decide +kernel)

theorem c1188_0 : P.sumLeaves 26 1216512 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1188) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1188 (by decide)
  decide +kernel

theorem contract1188_1 : P.leaf 32 19012 = 3288 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 19012) (ss := [(9, 7, 466), (8, 7, 472), (2, 1, 474), (6, 1, 482), (13, 1, 488), (3, 1, 523), (18, 1, 537), (21, 1, 586), (31, 0, 636), (29, 0, 489), (33, 0, 636), (20, 12, 866), (17, 12, 872)]) (ids := [2, 3, 5, 8, 9, 10, 12, 13, 14, 17, 20, 21, 22, 23, 24, 26, 28, 30, 25]) (cs := [1, 1, 2, 3, 1, 4, 4, 4, 5, 6, 7, 1, 8, 9, 10, 7, 1, 11, 7, 1, 12, 13, 14, 15, 16, 20, 17, 0, 18, 0, 19, 0]) (bs := [18, 1]) (W := 3288) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1188_1 : P.sumLeaves 26 1216768 64 = 3288 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 19012) rows (by decide) (by decide)).symm.trans contract1188_1

theorem c1188_2 : P.sumLeaves 26 1216832 320 = 14728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1188) (lo := 320) (len := 320) (W := 14728) check rows elimOK (by decide) (by decide) cover1188 (by decide)
  decide +kernel

theorem contract1188_3 : P.leaf 32 19018 = 3288 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 19018) (ss := [(9, 7, 466), (8, 7, 472), (2, 1, 474), (6, 0, 482), (13, 0, 412), (29, 1, 440), (31, 1, 489), (3, 1, 523), (18, 0, 419), (33, 1, 538), (21, 0, 586), (20, 12, 866), (17, 12, 872)]) (ids := [2, 3, 5, 8, 9, 10, 12, 13, 14, 17, 20, 21, 22, 23, 24, 26, 28, 30, 25]) (cs := [1, 1, 2, 3, 0, 4, 4, 4, 5, 6, 7, 0, 8, 9, 10, 7, 0, 11, 7, 0, 12, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1]) (bs := [18, 1]) (W := 3288) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1188_3 : P.sumLeaves 26 1217152 64 = 3288 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 19018) rows (by decide) (by decide)).symm.trans contract1188_3

theorem c1188_4 : P.sumLeaves 26 1217216 320 = 14792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1188) (lo := 704) (len := 320) (W := 14792) check rows elimOK (by decide) (by decide) cover1188 (by decide)
  decide +kernel

theorem h1188 : P.leaf 36 1188 = 36096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 3288), (320, 14728), (64, 3288), (320, 14792)]) (.cons c1188_0 (.cons c1188_1 (.cons c1188_2 (.cons c1188_3 (.cons c1188_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(511, 60), (1023, 6), (1043, 15), (1044, 180), (1045, 360), (1047, 180), (1052, 90), (1053, 180), (1055, 90), (1062, 360), (1063, 360), (1064, 120), (1065, 120), (1066, 720), (1067, 720), (1070, 360), (1071, 360), (1078, 360), (1079, 360), (1082, 360), (1083, 360), (1084, 720), (1085, 720), (1086, 720), (1087, 720), (1132, 180), (1133, 180), (1134, 360), (1135, 360), (1150, 180), (1151, 180), (1188, 60)]

theorem segOK : checkSeg 20 perms 511 1189 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 511 1189 10101 1156871826 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1156871826)
    (SegSum.cons (w := 60) h511 (SegSum.cons (w := 6) h1023 (SegSum.cons (w := 15) h1043 (SegSum.cons (w := 180) h1044 (SegSum.cons (w := 360) h1045 (SegSum.cons (w := 180) h1047 (SegSum.cons (w := 90) h1052 (SegSum.cons (w := 180) h1053 (SegSum.cons (w := 90) h1055 (SegSum.cons (w := 360) h1062 (SegSum.cons (w := 360) h1063 (SegSum.cons (w := 120) h1064 (SegSum.cons (w := 120) h1065 (SegSum.cons (w := 720) h1066 (SegSum.cons (w := 720) h1067 (SegSum.cons (w := 360) h1070 (SegSum.cons (w := 360) h1071 (SegSum.cons (w := 360) h1078 (SegSum.cons (w := 360) h1079 (SegSum.cons (w := 360) h1082 (SegSum.cons (w := 360) h1083 (SegSum.cons (w := 720) h1084 (SegSum.cons (w := 720) h1085 (SegSum.cons (w := 720) h1086 (SegSum.cons (w := 720) h1087 (SegSum.cons (w := 180) h1132 (SegSum.cons (w := 180) h1133 (SegSum.cons (w := 360) h1134 (SegSum.cons (w := 360) h1135 (SegSum.cons (w := 180) h1150 (SegSum.cons (w := 180) h1151 (SegSum.cons (w := 60) h1188 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S1
