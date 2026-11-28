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

theorem h511 : P.leaf 36 511 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 511) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 511) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover511 (by decide) (by decide) (by decide +kernel)
  decide +kernel

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
  leaf_weighted (k := 26) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 1023) (by decide) (by decide +kernel)) sum1023

theorem cover1043 : P.CoversSplit 26 10 1043 0x8000000000000000000000000000000000000000000000000000000000000001800000000000000000000400000000000000000000000000000000000000000180000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem h1043 : P.leaf 36 1043 = 749280 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 1043) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1043) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1043) (weight := rowWeight keep0 twice0) (xs := [256, 341, 511, 512, 682, 767, 768, 1023]) check rows elimOK (by decide) (by decide) cover1043 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1044 : P.CoversSplit 26 10 1044 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 972, 979, 1265, 1273, 2008]) (by decide +kernel)

theorem h1044 : P.leaf 36 1044 = 1412 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1044) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1044) (weight := fun _ => 1) (xs := [256, 341, 682, 767, 1023]) check rows elimOK (by decide) (by decide) cover1044 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1045 : P.CoversSplit 26 10 1045 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem h1045 : P.leaf 36 1045 = 4080 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1045) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1045) (weight := fun _ => 1) (xs := [256, 341, 682, 767, 1023]) check rows elimOK (by decide) (by decide) cover1045 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1047 : P.CoversSplit 26 10 1047 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem h1047 : P.leaf 36 1047 = 11040 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1047) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1047) (weight := fun _ => 1) (xs := [256, 341, 682, 767, 1023]) check rows elimOK (by decide) (by decide) cover1047 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1052 : P.CoversSplit 26 10 1052 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881, 972, 979, 1265, 1273]) (ps := [(3, [479, 486], [479, 486])]) (by decide +kernel)

theorem h1052 : P.leaf 36 1052 = 2724 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 1052) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1052) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1052) (weight := rowWeight keep0 twice0) (xs := [256, 512, 768, 1023]) check rows elimOK (by decide) (by decide) cover1052 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1053 : P.CoversSplit 26 10 1053 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881]) (ps := [(4, [480, 487], [480, 487])]) (by decide +kernel)

theorem h1053 : P.leaf 36 1053 = 5332 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 1053) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1053) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1053) (weight := rowWeight keep0 twice0) (xs := [256, 512, 768, 1023]) check rows elimOK (by decide) (by decide) cover1053 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1055 : P.CoversSplit 26 10 1055 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881]) (by decide +kernel)

theorem h1055 : P.leaf 36 1055 = 12268 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 1055) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1055) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1055) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover1055 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2124 : P.CoversSplit 26 10 2124 0x8000000000000001000000000000000000000000000000008000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h2124 : P.leaf 36 2124 = 2368 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2124) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2124) (weight := fun _ => 1) (xs := [768, 831, 960, 1023]) check rows elimOK (by decide) (by decide) cover2124 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1062 : P.leaf 36 1062 = 2368 :=
  orient6 (v := 2124) (by decide) (by decide +kernel) h2124

theorem cover2125 : P.CoversSplit 26 10 2125 0x8000000000000001000000000000000000000000000000008000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h2125 : P.leaf 36 2125 = 25680 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2125) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2125) (weight := fun _ => 1) (xs := [768, 831, 960, 1023]) check rows elimOK (by decide) (by decide) cover2125 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1063 : P.leaf 36 1063 = 25680 :=
  orient6 (v := 2125) (by decide) (by decide +kernel) h2125

theorem cover1064 : P.CoversSplit 26 10 1064 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h1064 : P.leaf 36 1064 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1064) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1064) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1064 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1065 : P.CoversSplit 26 10 1065 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [474]) (by decide +kernel)

theorem h1065 : P.leaf 36 1065 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1065) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1065) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1065 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1066 : P.CoversSplit 26 10 1066 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1066 : P.leaf 36 1066 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1066) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1066) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1066 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1067 : P.CoversSplit 26 10 1067 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1067 : P.leaf 36 1067 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1067) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1067) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1067 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1070 : P.CoversSplit 26 10 1070 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1070 : P.leaf 36 1070 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1070) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1070) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1070 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1071 : P.CoversSplit 26 10 1071 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1071 : P.leaf 36 1071 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1071) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1071) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1071 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2156 : P.CoversSplit 26 10 2156 0x8000000000000001000000000000000000000000000000008000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h2156 : P.leaf 36 2156 = 22952 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2156) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2156) (weight := fun _ => 1) (xs := [768, 831, 960, 1023]) check rows elimOK (by decide) (by decide) cover2156 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1078 : P.leaf 36 1078 = 22952 :=
  orient6 (v := 2156) (by decide) (by decide +kernel) h2156

theorem cover2157 : P.CoversSplit 26 10 2157 0x8000000000000001000000000000000000000000000000008000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h2157 : P.leaf 36 2157 = 99824 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2157) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2157) (weight := fun _ => 1) (xs := [768, 831, 960, 1023]) check rows elimOK (by decide) (by decide) cover2157 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1079 : P.leaf 36 1079 = 99824 :=
  orient6 (v := 2157) (by decide) (by decide +kernel) h2157

theorem cover1082 : P.CoversSplit 26 10 1082 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1082 : P.leaf 36 1082 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1082) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1082) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1082 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1083 : P.CoversSplit 26 10 1083 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1083 : P.leaf 36 1083 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1083) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1083) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1083 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1084 : P.CoversSplit 26 10 1084 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1084 : P.leaf 36 1084 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1084) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1084) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1084 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1085 : P.CoversSplit 26 10 1085 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1085 : P.leaf 36 1085 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1085) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1085) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1085 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1086 : P.CoversSplit 26 10 1086 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1086 : P.leaf 36 1086 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1086) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1086) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1086 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1087 : P.CoversSplit 26 10 1087 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1087 : P.leaf 36 1087 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1087) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1087) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1087 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1132 : P.CoversSplit 26 10 1132 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1132 : P.leaf 36 1132 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1132) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1132) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1132 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1133 : P.CoversSplit 26 10 1133 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1133 : P.leaf 36 1133 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1133) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1133) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1133 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1134 : P.CoversSplit 26 10 1134 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1134 : P.leaf 36 1134 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1134) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1134) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1134 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1135 : P.CoversSplit 26 10 1135 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1135 : P.leaf 36 1135 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1135) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1135) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1135 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1150 : P.CoversSplit 26 10 1150 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1150 : P.leaf 36 1150 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1150) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1150) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1150 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1151 : P.CoversSplit 26 10 1151 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1151 : P.leaf 36 1151 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1151) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1151) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1151 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2194 : P.CoversSplit 26 10 2194 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000044004400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000001100110000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 587, 629, 636, 922, 930, 2008]) (by decide +kernel)

theorem h2194 : P.leaf 36 2194 = 36096 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 2194) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 2194) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2194) (weight := rowWeight keep3 twice3) (xs := [256, 260, 272, 276, 341, 682, 686, 698, 702, 767, 1023]) check rows elimOK (by decide) (by decide) cover2194 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1188 : P.leaf 36 1188 = 36096 :=
  orient4 (v := 2194) (by decide) (by decide +kernel) h2194

def seg : List (ℕ × ℕ) := [(511, 60), (1023, 6), (1043, 15), (1044, 180), (1045, 360), (1047, 180), (1052, 90), (1053, 180), (1055, 90), (1062, 360), (1063, 360), (1064, 120), (1065, 120), (1066, 720), (1067, 720), (1070, 360), (1071, 360), (1078, 360), (1079, 360), (1082, 360), (1083, 360), (1084, 720), (1085, 720), (1086, 720), (1087, 720), (1132, 180), (1133, 180), (1134, 360), (1135, 360), (1150, 180), (1151, 180), (1188, 60)]

theorem segOK : checkSeg 20 perms 511 1189 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 511 1189 10101 1156871826 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1156871826)
    (SegSum.cons (w := 60) h511 (SegSum.cons (w := 6) h1023 (SegSum.cons (w := 15) h1043 (SegSum.cons (w := 180) h1044 (SegSum.cons (w := 360) h1045 (SegSum.cons (w := 180) h1047 (SegSum.cons (w := 90) h1052 (SegSum.cons (w := 180) h1053 (SegSum.cons (w := 90) h1055 (SegSum.cons (w := 360) h1062 (SegSum.cons (w := 360) h1063 (SegSum.cons (w := 120) h1064 (SegSum.cons (w := 120) h1065 (SegSum.cons (w := 720) h1066 (SegSum.cons (w := 720) h1067 (SegSum.cons (w := 360) h1070 (SegSum.cons (w := 360) h1071 (SegSum.cons (w := 360) h1078 (SegSum.cons (w := 360) h1079 (SegSum.cons (w := 360) h1082 (SegSum.cons (w := 360) h1083 (SegSum.cons (w := 720) h1084 (SegSum.cons (w := 720) h1085 (SegSum.cons (w := 720) h1086 (SegSum.cons (w := 720) h1087 (SegSum.cons (w := 180) h1132 (SegSum.cons (w := 180) h1133 (SegSum.cons (w := 360) h1134 (SegSum.cons (w := 360) h1135 (SegSum.cons (w := 180) h1150 (SegSum.cons (w := 180) h1151 (SegSum.cons (w := 60) h1188 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S1
