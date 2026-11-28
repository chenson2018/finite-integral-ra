/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S5

open RACert RACert.Problem

theorem cover1095 : P.CoversSplit 24 10 1095 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem h1095 : P.leaf 34 1095 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1095) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1095) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1095 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1100 : P.CoversSplit 24 10 1100 0x80008000000080000000000000000000800080000000040000000000000000000000000000000000002000000020000000000000000000000020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 572, 573, 858, 860, 915, 1202, 1208, 1209]) (by decide +kernel)

theorem h1100 : P.leaf 34 1100 = 112860 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1100) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1100) (weight := fun _ => 1) (xs := [16, 53, 149, 181, 330, 367, 383, 463, 495, 511]) check rows elimOK (by decide) (by decide) cover1100 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1101 : P.CoversSplit 24 10 1101 0x8000cc000000800000000000000000008000cc000000800000000000000000000000000000000000003300000020000000000000000000000033000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 572, 858, 865, 1202, 1208, 1209]) (by decide +kernel)

theorem h1101 : P.leaf 34 1101 = 857716 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1101) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 1101) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1101) (weight := rowWeight keep3 twice3) (xs := [21, 48, 49, 52, 53, 149, 176, 177, 180, 181, 335, 362, 363, 366, 367, 383, 463, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover1101 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1102 : P.CoversSplit 24 10 1102 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem h1102 : P.leaf 34 1102 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1102) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1102) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1102 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1103 : P.CoversSplit 24 10 1103 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem h1103 : P.leaf 34 1103 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1103) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1103) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1103 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1110 : P.CoversSplit 24 10 1110 0x8000000000000000000000000000000080000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 480, 516, 572, 573, 858, 865, 867, 915, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h1110 : P.leaf 34 1110 = 14160 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1110) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1110) (weight := fun _ => 1) (xs := [821, 895, 1023]) check rows elimOK (by decide) (by decide) cover1110 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1111 : P.CoversSplit 24 10 1111 0xcc000000000000000000000000000000cc000000000000000032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 516, 572, 573, 858, 865, 867, 915, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h1111 : P.leaf 34 1111 = 262512 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1111) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1111) (weight := fun _ => 1) (xs := [817, 820, 821, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1111 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1116 : P.CoversSplit 24 10 1116 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1116 : P.leaf 34 1116 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1116) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1116) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1116 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1117 : P.CoversSplit 24 10 1117 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1117 : P.leaf 34 1117 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1117) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1117) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1117 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1118 : P.CoversSplit 24 10 1118 0x8000000000000000000000000000000080000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 572, 573, 858, 865, 867, 915, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h1118 : P.leaf 34 1118 = 48176 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1118) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1118) (weight := fun _ => 1) (xs := [821, 895, 1023]) check rows elimOK (by decide) (by decide) cover1118 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1119 : P.CoversSplit 24 10 1119 0xcc000000000000000000000000000000cc000000000000000032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 572, 573, 858, 865, 867, 915, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h1119 : P.leaf 34 1119 = 396640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1119) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1119) (weight := fun _ => 1) (xs := [817, 820, 821, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1119 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1132 : P.CoversSplit 24 10 1132 0x8000cc000000880000000000000000008000c4000000000000000000000000000000000000000000003300000022000000000000000000000031000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 572, 858, 860, 867, 915, 1202, 1208, 1209]) (by decide +kernel)

theorem h1132 : P.leaf 34 1132 = 616812 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1132) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1132) (weight := fun _ => 1) (xs := [48, 52, 53, 145, 149, 176, 177, 180, 181, 362, 366, 367, 383, 459, 463, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover1132 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3177 : P.CoversSplit 24 10 3177 0x8000cc000000cc0000000000000000008000cc000000c80000000000000000000000000000000000003300000033000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 474, 515, 522, 572, 858, 865, 1208, 1209, 1217]) (by decide +kernel)

theorem h3177 : P.leaf 34 3177 = 2393668 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 3177) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 3177) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3177) (weight := rowWeight keep3 twice3) (xs := [17, 20, 21, 48, 49, 52, 53, 144, 145, 148, 149, 176, 177, 180, 181, 331, 334, 335, 362, 363, 366, 367, 383, 458, 459, 462, 463, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover3177 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1133 : P.leaf 34 1133 = 2393668 :=
  orient5 (v := 3177) (by decide) (by decide +kernel) h3177

theorem cover1134 : P.CoversSplit 24 10 1134 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1134 : P.leaf 34 1134 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1134) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1134) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1134 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1135 : P.CoversSplit 24 10 1135 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1135 : P.leaf 34 1135 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1135) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1135) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1135 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1150 : P.CoversSplit 24 10 1150 0xc0004400800000000000000000000000c0004400000000000031001100010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 915, 1202, 1258]) (by decide +kernel)

theorem h1150 : P.leaf 34 1150 = 284546 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1150) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1150) (weight := fun _ => 1) (xs := [784, 800, 804, 816, 820, 821, 874, 878, 894, 895, 991, 1002, 1006, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1150 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1151 : P.CoversSplit 24 10 1151 0xcc00c800880000000000000000000000cc00c800880000000032003200220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 867, 915, 1202, 1209, 1258]) (by decide +kernel)

theorem h1151 : P.leaf 34 1151 = 2203356 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1151) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1151) (weight := fun _ => 1) (xs := [785, 789, 801, 804, 805, 817, 820, 821, 859, 863, 875, 878, 879, 890, 891, 894, 895, 987, 991, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1151 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1152 : P.CoversSplit 24 10 1152 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1152 : P.leaf 34 1152 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1152) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1152) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1152 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1153 : P.CoversSplit 24 10 1153 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1153 : P.leaf 34 1153 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1153) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1153) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1153 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1155 : P.CoversSplit 24 10 1155 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem h1155 : P.leaf 34 1155 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1155) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1155) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1155 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1156 : P.CoversSplit 24 10 1156 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1156 : P.leaf 34 1156 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1156) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1156) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1156 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1157 : P.CoversSplit 24 10 1157 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1157 : P.leaf 34 1157 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1157) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1157) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1157 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1158 : P.CoversSplit 24 10 1158 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem h1158 : P.leaf 34 1158 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1158) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1158) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1158 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1159 : P.CoversSplit 24 10 1159 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem h1159 : P.leaf 34 1159 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1159) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1159) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1159 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1164 : P.CoversSplit 24 10 1164 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h1164 : P.leaf 34 1164 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1164) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1164) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1164 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1165 : P.CoversSplit 24 10 1165 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1165 : P.leaf 34 1165 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1165) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1165) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1165 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1167 : P.CoversSplit 24 10 1167 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem h1167 : P.leaf 34 1167 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1167) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1167) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1167 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1169 : P.CoversSplit 24 10 1169 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1169 : P.leaf 34 1169 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1169) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1169) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1169 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover33304 : P.CoversSplit 24 10 33304 0x800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 467, 472, 473, 474, 508, 516, 517, 524, 528, 529, 578, 871, 915]) (by decide +kernel)

theorem h33304 : P.leaf 34 33304 = 56 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 33304) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 33304) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 33304) (weight := rowWeight keep5 twice5) (xs := [303, 319, 367, 383]) check rows elimOK (by decide) (by decide) cover33304 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1170 : P.leaf 34 1170 = 56 :=
  orient5 (v := 33304) (by decide) (by decide +kernel) h33304

theorem cover1171 : P.CoversSplit 24 10 1171 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem h1171 : P.leaf 34 1171 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1171) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1171) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1171 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1172 : P.CoversSplit 24 10 1172 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1172 : P.leaf 34 1172 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1172) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1172) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1172 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1173 : P.CoversSplit 24 10 1173 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1173 : P.leaf 34 1173 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1173) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1173) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1173 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1095, 24), (1100, 24), (1101, 24), (1102, 24), (1103, 24), (1110, 24), (1111, 24), (1116, 48), (1117, 48), (1118, 48), (1119, 48), (1132, 24), (1133, 24), (1134, 48), (1135, 48), (1150, 24), (1151, 24), (1152, 12), (1153, 48), (1155, 24), (1156, 48), (1157, 48), (1158, 48), (1159, 48), (1164, 24), (1165, 48), (1167, 24), (1169, 24), (1170, 24), (1171, 48), (1172, 48), (1173, 48)]

theorem segOK : checkSeg 16 perms 1095 1174 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1095 1174 1116 183247632 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 183247632)
    (SegSum.cons (w := 24) h1095 (SegSum.cons (w := 24) h1100 (SegSum.cons (w := 24) h1101 (SegSum.cons (w := 24) h1102 (SegSum.cons (w := 24) h1103 (SegSum.cons (w := 24) h1110 (SegSum.cons (w := 24) h1111 (SegSum.cons (w := 48) h1116 (SegSum.cons (w := 48) h1117 (SegSum.cons (w := 48) h1118 (SegSum.cons (w := 48) h1119 (SegSum.cons (w := 24) h1132 (SegSum.cons (w := 24) h1133 (SegSum.cons (w := 48) h1134 (SegSum.cons (w := 48) h1135 (SegSum.cons (w := 24) h1150 (SegSum.cons (w := 24) h1151 (SegSum.cons (w := 12) h1152 (SegSum.cons (w := 48) h1153 (SegSum.cons (w := 24) h1155 (SegSum.cons (w := 48) h1156 (SegSum.cons (w := 48) h1157 (SegSum.cons (w := 48) h1158 (SegSum.cons (w := 48) h1159 (SegSum.cons (w := 24) h1164 (SegSum.cons (w := 48) h1165 (SegSum.cons (w := 24) h1167 (SegSum.cons (w := 24) h1169 (SegSum.cons (w := 24) h1170 (SegSum.cons (w := 48) h1171 (SegSum.cons (w := 48) h1172 (SegSum.cons (w := 48) h1173 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S5
