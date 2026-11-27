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

theorem c1095_0 : P.sumLeaves 24 1121280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1095) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1095 (by decide)
  decide +kernel

theorem h1095 : P.leaf 34 1095 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1095_0 (.nil)) (by decide) (by decide))

theorem cover1100 : P.CoversSplit 24 10 1100 0x80008000000080000000000000000000800080000000040000000000000000000000000000000000002000000020000000000000000000000020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 572, 573, 858, 860, 915, 1202, 1208, 1209]) (by decide +kernel)

theorem c1100_0 : P.sumLeaves 24 1126400 1024 = 112860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1100) (lo := 0) (len := 1024) (W := 112860) check rows elimOK (by decide) (by decide) cover1100 (by decide)
  decide +kernel

theorem h1100 : P.leaf 34 1100 = 112860 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 112860)]) (.cons c1100_0 (.nil)) (by decide) (by decide))

theorem cover1101 : P.CoversSplit 24 10 1101 0x8000cc000000800000000000000000008000cc000000800000000000000000000000000000000000003300000020000000000000000000000033000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 572, 858, 865, 1202, 1208, 1209]) (by decide +kernel)

noncomputable def f1101 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (1127424 + i)

theorem c1101_0 : rowSum f1101 0 1024 = 857716 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1101) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover1101 (by decide)
  decide +kernel

theorem sum1101 : rowSum f1101 0 1024 = 857716 :=
  c1101_0

theorem h1101 : P.leaf 34 1101 = 857716 :=
  leaf_weighted (k := 24) (d := 10) (H := 1101) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 1101) (by decide) (by decide +kernel)) sum1101

theorem cover1102 : P.CoversSplit 24 10 1102 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem c1102_0 : P.sumLeaves 24 1128448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1102) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1102 (by decide)
  decide +kernel

theorem h1102 : P.leaf 34 1102 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1102_0 (.nil)) (by decide) (by decide))

theorem cover1103 : P.CoversSplit 24 10 1103 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem c1103_0 : P.sumLeaves 24 1129472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1103) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1103 (by decide)
  decide +kernel

theorem h1103 : P.leaf 34 1103 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1103_0 (.nil)) (by decide) (by decide))

theorem h1110 : P.leaf 34 1110 = 14160 := by
  exact leaf_contract_factors (k := 34) (b := 22) (H := 1110) (ss := [(5, 1, 559), (30, 19, 866), (35, 1, 867), (18, 11, 879), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 901), (19, 1, 908), (26, 1, 465), (28, 1, 465), (31, 1, 1251)]) (ids := [0, 1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 18, 19, 20, 23, 25, 27, 30, 31, 32, 21, 22]) (cs := [2, 3, 4, 1, 1, 5, 6, 7, 1, 1, 1, 8, 9, 10, 11, 12, 1, 1, 13, 14, 15, 22, 23, 16, 1, 17, 1, 18, 1, 1, 19, 20, 21, 1]) (bs := [20, 2]) (W := 14160) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1111 : P.CoversSplit 24 10 1111 0xcc000000000000000000000000000000cc000000000000000032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 516, 572, 573, 858, 865, 867, 915, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c1111_0 : P.sumLeaves 24 1137664 1024 = 262512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1111) (lo := 0) (len := 1024) (W := 262512) check rows elimOK (by decide) (by decide) cover1111 (by decide)
  decide +kernel

theorem h1111 : P.leaf 34 1111 = 262512 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 262512)]) (.cons c1111_0 (.nil)) (by decide) (by decide))

theorem cover1116 : P.CoversSplit 24 10 1116 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1116_0 : P.sumLeaves 24 1142784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1116) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1116 (by decide)
  decide +kernel

theorem h1116 : P.leaf 34 1116 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1116_0 (.nil)) (by decide) (by decide))

theorem cover1117 : P.CoversSplit 24 10 1117 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1117_0 : P.sumLeaves 24 1143808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1117) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1117 (by decide)
  decide +kernel

theorem h1117 : P.leaf 34 1117 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1117_0 (.nil)) (by decide) (by decide))

theorem cover1118 : P.CoversSplit 24 10 1118 0x8000000000000000000000000000000080000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 572, 573, 858, 865, 867, 915, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c1118_0 : P.sumLeaves 24 1144832 1024 = 48176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1118) (lo := 0) (len := 1024) (W := 48176) check rows elimOK (by decide) (by decide) cover1118 (by decide)
  decide +kernel

theorem h1118 : P.leaf 34 1118 = 48176 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 48176)]) (.cons c1118_0 (.nil)) (by decide) (by decide))

theorem cover1119 : P.CoversSplit 24 10 1119 0xcc000000000000000000000000000000cc000000000000000032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 572, 573, 858, 865, 867, 915, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem c1119_0 : P.sumLeaves 24 1145856 1024 = 396640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1119) (lo := 0) (len := 1024) (W := 396640) check rows elimOK (by decide) (by decide) cover1119 (by decide)
  decide +kernel

theorem h1119 : P.leaf 34 1119 = 396640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 396640)]) (.cons c1119_0 (.nil)) (by decide) (by decide))

theorem cover1132 : P.CoversSplit 24 10 1132 0x8000cc000000880000000000000000008000c4000000000000000000000000000000000000000000003300000022000000000000000000000031000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 572, 858, 860, 867, 915, 1202, 1208, 1209]) (by decide +kernel)

theorem c1132_0 : P.sumLeaves 24 1159168 1024 = 616812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1132) (lo := 0) (len := 1024) (W := 616812) check rows elimOK (by decide) (by decide) cover1132 (by decide)
  decide +kernel

theorem h1132 : P.leaf 34 1132 = 616812 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 616812)]) (.cons c1132_0 (.nil)) (by decide) (by decide))

theorem cover1133 : P.CoversSplit 24 10 1133 0x8000cc000000880000000000000000008000cc000000880000000000000000000000000000000000003300000022000000000000000000000033000000220000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 858, 860, 865, 867, 1202, 1208, 1209]) (by decide +kernel)

theorem c1133_0 : P.sumLeaves 24 1160192 1024 = 2393668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1133) (lo := 0) (len := 1024) (W := 2393668) check rows elimOK (by decide) (by decide) cover1133 (by decide)
  decide +kernel

theorem h1133 : P.leaf 34 1133 = 2393668 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2393668)]) (.cons c1133_0 (.nil)) (by decide) (by decide))

theorem cover1134 : P.CoversSplit 24 10 1134 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1134_0 : P.sumLeaves 24 1161216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1134) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1134 (by decide)
  decide +kernel

theorem h1134 : P.leaf 34 1134 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1134_0 (.nil)) (by decide) (by decide))

theorem cover1135 : P.CoversSplit 24 10 1135 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1135_0 : P.sumLeaves 24 1162240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1135) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1135 (by decide)
  decide +kernel

theorem h1135 : P.leaf 34 1135 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1135_0 (.nil)) (by decide) (by decide))

theorem cover1150 : P.CoversSplit 24 10 1150 0xc0004400800000000000000000000000c0004400000000000031001100010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 915, 1202, 1258]) (by decide +kernel)

theorem c1150_0 : P.sumLeaves 24 1177600 768 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1150) (lo := 0) (len := 768) (W := 0) check rows elimOK (by decide) (by decide) cover1150 (by decide)
  decide +kernel

theorem contract1150_1 : P.leaf 30 18412 = 90 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 18412) (ss := [(19, 1, 866), (18, 1, 879), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (3, 2, 472), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (20, 1, 873), (21, 1, 874)]) (ids := [0, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 2, 3, 4, 5, 0, 0, 0, 6, 7, 8, 0, 0, 0, 0, 0, 1, 1, 1, 1, 9, 10, 11, 16, 12, 0, 13, 0, 14, 15]) (bs := [14, 1]) (W := 90) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1150_1 : P.sumLeaves 24 1178368 64 = 90 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 18412) rows (by decide) (by decide)).symm.trans contract1150_1

theorem c1150_2 : P.sumLeaves 24 1178432 192 = 284456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1150) (lo := 832) (len := 192) (W := 284456) check rows elimOK (by decide) (by decide) cover1150 (by decide)
  decide +kernel

theorem h1150 : P.leaf 34 1150 = 284546 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 0), (64, 90), (192, 284456)]) (.cons c1150_0 (.cons c1150_1 (.cons c1150_2 (.nil)))) (by decide) (by decide))

theorem cover1151 : P.CoversSplit 24 10 1151 0xcc00c800880000000000000000000000cc00c800880000000032003200220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 867, 915, 1202, 1209, 1258]) (by decide +kernel)

theorem c1151_0 : P.sumLeaves 24 1178624 768 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1151) (lo := 0) (len := 768) (W := 0) check rows elimOK (by decide) (by decide) cover1151 (by decide)
  decide +kernel

theorem contract1151_1 : P.leaf 30 18428 = 724 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 18428) (ss := [(19, 1, 866), (18, 1, 879), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (20, 1, 873), (21, 1, 874)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 0, 0, 0, 7, 8, 9, 0, 0, 0, 0, 0, 1, 1, 1, 1, 10, 11, 12, 17, 13, 0, 14, 0, 15, 16]) (bs := [15, 1]) (W := 724) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1151_1 : P.sumLeaves 24 1179392 64 = 724 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 18428) rows (by decide) (by decide)).symm.trans contract1151_1

theorem c1151_2 : P.sumLeaves 24 1179456 192 = 2202632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1151) (lo := 832) (len := 192) (W := 2202632) check rows elimOK (by decide) (by decide) cover1151 (by decide)
  decide +kernel

theorem h1151 : P.leaf 34 1151 = 2203356 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 0), (64, 724), (192, 2202632)]) (.cons c1151_0 (.cons c1151_1 (.cons c1151_2 (.nil)))) (by decide) (by decide))

theorem cover1152 : P.CoversSplit 24 10 1152 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1152_0 : P.sumLeaves 24 1179648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1152) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1152 (by decide)
  decide +kernel

theorem h1152 : P.leaf 34 1152 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1152_0 (.nil)) (by decide) (by decide))

theorem cover1153 : P.CoversSplit 24 10 1153 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1153_0 : P.sumLeaves 24 1180672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1153) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1153 (by decide)
  decide +kernel

theorem h1153 : P.leaf 34 1153 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1153_0 (.nil)) (by decide) (by decide))

theorem cover1155 : P.CoversSplit 24 10 1155 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem c1155_0 : P.sumLeaves 24 1182720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1155) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1155 (by decide)
  decide +kernel

theorem h1155 : P.leaf 34 1155 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1155_0 (.nil)) (by decide) (by decide))

theorem cover1156 : P.CoversSplit 24 10 1156 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1156_0 : P.sumLeaves 24 1183744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1156) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1156 (by decide)
  decide +kernel

theorem h1156 : P.leaf 34 1156 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1156_0 (.nil)) (by decide) (by decide))

theorem cover1157 : P.CoversSplit 24 10 1157 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1157_0 : P.sumLeaves 24 1184768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1157) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1157 (by decide)
  decide +kernel

theorem h1157 : P.leaf 34 1157 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1157_0 (.nil)) (by decide) (by decide))

theorem cover1158 : P.CoversSplit 24 10 1158 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem c1158_0 : P.sumLeaves 24 1185792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1158) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1158 (by decide)
  decide +kernel

theorem h1158 : P.leaf 34 1158 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1158_0 (.nil)) (by decide) (by decide))

theorem cover1159 : P.CoversSplit 24 10 1159 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem c1159_0 : P.sumLeaves 24 1186816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1159) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1159 (by decide)
  decide +kernel

theorem h1159 : P.leaf 34 1159 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1159_0 (.nil)) (by decide) (by decide))

theorem cover1164 : P.CoversSplit 24 10 1164 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c1164_0 : P.sumLeaves 24 1191936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1164) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1164 (by decide)
  decide +kernel

theorem h1164 : P.leaf 34 1164 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1164_0 (.nil)) (by decide) (by decide))

theorem cover1165 : P.CoversSplit 24 10 1165 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1165_0 : P.sumLeaves 24 1192960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1165) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1165 (by decide)
  decide +kernel

theorem h1165 : P.leaf 34 1165 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1165_0 (.nil)) (by decide) (by decide))

theorem cover1167 : P.CoversSplit 24 10 1167 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [536]) (by decide +kernel)

theorem c1167_0 : P.sumLeaves 24 1195008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1167) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1167 (by decide)
  decide +kernel

theorem h1167 : P.leaf 34 1167 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1167_0 (.nil)) (by decide) (by decide))

theorem cover1169 : P.CoversSplit 24 10 1169 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1169_0 : P.sumLeaves 24 1197056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1169) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1169 (by decide)
  decide +kernel

theorem h1169 : P.leaf 34 1169 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1169_0 (.nil)) (by decide) (by decide))

theorem h1170 : P.leaf 34 1170 = 56 := by
  apply (leaf_contract (k := 34) (b := 14) (H := 1170) (ss := [(2, 1, 453), (5, 1, 453), (7, 6, 467), (8, 0, 468), (34, 1, 475), (26, 6, 479), (3, 1, 502), (9, 6, 510), (30, 19, 866), (35, 0, 867), (14, 0, 580), (12, 1, 487), (21, 0, 580), (33, 0, 580), (20, 1, 433), (31, 1, 566), (18, 11, 879), (19, 11, 908), (29, 1, 921), (32, 1, 1259)]) (ids := [2, 4, 8, 9, 11, 13, 14, 15, 20, 21, 22, 23, 25, 26]) (cs := [1, 1, 2, 1, 3, 3, 0, 3, 4, 5, 1, 6, 0, 7, 8, 9, 5, 5, 1, 0, 10, 11, 12, 13, 3, 14, 15, 1, 5, 1, 1, 0, 1, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem cover1171 : P.CoversSplit 24 10 1171 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c1171_0 : P.sumLeaves 24 1199104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1171) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1171 (by decide)
  decide +kernel

theorem h1171 : P.leaf 34 1171 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1171_0 (.nil)) (by decide) (by decide))

theorem cover1172 : P.CoversSplit 24 10 1172 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1172_0 : P.sumLeaves 24 1200128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1172) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1172 (by decide)
  decide +kernel

theorem h1172 : P.leaf 34 1172 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1172_0 (.nil)) (by decide) (by decide))

theorem cover1173 : P.CoversSplit 24 10 1173 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1173_0 : P.sumLeaves 24 1201152 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1173) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1173 (by decide)
  decide +kernel

theorem h1173 : P.leaf 34 1173 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1173_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1095, 24), (1100, 24), (1101, 24), (1102, 24), (1103, 24), (1110, 24), (1111, 24), (1116, 48), (1117, 48), (1118, 48), (1119, 48), (1132, 24), (1133, 24), (1134, 48), (1135, 48), (1150, 24), (1151, 24), (1152, 12), (1153, 48), (1155, 24), (1156, 48), (1157, 48), (1158, 48), (1159, 48), (1164, 24), (1165, 48), (1167, 24), (1169, 24), (1170, 24), (1171, 48), (1172, 48), (1173, 48)]

theorem segOK : checkSeg 16 perms 1095 1174 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1095 1174 1116 183247632 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 183247632)
    (SegSum.cons (w := 24) h1095 (SegSum.cons (w := 24) h1100 (SegSum.cons (w := 24) h1101 (SegSum.cons (w := 24) h1102 (SegSum.cons (w := 24) h1103 (SegSum.cons (w := 24) h1110 (SegSum.cons (w := 24) h1111 (SegSum.cons (w := 48) h1116 (SegSum.cons (w := 48) h1117 (SegSum.cons (w := 48) h1118 (SegSum.cons (w := 48) h1119 (SegSum.cons (w := 24) h1132 (SegSum.cons (w := 24) h1133 (SegSum.cons (w := 48) h1134 (SegSum.cons (w := 48) h1135 (SegSum.cons (w := 24) h1150 (SegSum.cons (w := 24) h1151 (SegSum.cons (w := 12) h1152 (SegSum.cons (w := 48) h1153 (SegSum.cons (w := 24) h1155 (SegSum.cons (w := 48) h1156 (SegSum.cons (w := 48) h1157 (SegSum.cons (w := 48) h1158 (SegSum.cons (w := 48) h1159 (SegSum.cons (w := 24) h1164 (SegSum.cons (w := 48) h1165 (SegSum.cons (w := 24) h1167 (SegSum.cons (w := 24) h1169 (SegSum.cons (w := 24) h1170 (SegSum.cons (w := 48) h1171 (SegSum.cons (w := 48) h1172 (SegSum.cons (w := 48) h1173 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S5
