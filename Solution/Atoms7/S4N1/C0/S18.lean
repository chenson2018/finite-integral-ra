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

namespace RACert.S4N1.C0.S18

open RACert RACert.Problem

theorem cover3180 : P.CoversSplit 24 10 3180 0x800000000000000000000000000000008000000000000000000000000000000000000000000000000033000000320000000000000000000000330000003200008000cc000000c80000000000000000008000cc000000c80000000000000000000000000000000000003300000032000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 572, 858, 915, 1208, 1209]) (by decide +kernel)

noncomputable def f3180 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3256320 + i)

theorem c3180_0 : rowSum f3180 0 1024 = 2570417 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3180) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3180 (by decide)
  decide +kernel

theorem sum3180 : rowSum f3180 0 1024 = 2570417 :=
  c3180_0

theorem h3180 : P.leaf 34 3180 = 2570417 :=
  leaf_weighted (k := 24) (d := 10) (H := 3180) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 3180) (by decide) (by decide +kernel)) sum3180

theorem cover3181 : P.CoversSplit 24 10 3181 0x800000000000000000000000000000008000000000000000000000000000000000000000000000000033000000330000000000000000000000330000003300008000cc000000cc0000000000000000008000cc000000c80000000000000000000000000000000000003300000033000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 858, 865, 1208, 1209, 1217]) (by decide +kernel)

noncomputable def f3181 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3257344 + i)

theorem c3181_0 : rowSum f3181 0 1024 = 5488880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3181) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3181 (by decide)
  decide +kernel

theorem sum3181 : rowSum f3181 0 1024 = 5488880 :=
  c3181_0

theorem h3181 : P.leaf 34 3181 = 5488880 :=
  leaf_weighted (k := 24) (d := 10) (H := 3181) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 3181) (by decide) (by decide +kernel)) sum3181

theorem cover3182 : P.CoversSplit 24 10 3182 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000002100000000000000000000002100000021000080000000000000000000000000000000800000000000000000000000000000000000000000000000002100000021000000000000000000000021000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 572, 858, 865, 915, 1209, 1217]) (by decide +kernel)

theorem c3182_0 : P.sumLeaves 24 3258368 512 = 9969 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3182) (lo := 0) (len := 512) (W := 9969) check rows elimOK (by decide) (by decide) cover3182 (by decide)
  decide +kernel

theorem contract3182_1 : P.leaf 30 50920 = 1099 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 50920) (ss := [(5, 1, 425), (10, 0, 466), (3, 0, 472), (12, 1, 458), (30, 1, 523), (27, 0, 572), (29, 0, 572), (17, 0, 1266), (20, 1, 538), (16, 0, 1272), (19, 18, 1651), (25, 18, 1609)]) (ids := [0, 2, 4, 5, 6, 7, 9, 11, 12, 13, 16, 19, 20, 21, 22, 24, 26, 29]) (cs := [2, 0, 3, 1, 4, 5, 6, 7, 0, 8, 1, 9, 10, 11, 0, 0, 12, 12, 1, 13, 14, 15, 16, 12, 17, 0, 18, 0, 1, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c3182_1 : P.sumLeaves 24 3258880 64 = 1099 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 50920) rows (by decide) (by decide)).symm.trans contract3182_1

theorem c3182_2 : P.sumLeaves 24 3258944 448 = 102286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3182) (lo := 576) (len := 448) (W := 102286) check rows elimOK (by decide) (by decide) cover3182 (by decide)
  decide +kernel

theorem h3182 : P.leaf 34 3182 = 113354 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 9969), (64, 1099), (448, 102286)]) (.cons c3182_0 (.cons c3182_1 (.cons c3182_2 (.nil)))) (by decide) (by decide))

theorem cover3183 : P.CoversSplit 24 10 3183 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000002100000000000000000000002100000021000080000000000000000000000000000000800000000000000000000000000000000000000000000000002100000021000000000000000000000021000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 1209, 1217]) (by decide +kernel)

theorem c3183_0 : P.sumLeaves 24 3259392 1024 = 412830 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3183) (lo := 0) (len := 1024) (W := 412830) check rows elimOK (by decide) (by decide) cover3183 (by decide)
  decide +kernel

theorem h3183 : P.leaf 34 3183 = 412830 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 412830)]) (.cons c3183_0 (.nil)) (by decide) (by decide))

theorem cover3198 : P.CoversSplit 24 10 3198 0xc0004400c00000000000000000000000c0004400c000000000310011003100000000000000000000000000000000000000000000000000000000000000000000c0004400c00000000000000000000000c0004400c000000000310011002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 915, 1209, 1217, 1258]) (ps := [(14, [1217], [915])]) (by decide +kernel)

theorem c3198_0 : P.sumLeaves 24 3274752 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3198) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover3198 (by decide)
  decide +kernel

theorem contract3198_1 : P.leaf 30 51172 = 292 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 51172) (ss := [(19, 1, 866), (18, 1, 867), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (3, 2, 472), (9, 0, 573), (13, 0, 579), (14, 0, 580), (5, 1, 433), (15, 0, 587), (17, 0, 587), (12, 1, 825), (20, 1, 873), (31, 1, 1217)]) (ids := [0, 2, 4, 8, 9, 20, 21, 22, 24, 26, 28, 19, 23]) (cs := [2, 2, 3, 1, 4, 0, 0, 0, 5, 6, 1, 0, 0, 0, 0, 0, 1, 1, 1, 13, 7, 8, 9, 14, 10, 0, 11, 0, 12, 1]) (bs := [11, 2]) (W := 292) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3198_1 : P.sumLeaves 24 3275008 64 = 292 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51172) rows (by decide) (by decide)).symm.trans contract3198_1

theorem contract3198_2 : P.leaf 30 51173 = 1600 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 51173) (ss := [(27, 1, 572), (19, 1, 866), (9, 1, 587), (18, 1, 867), (7, 1, 579), (29, 1, 915), (13, 1, 922), (15, 1, 930), (16, 1, 1265), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (20, 1, 628), (12, 1, 825), (31, 1, 1217), (17, 1, 1273)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 24, 26, 28, 19, 23]) (cs := [2, 3, 4, 1, 5, 1, 0, 1, 6, 7, 1, 1, 0, 1, 1, 1, 1, 1, 1, 14, 8, 9, 10, 15, 11, 1, 12, 1, 13, 1]) (bs := [12, 2]) (W := 1600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3198_2 : P.sumLeaves 24 3275072 64 = 1600 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51173) rows (by decide) (by decide)).symm.trans contract3198_2

theorem c3198_3 : P.sumLeaves 24 3275136 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3198) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover3198 (by decide)
  decide +kernel

theorem contract3198_4 : P.leaf 30 51175 = 5284 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 51175) (ss := [(27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 17, 10, 11, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 5284) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3198_4 : P.sumLeaves 24 3275200 64 = 5284 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51175) rows (by decide) (by decide)).symm.trans contract3198_4

theorem c3198_5 : P.sumLeaves 24 3275264 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3198) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover3198 (by decide)
  decide +kernel

theorem contract3198_6 : P.leaf 30 51180 = 3504 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 51180) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (3, 2, 472), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (20, 1, 873)]) (ids := [0, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 16, 17, 19, 23]) (cs := [2, 2, 3, 4, 5, 0, 0, 0, 6, 7, 8, 0, 0, 0, 0, 0, 16, 17, 1, 18, 9, 10, 11, 19, 12, 0, 13, 0, 14, 15]) (bs := [14, 4]) (W := 3504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3198_6 : P.sumLeaves 24 3275520 64 = 3504 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51180) rows (by decide) (by decide)).symm.trans contract3198_6

theorem c3198_7 : P.sumLeaves 24 3275584 192 = 995710 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3198) (lo := 832) (len := 192) (W := 995710) check rows elimOK (by decide) (by decide) cover3198 (by decide)
  decide +kernel

theorem h3198 : P.leaf 34 3198 = 1006390 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 292), (64, 1600), (64, 0), (64, 5284), (256, 0), (64, 3504), (192, 995710)]) (.cons c3198_0 (.cons c3198_1 (.cons c3198_2 (.cons c3198_3 (.cons c3198_4 (.cons c3198_5 (.cons c3198_6 (.cons c3198_7 (.nil))))))))) (by decide) (by decide))

theorem cover3199 : P.CoversSplit 24 10 3199 0xcc00c800cc0000000000000000000000cc00c800cc00000000320032003200000000000000000000000000000000000000000000000000000000000000000000cc00c800cc0000000000000000000000cc00c800c000000000320032002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 865, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915])]) (by decide +kernel)

theorem c3199_0 : P.sumLeaves 24 3275776 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3199) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover3199 (by decide)
  decide +kernel

theorem contract3199_1 : P.leaf 30 51188 = 1136 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 51188) (ss := [(19, 1, 866), (18, 1, 867), (16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (5, 1, 433), (15, 0, 587), (17, 0, 587), (12, 1, 825), (20, 1, 873), (31, 1, 1217)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 24, 26, 28, 19, 23]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 1, 1, 1, 14, 8, 9, 10, 15, 11, 0, 12, 0, 13, 1]) (bs := [12, 2]) (W := 1136) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3199_1 : P.sumLeaves 24 3276032 64 = 1136 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51188) rows (by decide) (by decide)).symm.trans contract3199_1

theorem contract3199_2 : P.leaf 30 51189 = 7872 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 51189) (ss := [(27, 1, 572), (19, 1, 866), (9, 1, 587), (18, 1, 867), (7, 1, 579), (29, 1, 915), (13, 1, 922), (15, 1, 930), (16, 1, 1265), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (20, 1, 628), (12, 1, 825), (31, 1, 1217), (17, 1, 1273)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 24, 26, 28, 19, 23]) (cs := [2, 3, 4, 1, 5, 1, 0, 1, 6, 7, 1, 1, 0, 1, 1, 1, 1, 1, 1, 14, 8, 9, 10, 15, 11, 1, 12, 1, 13, 1]) (bs := [12, 2]) (W := 7872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3199_2 : P.sumLeaves 24 3276096 64 = 7872 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51189) rows (by decide) (by decide)).symm.trans contract3199_2

theorem c3199_3 : P.sumLeaves 24 3276160 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3199) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover3199 (by decide)
  decide +kernel

theorem contract3199_4 : P.leaf 30 51191 = 22624 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 51191) (ss := [(27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 17, 10, 11, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 22624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3199_4 : P.sumLeaves 24 3276224 64 = 22624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51191) rows (by decide) (by decide)).symm.trans contract3199_4

theorem c3199_5 : P.sumLeaves 24 3276288 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3199) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover3199 (by decide)
  decide +kernel

theorem contract3199_6 : P.leaf 30 51196 = 18528 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 51196) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (15, 0, 587), (17, 0, 587), (20, 1, 873)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 16, 17, 19, 23]) (cs := [2, 3, 4, 5, 6, 0, 0, 0, 7, 8, 9, 0, 0, 0, 0, 0, 17, 18, 1, 19, 10, 11, 12, 20, 13, 0, 14, 0, 15, 16]) (bs := [15, 4]) (W := 18528) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3199_6 : P.sumLeaves 24 3276544 64 = 18528 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 51196) rows (by decide) (by decide)).symm.trans contract3199_6

theorem c3199_7 : P.sumLeaves 24 3276608 192 = 4513478 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3199) (lo := 832) (len := 192) (W := 4513478) check rows elimOK (by decide) (by decide) cover3199 (by decide)
  decide +kernel

theorem h3199 : P.leaf 34 3199 = 4563638 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 1136), (64, 7872), (64, 0), (64, 22624), (256, 0), (64, 18528), (192, 4513478)]) (.cons c3199_0 (.cons c3199_1 (.cons c3199_2 (.cons c3199_3 (.cons c3199_4 (.cons c3199_5 (.cons c3199_6 (.cons c3199_7 (.nil))))))))) (by decide) (by decide))

theorem cover3236 : P.CoversSplit 24 10 3236 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3236_0 : P.sumLeaves 24 3313664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3236) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3236 (by decide)
  decide +kernel

theorem h3236 : P.leaf 34 3236 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3236_0 (.nil)) (by decide) (by decide))

theorem h3237 : P.leaf 34 3237 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566), (4, 1, 867), (5, 1, 404)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3238 : P.CoversSplit 24 10 3238 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3238_0 : P.sumLeaves 24 3315712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3238) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3238 (by decide)
  decide +kernel

theorem h3238 : P.leaf 34 3238 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3238_0 (.nil)) (by decide) (by decide))

theorem cover3239 : P.CoversSplit 24 10 3239 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3239_0 : P.sumLeaves 24 3316736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3239) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3239 (by decide)
  decide +kernel

theorem h3239 : P.leaf 34 3239 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3239_0 (.nil)) (by decide) (by decide))

theorem cover3240 : P.CoversSplit 24 10 3240 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3240_0 : P.sumLeaves 24 3317760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3240) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3240 (by decide)
  decide +kernel

theorem h3240 : P.leaf 34 3240 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3240_0 (.nil)) (by decide) (by decide))

theorem h3241 : P.leaf 34 3241 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (18, 1, 475), (35, 14, 487), (14, 0, 524), (29, 2, 474), (16, 3, 529), (15, 2, 558), (4, 1, 559), (33, 0, 566)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3242 : P.CoversSplit 24 10 3242 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3242_0 : P.sumLeaves 24 3319808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3242) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3242 (by decide)
  decide +kernel

theorem h3242 : P.leaf 34 3242 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3242_0 (.nil)) (by decide) (by decide))

theorem cover3243 : P.CoversSplit 24 10 3243 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3243_0 : P.sumLeaves 24 3320832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3243) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3243 (by decide)
  decide +kernel

theorem h3243 : P.leaf 34 3243 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3243_0 (.nil)) (by decide) (by decide))

theorem cover3244 : P.CoversSplit 24 10 3244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3244_0 : P.sumLeaves 24 3321856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3244) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3244 (by decide)
  decide +kernel

theorem h3244 : P.leaf 34 3244 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3244_0 (.nil)) (by decide) (by decide))

theorem h3245 : P.leaf 34 3245 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (35, 0, 524), (18, 1, 475), (16, 3, 529), (33, 0, 566), (4, 1, 536), (14, 1, 929)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3246 : P.CoversSplit 24 10 3246 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3246_0 : P.sumLeaves 24 3323904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3246) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3246 (by decide)
  decide +kernel

theorem h3246 : P.leaf 34 3246 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3246_0 (.nil)) (by decide) (by decide))

theorem cover3247 : P.CoversSplit 24 10 3247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c3247_0 : P.sumLeaves 24 3324928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3247) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3247 (by decide)
  decide +kernel

theorem h3247 : P.leaf 34 3247 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3247_0 (.nil)) (by decide) (by decide))

theorem cover3254 : P.CoversSplit 24 10 3254 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 865, 866, 908, 916, 921, 1209, 1259, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem c3254_0 : P.sumLeaves 24 3332096 1024 = 58912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3254) (lo := 0) (len := 1024) (W := 58912) check rows elimOK (by decide) (by decide) cover3254 (by decide)
  decide +kernel

theorem h3254 : P.leaf 34 3254 = 58912 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 58912)]) (.cons c3254_0 (.nil)) (by decide) (by decide))

theorem cover3255 : P.CoversSplit 24 10 3255 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 858, 865, 866, 915, 916, 921, 1202, 1209, 1259, 1308]) (ps := [(8, [580], [573])]) (by decide +kernel)

theorem c3255_0 : P.sumLeaves 24 3333120 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3255) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3255 (by decide)
  decide +kernel

theorem contract3255_1 : P.leaf 30 52087 = 15360 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 52087) (ss := [(5, 1, 475), (8, 1, 580), (27, 1, 573), (18, 1, 580), (30, 1, 866), (11, 1, 872), (12, 1, 817), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 929), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 7, 20, 4, 5, 8, 13, 15, 21, 22, 23, 24, 26]) (cs := [2, 3, 4, 1, 7, 8, 1, 5, 9, 1, 1, 1, 1, 10, 1, 11, 1, 1, 1, 1, 6, 12, 13, 14, 15, 1, 16, 1, 1, 1]) (bs := [5, 10]) (W := 15360) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3255_1 : P.sumLeaves 24 3333568 64 = 15360 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52087) rows (by decide) (by decide)).symm.trans contract3255_1

theorem c3255_2 : P.sumLeaves 24 3333632 512 = 590080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3255) (lo := 512) (len := 512) (W := 590080) check rows elimOK (by decide) (by decide) cover3255 (by decide)
  decide +kernel

theorem h3255 : P.leaf 34 3255 = 605440 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 15360), (512, 590080)]) (.cons c3255_0 (.cons c3255_1 (.cons c3255_2 (.nil)))) (by decide) (by decide))

theorem h3256 : P.leaf 34 3256 = 9856 := by
  exact leaf_contract_factors (k := 34) (b := 17) (H := 3256) (ss := [(2, 1, 466), (29, 1, 472), (18, 11, 475), (35, 1, 487), (5, 1, 524), (3, 1, 409), (11, 1, 559), (4, 1, 410), (30, 1, 867), (28, 1, 858), (31, 1, 1251), (32, 1, 1259), (10, 1, 809), (6, 1, 459), (27, 1, 473), (12, 1, 817), (34, 1, 915)]) (ids := [5, 6, 7, 11, 12, 13, 14, 15, 17, 18, 19, 23, 24, 31, 20, 21, 22]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 6, 7, 8, 9, 1, 10, 11, 12, 16, 17, 18, 13, 14, 1, 1, 1, 1, 1, 1, 15, 1, 1]) (bs := [14, 3]) (W := 9856) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h3257 : P.leaf 34 3257 = 135040 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 3257) (ss := [(18, 11, 475), (35, 1, 487), (29, 1, 474), (5, 1, 524), (11, 1, 559), (30, 1, 867), (31, 1, 1251), (32, 1, 1259), (27, 1, 473), (6, 1, 459), (10, 1, 809), (12, 1, 817), (34, 1, 915)]) (ids := [0, 1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 17, 18, 19, 20, 22, 23, 24, 26, 31, 21]) (cs := [2, 3, 4, 1, 1, 5, 6, 7, 1, 1, 1, 8, 9, 10, 11, 12, 1, 13, 14, 15, 16, 22, 17, 18, 19, 1, 20, 1, 1, 1, 1, 21, 1, 1]) (bs := [20, 1]) (W := 135040) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover3258 : P.CoversSplit 24 10 3258 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 487, 517, 573, 858, 865, 867, 916, 921, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem c3258_0 : P.sumLeaves 24 3336192 1024 = 106576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3258) (lo := 0) (len := 1024) (W := 106576) check rows elimOK (by decide) (by decide) cover3258 (by decide)
  decide +kernel

theorem h3258 : P.leaf 34 3258 = 106576 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 106576)]) (.cons c3258_0 (.nil)) (by decide) (by decide))

theorem cover3259 : P.CoversSplit 24 10 3259 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 517, 573, 858, 867, 916, 921, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem c3259_0 : P.sumLeaves 24 3337216 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3259) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3259 (by decide)
  decide +kernel

theorem contract3259_1 : P.leaf 30 52151 = 11776 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 52151) (ss := [(5, 1, 524), (8, 1, 580), (27, 1, 573), (18, 1, 580), (30, 1, 867), (11, 1, 872), (12, 1, 818), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 7, 20, 5, 8, 15, 21, 22, 23, 24, 26]) (cs := [2, 3, 4, 1, 5, 8, 1, 6, 9, 1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 1, 7, 11, 12, 13, 14, 1, 15, 1, 1, 1]) (bs := [6, 8]) (W := 11776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3259_1 : P.sumLeaves 24 3337664 64 = 11776 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52151) rows (by decide) (by decide)).symm.trans contract3259_1

theorem c3259_2 : P.sumLeaves 24 3337728 512 = 1287872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3259) (lo := 512) (len := 512) (W := 1287872) check rows elimOK (by decide) (by decide) cover3259 (by decide)
  decide +kernel

theorem h3259 : P.leaf 34 3259 = 1299648 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 11776), (512, 1287872)]) (.cons c3259_0 (.cons c3259_1 (.cons c3259_2 (.nil)))) (by decide) (by decide))

theorem cover3260 : P.CoversSplit 24 10 3260 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 573, 858, 865, 915, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem c3260_0 : P.sumLeaves 24 3338240 1024 = 23488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3260) (lo := 0) (len := 1024) (W := 23488) check rows elimOK (by decide) (by decide) cover3260 (by decide)
  decide +kernel

theorem h3260 : P.leaf 34 3260 = 23488 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23488)]) (.cons c3260_0 (.nil)) (by decide) (by decide))

theorem cover3261 : P.CoversSplit 24 10 3261 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 573, 858, 865, 915, 1202, 1209, 1210, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c3261_0 : P.sumLeaves 24 3339264 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3261) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3261 (by decide)
  decide +kernel

theorem contract3261_1 : P.leaf 30 52183 = 4864 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 52183) (ss := [(27, 1, 473), (29, 1, 473), (18, 11, 475), (11, 1, 487), (6, 1, 459), (5, 1, 524), (8, 1, 580), (10, 1, 809), (12, 1, 817), (13, 1, 922), (14, 1, 929), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 7, 20, 5, 13, 15, 21, 22, 23, 24, 26]) (cs := [2, 3, 4, 1, 1, 7, 1, 5, 1, 1, 1, 1, 1, 8, 1, 9, 1, 1, 1, 1, 6, 10, 11, 12, 13, 1, 14, 1, 1, 1]) (bs := [5, 8]) (W := 4864) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3261_1 : P.sumLeaves 24 3339712 64 = 4864 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52183) rows (by decide) (by decide)).symm.trans contract3261_1

theorem c3261_2 : P.sumLeaves 24 3339776 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3261) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover3261 (by decide)
  decide +kernel

theorem contract3261_3 : P.leaf 30 52189 = 33024 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 52189) (ss := [(27, 1, 473), (29, 1, 473), (11, 1, 475), (6, 1, 459), (5, 1, 524), (31, 1, 566), (10, 1, 809), (12, 1, 817), (30, 1, 1209), (17, 1, 1266), (16, 1, 1272), (18, 1, 1265)]) (ids := [0, 1, 2, 5, 6, 7, 11, 12, 13, 17, 18, 19, 20, 22, 23, 24, 26, 21]) (cs := [2, 3, 4, 1, 1, 5, 6, 7, 1, 1, 1, 8, 9, 10, 1, 1, 1, 11, 12, 13, 14, 19, 15, 16, 17, 1, 18, 1, 1, 1]) (bs := [17, 1]) (W := 33024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3261_3 : P.sumLeaves 24 3340096 64 = 33024 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52189) rows (by decide) (by decide)).symm.trans contract3261_3

theorem c3261_4 : P.sumLeaves 24 3340160 128 = 121664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3261) (lo := 896) (len := 128) (W := 121664) check rows elimOK (by decide) (by decide) cover3261 (by decide)
  decide +kernel

theorem h3261 : P.leaf 34 3261 = 159552 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 4864), (320, 0), (64, 33024), (128, 121664)]) (.cons c3261_0 (.cons c3261_1 (.cons c3261_2 (.cons c3261_3 (.cons c3261_4 (.nil)))))) (by decide) (by decide))

theorem cover3262 : P.CoversSplit 24 10 3262 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 865, 916, 921, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem c3262_0 : P.sumLeaves 24 3340288 1024 = 383080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3262) (lo := 0) (len := 1024) (W := 383080) check rows elimOK (by decide) (by decide) cover3262 (by decide)
  decide +kernel

theorem h3262 : P.leaf 34 3262 = 383080 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 383080)]) (.cons c3262_0 (.nil)) (by decide) (by decide))

theorem cover3263 : P.CoversSplit 24 10 3263 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 865, 916, 921, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem c3263_0 : P.sumLeaves 24 3341312 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3263) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover3263 (by decide)
  decide +kernel

theorem contract3263_1 : P.leaf 30 52215 = 41344 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 52215) (ss := [(5, 1, 524), (8, 1, 580), (27, 1, 573), (18, 1, 580), (11, 1, 872), (29, 1, 916), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 8, 10, 13, 20, 21, 24, 5, 7, 15, 22, 23, 26]) (cs := [2, 3, 4, 1, 5, 12, 1, 13, 6, 1, 7, 1, 1, 8, 1, 14, 1, 1, 1, 1, 9, 10, 15, 16, 11, 1, 17, 1, 1, 1]) (bs := [10, 6]) (W := 41344) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c3263_1 : P.sumLeaves 24 3341760 64 = 41344 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 52215) rows (by decide) (by decide)).symm.trans contract3263_1

theorem c3263_2 : P.sumLeaves 24 3341824 512 = 2513056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3263) (lo := 512) (len := 512) (W := 2513056) check rows elimOK (by decide) (by decide) cover3263 (by decide)
  decide +kernel

theorem h3263 : P.leaf 34 3263 = 2554400 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 41344), (512, 2513056)]) (.cons c3263_0 (.cons c3263_1 (.cons c3263_2 (.nil)))) (by decide) (by decide))

theorem cover3272 : P.CoversSplit 24 10 3272 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c3272_0 : P.sumLeaves 24 3350528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3272) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3272 (by decide)
  decide +kernel

theorem h3272 : P.leaf 34 3272 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3272_0 (.nil)) (by decide) (by decide))

theorem h3273 : P.leaf 34 3273 = 2232 := by
  exact leaf_contract_factors (k := 34) (b := 16) (H := 3273) (ss := [(30, 1, 466), (11, 1, 472), (18, 1, 475), (35, 14, 487), (33, 14, 536), (29, 15, 558), (32, 17, 565), (14, 1, 929), (15, 1, 474), (17, 1, 522), (27, 1, 473), (6, 1, 459), (26, 1, 515), (10, 1, 809), (12, 1, 817), (28, 1, 858), (34, 1, 915), (31, 1, 1209)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 14, 17, 18, 19, 20, 23, 21, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 1, 1, 10, 1, 1, 11, 12, 13, 14, 16, 17, 15, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [14, 2]) (W := 2232) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h3274 : P.leaf 34 3274 = 17312 := by
  exact leaf_contract_factors (k := 34) (b := 19) (H := 3274) (ss := [(32, 1, 466), (3, 1, 472), (30, 18, 524), (35, 1, 536), (18, 1, 566), (4, 1, 417), (11, 1, 879), (10, 1, 809), (12, 1, 901), (29, 1, 916), (28, 1, 858), (26, 1, 515), (27, 1, 522), (34, 1, 916), (31, 1, 1209)]) (ids := [0, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 17, 18, 19, 23, 31, 20, 21, 22]) (cs := [2, 1, 1, 3, 4, 5, 6, 7, 1, 1, 1, 8, 9, 10, 11, 12, 1, 13, 14, 15, 18, 19, 20, 16, 1, 1, 1, 1, 1, 1, 1, 17, 1, 1]) (bs := [16, 3]) (W := 17312) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover3275 : P.CoversSplit 24 10 3275 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem c3275_0 : P.sumLeaves 24 3353600 1024 = 119264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3275) (lo := 0) (len := 1024) (W := 119264) check rows elimOK (by decide) (by decide) cover3275 (by decide)
  decide +kernel

theorem h3275 : P.leaf 34 3275 = 119264 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 119264)]) (.cons c3275_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3180, 4), (3181, 4), (3182, 12), (3183, 12), (3198, 12), (3199, 12), (3236, 24), (3237, 24), (3238, 48), (3239, 48), (3240, 48), (3241, 48), (3242, 48), (3243, 48), (3244, 48), (3245, 48), (3246, 48), (3247, 48), (3254, 24), (3255, 24), (3256, 48), (3257, 48), (3258, 48), (3259, 48), (3260, 48), (3261, 48), (3262, 48), (3263, 48), (3272, 24), (3273, 24), (3274, 48), (3275, 48)]

theorem segOK : checkSeg 16 perms 3180 3276 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3180 3276 1160 352184116 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 352184116)
    (SegSum.cons (w := 4) h3180 (SegSum.cons (w := 4) h3181 (SegSum.cons (w := 12) h3182 (SegSum.cons (w := 12) h3183 (SegSum.cons (w := 12) h3198 (SegSum.cons (w := 12) h3199 (SegSum.cons (w := 24) h3236 (SegSum.cons (w := 24) h3237 (SegSum.cons (w := 48) h3238 (SegSum.cons (w := 48) h3239 (SegSum.cons (w := 48) h3240 (SegSum.cons (w := 48) h3241 (SegSum.cons (w := 48) h3242 (SegSum.cons (w := 48) h3243 (SegSum.cons (w := 48) h3244 (SegSum.cons (w := 48) h3245 (SegSum.cons (w := 48) h3246 (SegSum.cons (w := 48) h3247 (SegSum.cons (w := 24) h3254 (SegSum.cons (w := 24) h3255 (SegSum.cons (w := 48) h3256 (SegSum.cons (w := 48) h3257 (SegSum.cons (w := 48) h3258 (SegSum.cons (w := 48) h3259 (SegSum.cons (w := 48) h3260 (SegSum.cons (w := 48) h3261 (SegSum.cons (w := 48) h3262 (SegSum.cons (w := 48) h3263 (SegSum.cons (w := 24) h3272 (SegSum.cons (w := 24) h3273 (SegSum.cons (w := 48) h3274 (SegSum.cons (w := 48) h3275 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S18
