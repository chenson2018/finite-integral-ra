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

namespace RACert.S4N1.C0.S0

open RACert RACert.Problem

theorem cover0 : P.CoversSplit 24 10 0 0x900900000000dd0d0000000000000000900900000000dd0db0bb000000000000000000009009dd0db0bb0000b0bb0000000000000000dd0db0bb0000000000009009dd0d0000dd0d00000000000000009009dd0d0000dd0db0bb0000000000000000000000000000b0bb0000b0bb0000000000009009dd0db0bb0000b0bb0000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1208, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f0 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (0 + i)

theorem c0_0 : rowSum f0 0 1023 = 102258 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 0) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem c0_1 : rowSum f0 1023 1 = 2368 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 0) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem sum0 : rowSum f0 0 1024 = 104626 :=
  rowSum_append (F := f0) (lo := 0) (n := 1023) (m := 1) (A := 102258) (B := 2368) c0_0 (c0_1)

theorem h0 : P.leaf 34 0 = 104626 :=
  leaf_weighted (k := 24) (d := 10) (H := 0) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 0) (by decide) (by decide +kernel)) sum0

theorem cover1 : P.CoversSplit 24 10 1 0x800000000000cc000000000000000000800000000000cc000033000000000000000000008000cc000033000000330000000000000000cc0000330000000000008000cc000000cc0000000000000000008000cc000000cc00003300000000000000000000000000000033000000330000000000008000cc000033000000330000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 1208, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f1 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (1024 + i)

theorem c1_0 : rowSum f1 0 1024 = 26960 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover1 (by decide)
  decide +kernel

theorem sum1 : rowSum f1 0 1024 = 26960 :=
  c1_0

theorem h1 : P.leaf 34 1 = 26960 :=
  leaf_weighted (k := 24) (d := 10) (H := 1) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1) (by decide) (by decide +kernel)) sum1

theorem cover3 : P.CoversSplit 24 10 3 0x8001000000000000000000000000000080010000000000000021000000000000000000008001040100000000002100000000000000000401000000000000000080010401000000000000000000000000800104010000000000210000000000000000000000000000000000000021000000000000800104010000000000210000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 1209, 1217, 1258, 1609]) (ps := [(5, [467, 474], [467, 474])]) (by decide +kernel)

noncomputable def f3 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (3072 + i)

theorem c3_0 : rowSum f3 0 1024 = 6592 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover3 (by decide)
  decide +kernel

theorem sum3 : rowSum f3 0 1024 = 6592 :=
  c3_0

theorem h3 : P.leaf 34 3 = 6592 :=
  leaf_weighted (k := 24) (d := 10) (H := 3) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 3) (by decide) (by decide +kernel)) sum3

theorem cover4 : P.CoversSplit 24 10 4 0x800080000000040080000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 515, 516, 522, 572, 858, 860, 865, 916, 1208]) (by decide +kernel)

noncomputable def f4 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (4096 + i)

theorem c4_0 : rowSum f4 0 1024 = 11344 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 4) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover4 (by decide)
  decide +kernel

theorem sum4 : rowSum f4 0 1024 = 11344 :=
  c4_0

theorem h4 : P.leaf 34 4 = 11344 :=
  leaf_weighted (k := 24) (d := 10) (H := 4) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 4) (by decide) (by decide +kernel)) sum4

theorem cover5 : P.CoversSplit 24 10 5 0x80008400000004000000000000000000800084000000000000000000000000000000000000000000002100000001000000000000000000000021000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 475, 515, 516, 522, 572, 858, 860, 865, 1208]) (ps := [(5, [418], [468])]) (by decide +kernel)

theorem c5_0 : P.sumLeaves 24 5120 1024 = 4372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5) (lo := 0) (len := 1024) (W := 4372) check rows elimOK (by decide) (by decide) cover5 (by decide)
  decide +kernel

theorem h5 : P.leaf 34 5 = 4372 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4372)]) (.cons c5_0 (.nil)) (by decide) (by decide))

theorem cover7 : P.CoversSplit 24 10 7 0x8001000000000401000000000000000080010000000000000021000000000000000000000001000100210000000100000000000000000000002100000000000080010401000004010000000000000000800104010000000000210000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 572, 858, 865, 1209, 1217, 1258, 1609]) (ps := [(5, [418, 425], [468, 475])]) (by decide +kernel)

noncomputable def f7 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (7168 + i)

theorem c7_0 : rowSum f7 0 1024 = 4486 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover7 (by decide)
  decide +kernel

theorem sum7 : rowSum f7 0 1024 = 4486 :=
  c7_0

theorem h7 : P.leaf 34 7 = 4486 :=
  leaf_weighted (k := 24) (d := 10) (H := 7) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 7) (by decide) (by decide +kernel)) sum7

theorem cover12 : P.CoversSplit 24 10 12 0x8000000000000400000000000000000080000000000004008000000000000000000000000001000100200000000100000000000000000001002000000000000080008000000004000000000000000000800080000000040080000000000000000000000000000000002000000001000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 572, 858, 859, 865, 915, 1208, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f12 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (12288 + i)

theorem c12_0 : rowSum f12 0 1024 = 97192 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 12) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover12 (by decide)
  decide +kernel

theorem sum12 : rowSum f12 0 1024 = 97192 :=
  c12_0

theorem h12 : P.leaf 34 12 = 97192 :=
  leaf_weighted (k := 24) (d := 10) (H := 12) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 12) (by decide) (by decide +kernel)) sum12

theorem cover13 : P.CoversSplit 24 10 13 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000000100000000000000000000002100000000000080008400000004000000000000000000800084000000040000000000000000000000000000000000002100000001000000000000000000000021000000010000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 572, 858, 859, 865, 1208, 1209, 1217]) (ps := [(4, [480], [466])]) (by decide +kernel)

theorem c13_0 : P.sumLeaves 24 13312 1024 = 55956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 13) (lo := 0) (len := 1024) (W := 55956) check rows elimOK (by decide) (by decide) cover13 (by decide)
  decide +kernel

theorem h13 : P.leaf 34 13 = 55956 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 55956)]) (.cons c13_0 (.nil)) (by decide) (by decide))

theorem cover15 : P.CoversSplit 24 10 15 0x8001000000000401000000000000000080010000000004010021000000000000000000000001000100210000000100000000000000000001002100000000000080010401000004010000000000000000800104010000040100210000000000000000000000000000002100000001000000000000000100010021000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 572, 858, 865, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f15 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (15360 + i)

theorem c15_0 : rowSum f15 0 1024 = 62928 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15 (by decide)
  decide +kernel

theorem sum15 : rowSum f15 0 1024 = 62928 :=
  c15_0

theorem h15 : P.leaf 34 15 = 62928 :=
  leaf_weighted (k := 24) (d := 10) (H := 15) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 15) (by decide) (by decide +kernel)) sum15

theorem cover19 : P.CoversSplit 24 10 19 0xfff800000000000000000000000000008888000000000000000000000000000000000000fff8faf800000000ffc8fac80000000000005050000000000000504088880000000000000000000000000000fff8faf800000000ffc8fac8000000000000000000000000000000003300320000000000fff8faf800000000ffc8fac8 :=
  coversProjected check rows (by decide) (by decide) (xs := [529, 858, 865, 1209, 1217, 1258, 1609]) (ps := [(8, [531, 580], [516, 572, 1217, 1609]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem contract19_0 : P.leaf 30 304 = 6870 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 304) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (16, 1, 1216), (7, 1, 579), (18, 1, 579), (13, 1, 873), (17, 1, 1224), (9, 1, 587), (19, 1, 587), (15, 1, 881), (8, 0, 1266), (14, 0, 531)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 23, 24, 25, 26, 27, 28, 18, 19]) (cs := [2, 3, 4, 0, 5, 1, 0, 1, 6, 7, 0, 1, 0, 1, 1, 1, 1, 1, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0]) (bs := [15, 2]) (W := 6870) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c19_0 : P.sumLeaves 24 19456 64 = 6870 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 304) rows (by decide) (by decide)).symm.trans contract19_0

theorem contract19_1 : P.leaf 30 305 = 17601 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 305) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (16, 1, 1216), (7, 1, 579), (18, 1, 579), (13, 1, 873), (17, 1, 1224), (9, 1, 587), (19, 1, 587), (15, 1, 881), (8, 0, 1266), (14, 0, 531)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 23, 24, 25, 26, 27, 28, 18, 19]) (cs := [2, 3, 4, 0, 5, 1, 0, 1, 6, 7, 0, 1, 0, 1, 1, 1, 1, 1, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0]) (bs := [15, 2]) (W := 17601) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c19_1 : P.sumLeaves 24 19520 64 = 17601 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 305) rows (by decide) (by decide)).symm.trans contract19_1

theorem contract19_2 : P.leaf 30 306 = 0 := by
  exact leaf_contract_zero (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (8, 1, 580), (18, 1, 580), (19, 1, 586), (9, 7, 601), (14, 1, 923), (15, 13, 951), (17, 16, 1301), (27, 0, 1609), (10, 1, 865), (13, 1, 825), (7, 1, 579), (29, 1, 865), (16, 1, 1265)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19_2 : P.sumLeaves 24 19584 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 306) rows (by decide) (by decide)).symm.trans contract19_2

theorem c19_3 : P.sumLeaves 24 19648 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19) (lo := 192) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem contract19_4 : P.leaf 30 308 = 6870 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 308) (ss := [(31, 5, 467), (5, 1, 474), (12, 1, 479), (16, 0, 1258), (13, 0, 530), (18, 0, 530), (14, 0, 531), (7, 0, 873), (8, 0, 874), (17, 0, 1259), (15, 0, 538), (19, 0, 489), (9, 0, 881)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 23, 24, 25, 26, 27, 28, 18, 19]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 0, 0, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1]) (bs := [15, 2]) (W := 6870) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c19_4 : P.sumLeaves 24 19712 64 = 6870 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 308) rows (by decide) (by decide)).symm.trans contract19_4

theorem c19_5 : P.sumLeaves 24 19776 128 = 17635 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19) (lo := 320) (len := 128) (W := 17635) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem contract19_6 : P.leaf 30 311 = 32 := by
  exact leaf_contract_factors (k := 30) (b := 5) (H := 311) (ss := [(31, 5, 467), (5, 1, 474), (3, 1, 418), (12, 1, 479), (8, 1, 580), (6, 1, 460), (26, 1, 516), (27, 1, 572), (18, 1, 580), (4, 1, 426), (7, 1, 579), (19, 1, 586), (9, 1, 587), (10, 1, 810), (11, 1, 817), (13, 1, 922), (2, 1, 412), (28, 1, 859), (29, 1, 915), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [19, 20, 21, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 1, 1, 1, 1]) (bs := [0, 5]) (W := 32) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c19_6 : P.sumLeaves 24 19904 64 = 32 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 311) rows (by decide) (by decide)).symm.trans contract19_6

theorem c19_7 : P.sumLeaves 24 19968 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19) (lo := 512) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem contract19_8 : P.leaf 30 313 = 0 := by
  exact leaf_contract_zero (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (8, 1, 531), (16, 1, 531), (17, 1, 537), (9, 7, 601), (14, 1, 874), (15, 13, 951), (26, 0, 1217), (28, 0, 1217), (29, 1, 858), (30, 1, 858)]) (q := 1217) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19_8 : P.sumLeaves 24 20032 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 313) rows (by decide) (by decide)).symm.trans contract19_8

theorem c19_9 : P.sumLeaves 24 20096 192 = 25619 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19) (lo := 640) (len := 192) (W := 25619) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem contract19_10 : P.leaf 30 317 = 32 := by
  exact leaf_contract_factors (k := 30) (b := 5) (H := 317) (ss := [(31, 5, 467), (5, 1, 474), (4, 1, 425), (12, 1, 479), (8, 1, 531), (6, 1, 460), (26, 1, 516), (16, 1, 531), (3, 1, 419), (7, 1, 530), (17, 1, 537), (9, 1, 538), (27, 1, 572), (10, 1, 810), (11, 1, 817), (13, 1, 873), (2, 1, 412), (28, 1, 859), (14, 1, 874), (15, 1, 881), (29, 1, 915), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314)]) (ids := [19, 20, 21, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 1, 1, 1, 1, 1]) (bs := [0, 5]) (W := 32) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c19_10 : P.sumLeaves 24 20288 64 = 32 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 317) rows (by decide) (by decide)).symm.trans contract19_10

theorem c19_11 : P.sumLeaves 24 20352 128 = 512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19) (lo := 896) (len := 128) (W := 512) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem h19 : P.leaf 34 19 = 75171 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 6870), (64, 17601), (64, 0), (64, 0), (64, 6870), (128, 17635), (64, 32), (64, 0), (64, 0), (192, 25619), (64, 32), (128, 512)]) (.cons c19_0 (.cons c19_1 (.cons c19_2 (.cons c19_3 (.cons c19_4 (.cons c19_5 (.cons c19_6 (.cons c19_7 (.cons c19_8 (.cons c19_9 (.cons c19_10 (.cons c19_11 (.nil))))))))))))) (by decide) (by decide))

theorem cover20 : P.CoversSplit 24 10 20 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c20_0 : P.sumLeaves 24 20480 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover20 (by decide)
  decide +kernel

theorem h20 : P.leaf 34 20 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c20_0 (.nil)) (by decide) (by decide))

theorem cover21 : P.CoversSplit 24 10 21 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c21_0 : P.sumLeaves 24 21504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21 (by decide)
  decide +kernel

theorem h21 : P.leaf 34 21 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21_0 (.nil)) (by decide) (by decide))

theorem cover23 : P.CoversSplit 24 10 23 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c23_0 : P.sumLeaves 24 23552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23 (by decide)
  decide +kernel

theorem h23 : P.leaf 34 23 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23_0 (.nil)) (by decide) (by decide))

theorem cover28 : P.CoversSplit 24 10 28 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c28_0 : P.sumLeaves 24 28672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover28 (by decide)
  decide +kernel

theorem h28 : P.leaf 34 28 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c28_0 (.nil)) (by decide) (by decide))

theorem cover29 : P.CoversSplit 24 10 29 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c29_0 : P.sumLeaves 24 29696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 29) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover29 (by decide)
  decide +kernel

theorem h29 : P.leaf 34 29 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c29_0 (.nil)) (by decide) (by decide))

theorem cover31 : P.CoversSplit 24 10 31 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c31_0 : P.sumLeaves 24 31744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 31) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31 (by decide)
  decide +kernel

theorem h31 : P.leaf 34 31 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31_0 (.nil)) (by decide) (by decide))

theorem h36 : P.leaf 34 36 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (19, 11, 474), (35, 0, 475), (13, 2, 479), (18, 4, 487), (14, 0, 510), (16, 3, 486), (30, 11, 523), (11, 4, 558), (12, 1, 951), (6, 1, 458), (10, 1, 458)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover37 : P.CoversSplit 24 10 37 0x8000c0000000000000000000000000008000c0000000000000000000000000000000000000000000003000000000000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 517, 522, 572, 858, 859, 860, 865, 871, 1208]) (by decide +kernel)

theorem c37_0 : P.sumLeaves 24 37888 1024 = 15440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 37) (lo := 0) (len := 1024) (W := 15440) check rows elimOK (by decide) (by decide) cover37 (by decide)
  decide +kernel

theorem h37 : P.leaf 34 37 = 15440 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15440)]) (.cons c37_0 (.nil)) (by decide) (by decide))

theorem cover38 : P.CoversSplit 24 10 38 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem c38_0 : P.sumLeaves 24 38912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 38) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover38 (by decide)
  decide +kernel

theorem h38 : P.leaf 34 38 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c38_0 (.nil)) (by decide) (by decide))

theorem cover39 : P.CoversSplit 24 10 39 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem c39_0 : P.sumLeaves 24 39936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 39) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover39 (by decide)
  decide +kernel

theorem h39 : P.leaf 34 39 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c39_0 (.nil)) (by decide) (by decide))

theorem cover40 : P.CoversSplit 24 10 40 0x80008000000040000000000000000000000000000000000000000000000000000000000000000000002000000010000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 467, 473, 474, 515, 517, 522, 572, 573, 858, 859, 915, 1208, 1301]) (ps := [(14, [880], [486])]) (by decide +kernel)

theorem c40_0 : P.sumLeaves 24 40960 1024 = 2536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 40) (lo := 0) (len := 1024) (W := 2536) check rows elimOK (by decide) (by decide) cover40 (by decide)
  decide +kernel

theorem h40 : P.leaf 34 40 = 2536 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2536)]) (.cons c40_0 (.nil)) (by decide) (by decide))

theorem cover41 : P.CoversSplit 24 10 41 0x8000c000000000000000000000000000800080000000000000000000000000000000000000000000003000000000000000000000000000000020000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 474, 515, 517, 522, 572, 858, 859, 865, 871, 1208]) (by decide +kernel)

theorem c41_0 : P.sumLeaves 24 41984 1024 = 24800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 41) (lo := 0) (len := 1024) (W := 24800) check rows elimOK (by decide) (by decide) cover41 (by decide)
  decide +kernel

theorem h41 : P.leaf 34 41 = 24800 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24800)]) (.cons c41_0 (.nil)) (by decide) (by decide))

theorem cover42 : P.CoversSplit 24 10 42 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem c42_0 : P.sumLeaves 24 43008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 42) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover42 (by decide)
  decide +kernel

theorem h42 : P.leaf 34 42 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c42_0 (.nil)) (by decide) (by decide))

theorem cover43 : P.CoversSplit 24 10 43 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem c43_0 : P.sumLeaves 24 44032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 43) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover43 (by decide)
  decide +kernel

theorem h43 : P.leaf 34 43 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c43_0 (.nil)) (by decide) (by decide))

theorem cover44 : P.CoversSplit 24 10 44 0x80008000000040000000000000000000800080000000000000000000000000000000000000000000002000000010000000000000000000000020000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 524, 572, 858, 859, 915, 1208, 1301]) (by decide +kernel)

theorem c44_0 : P.sumLeaves 24 45056 1024 = 14376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 44) (lo := 0) (len := 1024) (W := 14376) check rows elimOK (by decide) (by decide) cover44 (by decide)
  decide +kernel

theorem h44 : P.leaf 34 44 = 14376 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14376)]) (.cons c44_0 (.nil)) (by decide) (by decide))

theorem cover45 : P.CoversSplit 24 10 45 0x8000c000000000000000000000000000800080000000000000000000000000000000000000000000003000000000000000000000000000000020000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 572, 858, 859, 860, 865, 871, 1208]) (by decide +kernel)

theorem c45_0 : P.sumLeaves 24 46080 1024 = 148024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 45) (lo := 0) (len := 1024) (W := 148024) check rows elimOK (by decide) (by decide) cover45 (by decide)
  decide +kernel

theorem h45 : P.leaf 34 45 = 148024 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 148024)]) (.cons c45_0 (.nil)) (by decide) (by decide))

theorem cover46 : P.CoversSplit 24 10 46 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem c46_0 : P.sumLeaves 24 47104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 46) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover46 (by decide)
  decide +kernel

theorem h46 : P.leaf 34 46 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c46_0 (.nil)) (by decide) (by decide))

theorem cover47 : P.CoversSplit 24 10 47 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem c47_0 : P.sumLeaves 24 48128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 47) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover47 (by decide)
  decide +kernel

theorem h47 : P.leaf 34 47 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c47_0 (.nil)) (by decide) (by decide))

theorem cover54 : P.CoversSplit 24 10 54 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c54_0 : P.sumLeaves 24 55296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 54) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover54 (by decide)
  decide +kernel

theorem h54 : P.leaf 34 54 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c54_0 (.nil)) (by decide) (by decide))

theorem cover55 : P.CoversSplit 24 10 55 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c55_0 : P.sumLeaves 24 56320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 55) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover55 (by decide)
  decide +kernel

theorem h55 : P.leaf 34 55 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c55_0 (.nil)) (by decide) (by decide))

theorem cover58 : P.CoversSplit 24 10 58 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c58_0 : P.sumLeaves 24 59392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 58) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover58 (by decide)
  decide +kernel

theorem h58 : P.leaf 34 58 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c58_0 (.nil)) (by decide) (by decide))

theorem cover59 : P.CoversSplit 24 10 59 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c59_0 : P.sumLeaves 24 60416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 59) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover59 (by decide)
  decide +kernel

theorem h59 : P.leaf 34 59 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c59_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(0, 1), (1, 4), (3, 6), (4, 12), (5, 24), (7, 12), (12, 6), (13, 12), (15, 6), (19, 4), (20, 24), (21, 48), (23, 24), (28, 12), (29, 24), (31, 12), (36, 24), (37, 24), (38, 48), (39, 48), (40, 24), (41, 24), (42, 48), (43, 48), (44, 48), (45, 48), (46, 48), (47, 48), (54, 24), (55, 24), (58, 24), (59, 24)]

theorem segOK : checkSeg 16 perms 0 60 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 0 60 807 11301606 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11301606)
    (SegSum.cons (w := 1) h0 (SegSum.cons (w := 4) h1 (SegSum.cons (w := 6) h3 (SegSum.cons (w := 12) h4 (SegSum.cons (w := 24) h5 (SegSum.cons (w := 12) h7 (SegSum.cons (w := 6) h12 (SegSum.cons (w := 12) h13 (SegSum.cons (w := 6) h15 (SegSum.cons (w := 4) h19 (SegSum.cons (w := 24) h20 (SegSum.cons (w := 48) h21 (SegSum.cons (w := 24) h23 (SegSum.cons (w := 12) h28 (SegSum.cons (w := 24) h29 (SegSum.cons (w := 12) h31 (SegSum.cons (w := 24) h36 (SegSum.cons (w := 24) h37 (SegSum.cons (w := 48) h38 (SegSum.cons (w := 48) h39 (SegSum.cons (w := 24) h40 (SegSum.cons (w := 24) h41 (SegSum.cons (w := 48) h42 (SegSum.cons (w := 48) h43 (SegSum.cons (w := 48) h44 (SegSum.cons (w := 48) h45 (SegSum.cons (w := 48) h46 (SegSum.cons (w := 48) h47 (SegSum.cons (w := 24) h54 (SegSum.cons (w := 24) h55 (SegSum.cons (w := 24) h58 (SegSum.cons (w := 24) h59 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S0
