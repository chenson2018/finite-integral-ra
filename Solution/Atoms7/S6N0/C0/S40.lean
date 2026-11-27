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

namespace RACert.S6N0.C0.S40

open RACert RACert.Problem

theorem cover77165 : P.CoversSplit 26 10 77165 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77165_0 : P.sumLeaves 26 79016960 1024 = 34712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77165) (lo := 0) (len := 1024) (W := 34712) check rows elimOK (by decide) (by decide) cover77165 (by decide)
  decide +kernel

theorem h77165 : P.leaf 36 77165 = 34712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34712)]) (.cons c77165_0 (.nil)) (by decide) (by decide))

theorem cover77166 : P.CoversSplit 26 10 77166 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77166_0 : P.sumLeaves 26 79017984 1024 = 75888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77166) (lo := 0) (len := 1024) (W := 75888) check rows elimOK (by decide) (by decide) cover77166 (by decide)
  decide +kernel

theorem h77166 : P.leaf 36 77166 = 75888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 75888)]) (.cons c77166_0 (.nil)) (by decide) (by decide))

theorem cover77167 : P.CoversSplit 26 10 77167 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77167_0 : P.sumLeaves 26 79019008 1024 = 287230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77167) (lo := 0) (len := 1024) (W := 287230) check rows elimOK (by decide) (by decide) cover77167 (by decide)
  decide +kernel

theorem h77167 : P.leaf 36 77167 = 287230 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 287230)]) (.cons c77167_0 (.nil)) (by decide) (by decide))

theorem cover77182 : P.CoversSplit 26 10 77182 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77182_0 : P.sumLeaves 26 79034368 1024 = 371608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77182) (lo := 0) (len := 1024) (W := 371608) check rows elimOK (by decide) (by decide) cover77182 (by decide)
  decide +kernel

theorem h77182 : P.leaf 36 77182 = 371608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 371608)]) (.cons c77182_0 (.nil)) (by decide) (by decide))

theorem cover77183 : P.CoversSplit 26 10 77183 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77183_0 : P.sumLeaves 26 79035392 1024 = 1827836 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77183) (lo := 0) (len := 1024) (W := 1827836) check rows elimOK (by decide) (by decide) cover77183 (by decide)
  decide +kernel

theorem h77183 : P.leaf 36 77183 = 1827836 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1827836)]) (.cons c77183_0 (.nil)) (by decide) (by decide))

theorem cover77292 : P.CoversSplit 26 10 77292 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77292_0 : P.sumLeaves 26 79147008 1024 = 125498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77292) (lo := 0) (len := 1024) (W := 125498) check rows elimOK (by decide) (by decide) cover77292 (by decide)
  decide +kernel

theorem h77292 : P.leaf 36 77292 = 125498 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 125498)]) (.cons c77292_0 (.nil)) (by decide) (by decide))

theorem cover77293 : P.CoversSplit 26 10 77293 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77293_0 : P.sumLeaves 26 79148032 1024 = 315830 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77293) (lo := 0) (len := 1024) (W := 315830) check rows elimOK (by decide) (by decide) cover77293 (by decide)
  decide +kernel

theorem h77293 : P.leaf 36 77293 = 315830 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 315830)]) (.cons c77293_0 (.nil)) (by decide) (by decide))

theorem cover77295 : P.CoversSplit 26 10 77295 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77295_0 : P.sumLeaves 26 79150080 1024 = 1234078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77295) (lo := 0) (len := 1024) (W := 1234078) check rows elimOK (by decide) (by decide) cover77295 (by decide)
  decide +kernel

theorem h77295 : P.leaf 36 77295 = 1234078 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1234078)]) (.cons c77295_0 (.nil)) (by decide) (by decide))

theorem cover77311 : P.CoversSplit 26 10 77311 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77311_0 : P.sumLeaves 26 79166464 1024 = 6888880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77311) (lo := 0) (len := 1024) (W := 6888880) check rows elimOK (by decide) (by decide) cover77311 (by decide)
  decide +kernel

theorem h77311 : P.leaf 36 77311 = 6888880 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6888880)]) (.cons c77311_0 (.nil)) (by decide) (by decide))

theorem cover77640 : P.CoversSplit 26 10 77640 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000005555555555555555555555555555555555555555555055005555555555005500a0a00000a0a000000000000000000000a0a00000a000000000000000000000005555555555555555555555555555555555555555550055005555555555005500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 972, 979, 1322, 1665]) (by decide +kernel)

noncomputable def f77640 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (79503360 + i)

theorem c77640_0 : rowSum f77640 0 564 = 507228 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77640) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77640 (by decide)
  decide +kernel

theorem c77640_1 : rowSum f77640 564 460 = 1570105 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77640) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77640 (by decide)
  decide +kernel

theorem sum77640 : rowSum f77640 0 1024 = 2077333 :=
  rowSum_append (F := f77640) (lo := 0) (n := 564) (m := 460) (A := 507228) (B := 1570105) c77640_0 (c77640_1)

theorem h77640 : P.leaf 36 77640 = 2077333 :=
  leaf_weighted (k := 26) (d := 10) (H := 77640) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 77640) (by decide) (by decide +kernel)) sum77640

theorem cover77641 : P.CoversSplit 26 10 77641 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 579, 881, 930, 972]) (by decide +kernel)

theorem c77641_0 : P.sumLeaves 26 79504384 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77641) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover77641 (by decide)
  decide +kernel

theorem contract77641_1 : P.leaf 32 1242261 = 14336 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1242261) (ss := [(28, 1, 474), (2, 1, 475), (9, 1, 480), (15, 1, 473), (30, 1, 481), (19, 1, 522), (3, 1, 524), (32, 1, 530), (4, 1, 580), (5, 1, 586), (20, 1, 572), (13, 1, 867), (18, 1, 879), (21, 1, 916)]) (ids := [4, 5, 6, 8, 9, 10, 12, 14, 15, 21, 22, 25, 27, 29, 31, 20, 23, 24]) (cs := [1, 1, 1, 1, 2, 3, 4, 1, 5, 6, 7, 1, 8, 1, 9, 10, 1, 1, 1, 1, 17, 11, 12, 18, 19, 13, 1, 14, 1, 15, 1, 16]) (bs := [15, 3]) (W := 14336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77641_1 : P.sumLeaves 26 79504704 64 = 14336 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242261) rows (by decide) (by decide)).symm.trans contract77641_1

theorem c77641_2 : P.sumLeaves 26 79504768 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77641) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover77641 (by decide)
  decide +kernel

theorem contract77641_3 : P.leaf 32 1242263 = 15552 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1242263) (ss := [(28, 1, 474), (9, 1, 480), (30, 1, 481), (2, 1, 482), (15, 1, 473), (19, 1, 522), (32, 1, 530), (3, 1, 531), (4, 1, 580), (13, 1, 867), (11, 1, 818), (18, 1, 879), (21, 1, 916), (20, 1, 572), (16, 1, 1210)]) (ids := [3, 5, 6, 8, 10, 12, 15, 20, 25, 27, 29, 31, 4, 21, 22, 23, 24]) (cs := [1, 1, 1, 2, 14, 3, 4, 1, 5, 1, 6, 1, 7, 1, 1, 8, 1, 1, 1, 1, 9, 15, 16, 17, 18, 10, 1, 11, 1, 12, 1, 13]) (bs := [12, 5]) (W := 15552) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77641_3 : P.sumLeaves 26 79504832 64 = 15552 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242263) rows (by decide) (by decide)).symm.trans contract77641_3

theorem c77641_4 : P.sumLeaves 26 79504896 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77641) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover77641 (by decide)
  decide +kernel

theorem contract77641_5 : P.leaf 32 1242269 = 15552 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1242269) (ss := [(28, 1, 474), (2, 1, 475), (9, 1, 480), (15, 1, 473), (30, 1, 481), (19, 1, 522), (3, 1, 524), (32, 1, 530), (5, 1, 586), (20, 1, 572), (13, 1, 867), (12, 1, 825), (18, 1, 879), (21, 1, 916), (17, 1, 1217)]) (ids := [2, 5, 6, 8, 9, 12, 14, 20, 25, 27, 29, 31, 4, 21, 22, 23, 24]) (cs := [1, 1, 2, 1, 14, 3, 4, 1, 5, 6, 1, 1, 7, 1, 8, 1, 1, 1, 1, 1, 9, 15, 16, 17, 18, 10, 1, 11, 1, 12, 1, 13]) (bs := [12, 5]) (W := 15552) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77641_5 : P.sumLeaves 26 79505216 64 = 15552 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242269) rows (by decide) (by decide)).symm.trans contract77641_5

theorem c77641_6 : P.sumLeaves 26 79505280 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77641) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover77641 (by decide)
  decide +kernel

theorem contract77641_7 : P.leaf 32 1242271 = 45696 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1242271) (ss := [(28, 1, 474), (9, 1, 480), (30, 1, 481), (32, 1, 530), (13, 1, 867), (11, 1, 818), (12, 1, 825), (18, 1, 879), (15, 1, 916), (19, 1, 522), (21, 1, 916), (20, 1, 572), (16, 1, 1210), (17, 1, 1217)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 12, 20, 25, 27, 29, 31, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 1, 1, 1, 10, 1, 1, 1, 1, 1, 1, 1, 11, 16, 17, 18, 19, 12, 1, 13, 1, 14, 1, 15]) (bs := [14, 4]) (W := 45696) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77641_7 : P.sumLeaves 26 79505344 64 = 45696 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242271) rows (by decide) (by decide)).symm.trans contract77641_7

theorem h77641 : P.leaf 36 77641 = 91136 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 14336), (64, 0), (64, 15552), (320, 0), (64, 15552), (64, 0), (64, 45696)]) (.cons c77641_0 (.cons c77641_1 (.cons c77641_2 (.cons c77641_3 (.cons c77641_4 (.cons c77641_5 (.cons c77641_6 (.cons c77641_7 (.nil))))))))) (by decide) (by decide))

theorem cover77643 : P.CoversSplit 26 10 77643 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 881, 972, 979]) (by decide +kernel)

theorem c77643_0 : P.sumLeaves 26 79506432 832 = 288368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77643) (lo := 0) (len := 832) (W := 288368) check rows elimOK (by decide) (by decide) cover77643 (by decide)
  decide +kernel

theorem contract77643_1 : P.leaf 32 1242301 = 195392 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1242301) (ss := [(28, 1, 481), (30, 1, 481), (3, 1, 524), (32, 1, 530), (5, 1, 586), (13, 1, 867), (12, 1, 825), (18, 1, 880), (21, 1, 929), (17, 1, 1217), (20, 1, 1609)]) (ids := [0, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 17, 20, 25, 27, 29, 31, 21, 22, 23, 24]) (cs := [2, 1, 3, 1, 4, 5, 6, 7, 8, 9, 1, 1, 10, 11, 12, 1, 1, 13, 1, 1, 14, 19, 20, 21, 22, 15, 1, 16, 1, 17, 1, 18]) (bs := [17, 4]) (W := 195392) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77643_1 : P.sumLeaves 26 79507264 64 = 195392 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242301) rows (by decide) (by decide)).symm.trans contract77643_1

theorem c77643_2 : P.sumLeaves 26 79507328 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77643) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover77643 (by decide)
  decide +kernel

theorem contract77643_3 : P.leaf 32 1242303 = 369280 := by
  exact leaf_contract_factors (k := 32) (b := 22) (H := 1242303) (ss := [(28, 1, 481), (30, 1, 481), (32, 1, 530), (13, 1, 867), (12, 1, 825), (18, 1, 880), (21, 1, 929), (16, 1, 1210), (17, 1, 1217), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 17, 20, 25, 27, 29, 31, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 1, 12, 13, 1, 1, 1, 14, 1, 1, 15, 20, 21, 22, 23, 16, 1, 17, 1, 18, 1, 19]) (bs := [18, 4]) (W := 369280) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77643_3 : P.sumLeaves 26 79507392 64 = 369280 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242303) rows (by decide) (by decide)).symm.trans contract77643_3

theorem h77643 : P.leaf 36 77643 = 853040 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 288368), (64, 195392), (64, 0), (64, 369280)]) (.cons c77643_0 (.cons c77643_1 (.cons c77643_2 (.cons c77643_3 (.nil))))) (by decide) (by decide))

theorem cover77647 : P.CoversSplit 26 10 77647 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055005050505050505050505050505050505050505050505050005050505050005000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055005050505050505050505050505050505050505050500050005050505050005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f77647 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (79510528 + i)

theorem c77647_0 : rowSum f77647 0 596 = 4340622 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77647 (by decide)
  decide +kernel

theorem c77647_1 : rowSum f77647 596 428 = 5084051 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77647) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77647 (by decide)
  decide +kernel

theorem sum77647 : rowSum f77647 0 1024 = 9424673 :=
  rowSum_append (F := f77647) (lo := 0) (n := 596) (m := 428) (A := 4340622) (B := 5084051) c77647_0 (c77647_1)

theorem h77647 : P.leaf 36 77647 = 9424673 :=
  leaf_weighted (k := 26) (d := 10) (H := 77647) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 77647) (by decide) (by decide +kernel)) sum77647

theorem cover77659 : P.CoversSplit 26 10 77659 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000005050000050500000000000000000000050500000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 881, 972, 979]) (by decide +kernel)

theorem contract77659_0 : P.leaf 32 1242544 = 7116 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1242544) (ss := [(2, 1, 482), (3, 1, 531), (30, 0, 579), (28, 0, 481), (5, 1, 467), (32, 0, 481), (4, 1, 580), (26, 1, 629), (13, 1, 874), (12, 7, 825), (18, 1, 880), (21, 1, 929), (17, 8, 1217), (20, 9, 1609)]) (ids := [4, 5, 6, 7, 8, 9, 12, 13, 14, 17, 20, 21, 22, 23, 25, 27, 29, 31]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 3, 1, 8, 9, 10, 4, 1, 11, 5, 1, 12, 13, 14, 15, 1, 16, 0, 17, 0, 18, 0, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c77659_0 : P.sumLeaves 26 79522816 64 = 7116 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242544) rows (by decide) (by decide)).symm.trans contract77659_0

theorem c77659_1 : P.sumLeaves 26 79522880 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77659) (lo := 64) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover77659 (by decide)
  decide +kernel

theorem contract77659_2 : P.leaf 32 1242546 = 14934 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1242546) (ss := [(2, 1, 482), (3, 1, 531), (30, 0, 579), (28, 0, 481), (5, 1, 467), (32, 0, 481), (4, 1, 580), (26, 1, 629), (13, 1, 874), (12, 7, 825), (18, 1, 880), (21, 1, 929), (17, 8, 1217), (20, 9, 1609)]) (ids := [4, 5, 6, 7, 8, 9, 12, 13, 14, 17, 20, 21, 22, 23, 25, 27, 29, 31]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 3, 1, 8, 9, 10, 4, 1, 11, 5, 1, 12, 13, 14, 15, 1, 16, 0, 17, 0, 18, 0, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c77659_2 : P.sumLeaves 26 79522944 64 = 14934 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242546) rows (by decide) (by decide)).symm.trans contract77659_2

theorem c77659_3 : P.sumLeaves 26 79523008 640 = 1223265 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77659) (lo := 192) (len := 640) (W := 1223265) check rows elimOK (by decide) (by decide) cover77659 (by decide)
  decide +kernel

theorem contract77659_4 : P.leaf 32 1242557 = 658624 := by
  exact leaf_contract_factors (k := 32) (b := 22) (H := 1242557) (ss := [(28, 1, 481), (30, 1, 481), (32, 1, 530), (5, 1, 586), (13, 1, 874), (12, 1, 825), (18, 1, 880), (21, 1, 929), (17, 1, 1217), (20, 1, 1609)]) (ids := [0, 1, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 17, 20, 25, 27, 29, 31, 21, 22, 23, 24]) (cs := [2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 1, 1, 11, 12, 13, 1, 1, 14, 1, 1, 15, 20, 21, 22, 23, 16, 1, 17, 1, 18, 1, 19]) (bs := [18, 4]) (W := 658624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c77659_4 : P.sumLeaves 26 79523648 64 = 658624 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1242557) rows (by decide) (by decide)).symm.trans contract77659_4

theorem c77659_5 : P.sumLeaves 26 79523712 128 = 1943552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77659) (lo := 896) (len := 128) (W := 1943552) check rows elimOK (by decide) (by decide) cover77659 (by decide)
  decide +kernel

theorem h77659 : P.leaf 36 77659 = 3847491 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 7116), (64, 0), (64, 14934), (640, 1223265), (64, 658624), (128, 1943552)]) (.cons c77659_0 (.cons c77659_1 (.cons c77659_2 (.cons c77659_3 (.cons c77659_4 (.cons c77659_5 (.nil))))))) (by decide) (by decide))

theorem cover77660 : P.CoversSplit 26 10 77660 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055000000000000000000000000000000000000000000000000000000000000000000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f77660 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (79523840 + i)

theorem c77660_0 : rowSum f77660 0 1015 = 1068320 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77660) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77660 (by decide)
  decide +kernel

theorem c77660_1 : rowSum f77660 1015 9 = 382064 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77660) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77660 (by decide)
  decide +kernel

theorem sum77660 : rowSum f77660 0 1024 = 1450384 :=
  rowSum_append (F := f77660) (lo := 0) (n := 1015) (m := 9) (A := 1068320) (B := 382064) c77660_0 (c77660_1)

theorem h77660 : P.leaf 36 77660 = 1450384 :=
  leaf_weighted (k := 26) (d := 10) (H := 77660) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 77660) (by decide) (by decide +kernel)) sum77660

theorem cover77661 : P.CoversSplit 26 10 77661 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055000000000000000000000000000000000000000000000000000000000000000000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 929, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77661_0 : P.sumLeaves 26 79524864 855 = 2448108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77661) (lo := 0) (len := 855) (W := 2448108) check rows elimOK (by decide) (by decide) cover77661 (by decide)
  decide +kernel

theorem c77661_1 : P.sumLeaves 26 79525719 169 = 4026136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77661) (lo := 855) (len := 169) (W := 4026136) check rows elimOK (by decide) (by decide) cover77661 (by decide)
  decide +kernel

theorem h77661 : P.leaf 36 77661 = 6474244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(855, 2448108), (169, 4026136)]) (.cons c77661_0 (.cons c77661_1 (.nil))) (by decide) (by decide))

theorem cover77663 : P.CoversSplit 26 10 77663 0xfffa0000fffa55500000000000000000fffa0000fff8550055500000550055000000000000000000000050500000505000000000000000000000505000005000fffa0000fffa55500000000000000000fffa0000ff00550055500000550055000000000000000000000050500000505000000000000000000000505000005000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 881, 972, 979, 1315, 1322, 1658, 1665]) (ps := [(18, [1266], [1315]), (21, [1272], [1658])]) (by decide +kernel)

noncomputable def f77663 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (79526912 + i)

theorem c77663_0 : rowSum f77663 0 863 = 13282980 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77663 (by decide)
  decide +kernel

theorem c77663_1 : rowSum f77663 863 161 = 14543384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77663) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77663 (by decide)
  decide +kernel

theorem sum77663 : rowSum f77663 0 1024 = 27826364 :=
  rowSum_append (F := f77663) (lo := 0) (n := 863) (m := 161) (A := 13282980) (B := 14543384) c77663_0 (c77663_1)

theorem h77663 : P.leaf 36 77663 = 27826364 :=
  leaf_weighted (k := 26) (d := 10) (H := 77663) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 77663) (by decide) (by decide +kernel)) sum77663

theorem cover77694 : P.CoversSplit 26 10 77694 0xfffafffafffaaaaa0000000000000000fffafffafff8aa8855505550550000000000000000000000000000000000000000000000000000000000000000000000fffafffafffaaaaa0000000000000000fffafffaff00aa0055505550550000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f77694 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (79558656 + i)

theorem c77694_0 : rowSum f77694 0 874 = 10754824 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77694) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover77694 (by decide)
  decide +kernel

theorem c77694_1 : rowSum f77694 874 150 = 18137744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77694) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover77694 (by decide)
  decide +kernel

theorem sum77694 : rowSum f77694 0 1024 = 28892568 :=
  rowSum_append (F := f77694) (lo := 0) (n := 874) (m := 150) (A := 10754824) (B := 18137744) c77694_0 (c77694_1)

theorem h77694 : P.leaf 36 77694 = 28892568 :=
  leaf_weighted (k := 26) (d := 10) (H := 77694) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 77694) (by decide) (by decide +kernel)) sum77694

theorem cover77695 : P.CoversSplit 26 10 77695 0xfffafffafffaaaaa0000000000000000fffafffafff8aa8855505550550000005050000050500000505000005050000050500000505000005050000050000000fffafffafffaaaaa0000000000000000fffafffaff00aa0055505550550000005050000050500000505000005050000050500000500000005050000050000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f77695 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (79559680 + i)

theorem c77695_0 : rowSum f77695 0 660 = 31100602 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77695) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover77695 (by decide)
  decide +kernel

theorem c77695_1 : rowSum f77695 660 364 = 84113124 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77695) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover77695 (by decide)
  decide +kernel

theorem sum77695 : rowSum f77695 0 1024 = 115213726 :=
  rowSum_append (F := f77695) (lo := 0) (n := 660) (m := 364) (A := 31100602) (B := 84113124) c77695_0 (c77695_1)

theorem h77695 : P.leaf 36 77695 = 115213726 :=
  leaf_weighted (k := 26) (d := 10) (H := 77695) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 77695) (by decide) (by decide +kernel)) sum77695

theorem cover77823 : P.CoversSplit 26 10 77823 0xfffafffafffaaaaafffafffafffaaaaafffafffafff8aa88aaaaaaaaaa88aa88fafaaaaafafaaaaaaaaaaaaaaaaaaaaafafaaaaafaf8aa88aaaaaaaaaa88aa88fffafffafffaaaaafffafffafffaaaaafffafffaffc8aa88aaaaaaaaaa88aa88fafaaaaafafaaaaaaaaaaaaaaaaaaaaafafaaaaafac8aa88aaaaaaaaaa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f77823 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (79690752 + i)

theorem c77823_0 : rowSum f77823 0 287 = 23276038 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_1 : rowSum f77823 287 223 = 374503408 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_2 : rowSum f77823 510 281 = 476065776 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_3 : rowSum f77823 791 225 = 678947958 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_4 : rowSum f77823 1016 8 = 102550166 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 77823) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem sum77823 : rowSum f77823 0 1024 = 1655343346 :=
  rowSum_append (F := f77823) (lo := 0) (n := 287) (m := 737) (A := 23276038) (B := 1632067308) c77823_0 (rowSum_append (F := f77823) (lo := 287) (n := 223) (m := 514) (A := 374503408) (B := 1257563900) c77823_1 (rowSum_append (F := f77823) (lo := 510) (n := 281) (m := 233) (A := 476065776) (B := 781498124) c77823_2 (rowSum_append (F := f77823) (lo := 791) (n := 225) (m := 8) (A := 678947958) (B := 102550166) c77823_3 (c77823_4))))

theorem h77823 : P.leaf 36 77823 = 1655343346 :=
  leaf_weighted (k := 26) (d := 10) (H := 77823) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 77823) (by decide) (by decide +kernel)) sum77823

def seg : List (ℕ × ℕ) := [(77165, 360), (77166, 720), (77167, 720), (77182, 360), (77183, 360), (77292, 120), (77293, 360), (77295, 360), (77311, 120), (77640, 15), (77641, 180), (77643, 360), (77647, 120), (77659, 120), (77660, 90), (77661, 360), (77663, 360), (77694, 90), (77695, 180), (77823, 30)]

theorem segOK : checkSeg 20 perms 77165 78030 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 77165 78030 5385 89890607535 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 89890607535)
    (SegSum.cons (w := 360) h77165 (SegSum.cons (w := 720) h77166 (SegSum.cons (w := 720) h77167 (SegSum.cons (w := 360) h77182 (SegSum.cons (w := 360) h77183 (SegSum.cons (w := 120) h77292 (SegSum.cons (w := 360) h77293 (SegSum.cons (w := 360) h77295 (SegSum.cons (w := 120) h77311 (SegSum.cons (w := 15) h77640 (SegSum.cons (w := 180) h77641 (SegSum.cons (w := 360) h77643 (SegSum.cons (w := 120) h77647 (SegSum.cons (w := 120) h77659 (SegSum.cons (w := 90) h77660 (SegSum.cons (w := 360) h77661 (SegSum.cons (w := 360) h77663 (SegSum.cons (w := 90) h77694 (SegSum.cons (w := 180) h77695 (SegSum.cons (w := 30) h77823 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S40
