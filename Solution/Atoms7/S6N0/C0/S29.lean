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

namespace RACert.S6N0.C0.S29

open RACert RACert.Problem

theorem cover14305 : P.CoversSplit 26 10 14305 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14305_0 : P.sumLeaves 26 14648320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14305) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14305 (by decide)
  decide +kernel

theorem h14305 : P.leaf 36 14305 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14305_0 (.nil)) (by decide) (by decide))

theorem cover14307 : P.CoversSplit 26 10 14307 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14307_0 : P.sumLeaves 26 14650368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14307) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14307 (by decide)
  decide +kernel

theorem h14307 : P.leaf 36 14307 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14307_0 (.nil)) (by decide) (by decide))

theorem cover14308 : P.CoversSplit 26 10 14308 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14308_0 : P.sumLeaves 26 14651392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14308) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14308 (by decide)
  decide +kernel

theorem h14308 : P.leaf 36 14308 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14308_0 (.nil)) (by decide) (by decide))

theorem cover14309 : P.CoversSplit 26 10 14309 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14309_0 : P.sumLeaves 26 14652416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14309) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14309 (by decide)
  decide +kernel

theorem h14309 : P.leaf 36 14309 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14309_0 (.nil)) (by decide) (by decide))

theorem cover14310 : P.CoversSplit 26 10 14310 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14310_0 : P.sumLeaves 26 14653440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14310) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14310 (by decide)
  decide +kernel

theorem h14310 : P.leaf 36 14310 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14310_0 (.nil)) (by decide) (by decide))

theorem cover14311 : P.CoversSplit 26 10 14311 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14311_0 : P.sumLeaves 26 14654464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14311) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14311 (by decide)
  decide +kernel

theorem h14311 : P.leaf 36 14311 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14311_0 (.nil)) (by decide) (by decide))

theorem cover14316 : P.CoversSplit 26 10 14316 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14316_0 : P.sumLeaves 26 14659584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14316) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14316 (by decide)
  decide +kernel

theorem h14316 : P.leaf 36 14316 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14316_0 (.nil)) (by decide) (by decide))

theorem cover14317 : P.CoversSplit 26 10 14317 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14317_0 : P.sumLeaves 26 14660608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14317) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14317 (by decide)
  decide +kernel

theorem h14317 : P.leaf 36 14317 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14317_0 (.nil)) (by decide) (by decide))

theorem cover14319 : P.CoversSplit 26 10 14319 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14319_0 : P.sumLeaves 26 14662656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14319) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14319 (by decide)
  decide +kernel

theorem h14319 : P.leaf 36 14319 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14319_0 (.nil)) (by decide) (by decide))

theorem cover14320 : P.CoversSplit 26 10 14320 0xf0000000f0000000f0000000f00000000000000000000000000000000000000000000000000000000000aa0000008800000000000000000000000000000000000000000000000000000000000000000000000000c0c0000000000000808000000000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (by decide +kernel)

theorem contract14320_0 : P.leaf 32 229120 = 0 := by
  exact leaf_contract_zero (ss := [(22, 1, 433), (2, 1, 467), (17, 0, 874), (16, 0, 859), (21, 13, 867), (12, 0, 880), (10, 0, 460), (11, 0, 458), (13, 0, 458), (5, 4, 586), (7, 1, 810), (3, 0, 458), (4, 0, 409), (6, 0, 409), (20, 19, 523), (19, 0, 524), (18, 0, 515), (24, 0, 515), (32, 0, 516), (33, 0, 517), (25, 0, 522), (26, 0, 530), (27, 0, 538)]) (q := 825) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c14320_0 : P.sumLeaves 26 14663680 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 229120) rows (by decide) (by decide)).symm.trans contract14320_0

theorem c14320_1 : P.sumLeaves 26 14663744 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14320) (lo := 64) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover14320 (by decide)
  decide +kernel

theorem contract14320_2 : P.leaf 32 229125 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 467), (30, 1, 873), (32, 1, 873), (17, 0, 874), (16, 0, 859), (21, 13, 867), (12, 0, 880), (10, 0, 460), (11, 0, 458), (13, 0, 458), (22, 1, 426), (5, 1, 586), (4, 1, 410), (3, 1, 409), (6, 1, 412), (7, 0, 458), (8, 1, 465), (9, 1, 473), (28, 1, 481), (29, 1, 489)]) (q := 810) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c14320_2 : P.sumLeaves 26 14664000 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 229125) rows (by decide) (by decide)).symm.trans contract14320_2

theorem c14320_3 : P.sumLeaves 26 14664064 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14320) (lo := 384) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover14320 (by decide)
  decide +kernel

theorem contract14320_4 : P.leaf 32 229130 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 467), (17, 1, 874), (12, 1, 880), (5, 1, 411), (4, 1, 410), (3, 1, 409), (6, 1, 412), (7, 1, 458), (10, 1, 458), (11, 1, 459), (13, 1, 461)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c14320_4 : P.sumLeaves 26 14664320 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 229130) rows (by decide) (by decide)).symm.trans contract14320_4

theorem c14320_5 : P.sumLeaves 26 14664384 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14320) (lo := 704) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover14320 (by decide)
  decide +kernel

theorem contract14320_6 : P.leaf 32 229134 = 25088 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 229134) (ss := [(2, 1, 467), (30, 1, 873), (32, 1, 873), (17, 1, 874), (14, 1, 859), (12, 1, 880), (5, 1, 411), (4, 1, 410), (3, 1, 409), (6, 1, 412), (7, 1, 458), (10, 1, 458), (11, 1, 459), (13, 1, 461), (21, 1, 929), (31, 1, 930), (15, 1, 916)]) (ids := [6, 14, 16, 22, 26, 7, 17, 18, 23, 27, 20, 21, 24, 25, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8, 9, 1, 12, 13, 5, 10, 14, 15, 6, 11, 1, 1, 1, 16]) (bs := [5, 5, 5]) (W := 25088) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14320_6 : P.sumLeaves 26 14664576 64 = 25088 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 229134) rows (by decide) (by decide)).symm.trans contract14320_6

theorem contract14320_7 : P.leaf 32 229135 = 25088 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 229135) (ss := [(2, 1, 467), (30, 1, 873), (32, 1, 873), (17, 1, 874), (14, 1, 859), (12, 1, 880), (5, 1, 411), (4, 1, 410), (3, 1, 409), (6, 1, 412), (7, 1, 458), (10, 1, 458), (11, 1, 459), (13, 1, 461), (21, 1, 929), (31, 1, 930), (15, 1, 916)]) (ids := [6, 14, 16, 22, 26, 7, 17, 18, 23, 27, 20, 21, 24, 25, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8, 9, 1, 12, 13, 5, 10, 14, 15, 6, 11, 1, 1, 1, 16]) (bs := [5, 5, 5]) (W := 25088) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14320_7 : P.sumLeaves 26 14664640 64 = 25088 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 229135) rows (by decide) (by decide)).symm.trans contract14320_7

theorem h14320 : P.leaf 36 14320 = 50176 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (256, 0), (64, 0), (256, 0), (64, 0), (192, 0), (64, 25088), (64, 25088)]) (.cons c14320_0 (.cons c14320_1 (.cons c14320_2 (.cons c14320_3 (.cons c14320_4 (.cons c14320_5 (.cons c14320_6 (.cons c14320_7 (.nil))))))))) (by decide) (by decide))

theorem cover14321 : P.CoversSplit 26 10 14321 0xf0000000f0000000f0000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (ps := [(12, [880], [979])]) (by decide +kernel)

theorem c14321_0 : P.sumLeaves 26 14664704 1024 = 1536784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14321) (lo := 0) (len := 1024) (W := 1536784) check rows elimOK (by decide) (by decide) cover14321 (by decide)
  decide +kernel

theorem h14321 : P.leaf 36 14321 = 1536784 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1536784)]) (.cons c14321_0 (.nil)) (by decide) (by decide))

theorem cover14323 : P.CoversSplit 26 10 14323 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (by decide +kernel)

noncomputable def f14323 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (14666752 + i)

theorem c14323_0 : rowSum f14323 0 1024 = 6860096 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14323) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14323 (by decide)
  decide +kernel

theorem sum14323 : rowSum f14323 0 1024 = 6860096 :=
  c14323_0

theorem h14323 : P.leaf 36 14323 = 6860096 :=
  leaf_weighted (k := 26) (d := 10) (H := 14323) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 14323) (by decide) (by decide +kernel)) sum14323

theorem cover14324 : P.CoversSplit 26 10 14324 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 880, 929, 930, 1265, 1315, 1322]) (by decide +kernel)

theorem c14324_0 : P.sumLeaves 26 14667776 1024 = 1087824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14324) (lo := 0) (len := 1024) (W := 1087824) check rows elimOK (by decide) (by decide) cover14324 (by decide)
  decide +kernel

theorem h14324 : P.leaf 36 14324 = 1087824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1087824)]) (.cons c14324_0 (.nil)) (by decide) (by decide))

theorem cover14325 : P.CoversSplit 26 10 14325 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 929, 930, 972, 979, 1265, 1315, 1322]) (by decide +kernel)

theorem c14325_0 : P.sumLeaves 26 14668800 1024 = 7812712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14325) (lo := 0) (len := 1024) (W := 7812712) check rows elimOK (by decide) (by decide) cover14325 (by decide)
  decide +kernel

theorem h14325 : P.leaf 36 14325 = 7812712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7812712)]) (.cons c14325_0 (.nil)) (by decide) (by decide))

theorem cover14326 : P.CoversSplit 26 10 14326 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 880, 930, 972, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14326_0 : P.sumLeaves 26 14669824 1024 = 13142184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14326) (lo := 0) (len := 1024) (W := 13142184) check rows elimOK (by decide) (by decide) cover14326 (by decide)
  decide +kernel

theorem h14326 : P.leaf 36 14326 = 13142184 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13142184)]) (.cons c14326_0 (.nil)) (by decide) (by decide))

theorem cover14327 : P.CoversSplit 26 10 14327 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 930, 972, 979, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14327_0 : P.sumLeaves 26 14670848 1024 = 61616798 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14327) (lo := 0) (len := 1024) (W := 61616798) check rows elimOK (by decide) (by decide) cover14327 (by decide)
  decide +kernel

theorem h14327 : P.leaf 36 14327 = 61616798 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61616798)]) (.cons c14327_0 (.nil)) (by decide) (by decide))

theorem cover14332 : P.CoversSplit 26 10 14332 0xfffffffaffffc8c8fffffafaffffc8c8fffcfff8ffccc8c8aa88aa88aa888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 874, 923, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f14332 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (14675968 + i)

theorem c14332_0 : rowSum f14332 0 1024 = 28424993 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14332) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14332 (by decide)
  decide +kernel

theorem sum14332 : rowSum f14332 0 1024 = 28424993 :=
  c14332_0

theorem h14332 : P.leaf 36 14332 = 28424993 :=
  leaf_weighted (k := 26) (d := 10) (H := 14332) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 14332) (by decide) (by decide +kernel)) sum14332

theorem cover14333 : P.CoversSplit 26 10 14333 0xfffffffaffffc8c8fffffafaffffc8c8fffcfff8ffccc8c8aa88aa88aa8888880000000000000000000000000000000000000000000000000000000000000000fffffffaccccc8c8fffffafaccccc8c8ffccffc8cc00c800aa88aa88880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14333_0 : P.sumLeaves 26 14676992 470 = 34017468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 0) (len := 470) (W := 34017468) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem c14333_1 : P.sumLeaves 26 14677462 419 = 50645456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 470) (len := 419) (W := 50645456) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem c14333_2 : P.sumLeaves 26 14677881 122 = 74540192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 889) (len := 122) (W := 74540192) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem c14333_3 : P.sumLeaves 26 14678003 13 = 23231292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 1011) (len := 13) (W := 23231292) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem h14333 : P.leaf 36 14333 = 182434408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(470, 34017468), (419, 50645456), (122, 74540192), (13, 23231292)]) (.cons c14333_0 (.cons c14333_1 (.cons c14333_2 (.cons c14333_3 (.nil))))) (by decide) (by decide))

theorem cover14335 : P.CoversSplit 26 10 14335 0xfffffffaffffc8c8fffffafaffffc8c8fffcfff8ffccc8c8aa88aa88aa888888fffffafaffffc8c8aaaaaaaaaaaa8888fffcfaf8ffccc8c8aa88aa88aa888888fffffffaccccc8c8fffffafaccccc8c8ffccffc8ccccc8c8aa88aa8888888888fffffafaccccc8c8aaaaaaaa88888888ffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f14335 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (14679040 + i)

theorem c14335_0 : rowSum f14335 0 346 = 112879508 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14335) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_1 : rowSum f14335 346 149 = 543136780 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14335) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_2 : rowSum f14335 495 463 = 678893834 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14335) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_3 : rowSum f14335 958 66 = 165410064 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14335) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem sum14335 : rowSum f14335 0 1024 = 1500320186 :=
  rowSum_append (F := f14335) (lo := 0) (n := 346) (m := 678) (A := 112879508) (B := 1387440678) c14335_0 (rowSum_append (F := f14335) (lo := 346) (n := 149) (m := 529) (A := 543136780) (B := 844303898) c14335_1 (rowSum_append (F := f14335) (lo := 495) (n := 463) (m := 66) (A := 678893834) (B := 165410064) c14335_2 (c14335_3)))

theorem h14335 : P.leaf 36 14335 = 1500320186 :=
  leaf_weighted (k := 26) (d := 10) (H := 14335) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 14335) (by decide) (by decide +kernel)) sum14335

theorem cover15606 : P.CoversSplit 26 10 15606 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15606_0 : P.sumLeaves 26 15980544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15606) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15606 (by decide)
  decide +kernel

theorem h15606 : P.leaf 36 15606 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15606_0 (.nil)) (by decide) (by decide))

theorem cover15607 : P.CoversSplit 26 10 15607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15607_0 : P.sumLeaves 26 15981568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15607) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15607 (by decide)
  decide +kernel

theorem h15607 : P.leaf 36 15607 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15607_0 (.nil)) (by decide) (by decide))

theorem cover15608 : P.CoversSplit 26 10 15608 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15608_0 : P.sumLeaves 26 15982592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15608) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15608 (by decide)
  decide +kernel

theorem h15608 : P.leaf 36 15608 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15608_0 (.nil)) (by decide) (by decide))

theorem cover15609 : P.CoversSplit 26 10 15609 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15609_0 : P.sumLeaves 26 15983616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15609) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15609 (by decide)
  decide +kernel

theorem h15609 : P.leaf 36 15609 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15609_0 (.nil)) (by decide) (by decide))

theorem cover15610 : P.CoversSplit 26 10 15610 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15610_0 : P.sumLeaves 26 15984640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15610) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15610 (by decide)
  decide +kernel

theorem h15610 : P.leaf 36 15610 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15610_0 (.nil)) (by decide) (by decide))

theorem cover15611 : P.CoversSplit 26 10 15611 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15611_0 : P.sumLeaves 26 15985664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15611) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15611 (by decide)
  decide +kernel

theorem h15611 : P.leaf 36 15611 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15611_0 (.nil)) (by decide) (by decide))

theorem cover15614 : P.CoversSplit 26 10 15614 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15614_0 : P.sumLeaves 26 15988736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15614) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15614 (by decide)
  decide +kernel

theorem h15614 : P.leaf 36 15614 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15614_0 (.nil)) (by decide) (by decide))

theorem cover15615 : P.CoversSplit 26 10 15615 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15615_0 : P.sumLeaves 26 15989760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15615) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15615 (by decide)
  decide +kernel

theorem h15615 : P.leaf 36 15615 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15615_0 (.nil)) (by decide) (by decide))

theorem cover15732 : P.CoversSplit 26 10 15732 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15732_0 : P.sumLeaves 26 16109568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15732) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15732 (by decide)
  decide +kernel

theorem h15732 : P.leaf 36 15732 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15732_0 (.nil)) (by decide) (by decide))

theorem cover15733 : P.CoversSplit 26 10 15733 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15733_0 : P.sumLeaves 26 16110592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15733) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15733 (by decide)
  decide +kernel

theorem h15733 : P.leaf 36 15733 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15733_0 (.nil)) (by decide) (by decide))

theorem cover15734 : P.CoversSplit 26 10 15734 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15734_0 : P.sumLeaves 26 16111616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15734) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15734 (by decide)
  decide +kernel

theorem h15734 : P.leaf 36 15734 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15734_0 (.nil)) (by decide) (by decide))

theorem cover15735 : P.CoversSplit 26 10 15735 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15735_0 : P.sumLeaves 26 16112640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15735) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15735 (by decide)
  decide +kernel

theorem h15735 : P.leaf 36 15735 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15735_0 (.nil)) (by decide) (by decide))

theorem cover15740 : P.CoversSplit 26 10 15740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15740_0 : P.sumLeaves 26 16117760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15740) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15740 (by decide)
  decide +kernel

theorem h15740 : P.leaf 36 15740 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15740_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14305, 720), (14307, 360), (14308, 720), (14309, 720), (14310, 720), (14311, 720), (14316, 360), (14317, 720), (14319, 360), (14320, 360), (14321, 720), (14323, 360), (14324, 720), (14325, 720), (14326, 720), (14327, 720), (14332, 360), (14333, 720), (14335, 360), (15606, 180), (15607, 180), (15608, 180), (15609, 180), (15610, 360), (15611, 360), (15614, 180), (15615, 180), (15732, 720), (15733, 720), (15734, 720), (15735, 720), (15740, 360)]

theorem segOK : checkSeg 20 perms 14305 15741 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14305 15741 16200 745530073560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 745530073560)
    (SegSum.cons (w := 720) h14305 (SegSum.cons (w := 360) h14307 (SegSum.cons (w := 720) h14308 (SegSum.cons (w := 720) h14309 (SegSum.cons (w := 720) h14310 (SegSum.cons (w := 720) h14311 (SegSum.cons (w := 360) h14316 (SegSum.cons (w := 720) h14317 (SegSum.cons (w := 360) h14319 (SegSum.cons (w := 360) h14320 (SegSum.cons (w := 720) h14321 (SegSum.cons (w := 360) h14323 (SegSum.cons (w := 720) h14324 (SegSum.cons (w := 720) h14325 (SegSum.cons (w := 720) h14326 (SegSum.cons (w := 720) h14327 (SegSum.cons (w := 360) h14332 (SegSum.cons (w := 720) h14333 (SegSum.cons (w := 360) h14335 (SegSum.cons (w := 180) h15606 (SegSum.cons (w := 180) h15607 (SegSum.cons (w := 180) h15608 (SegSum.cons (w := 180) h15609 (SegSum.cons (w := 360) h15610 (SegSum.cons (w := 360) h15611 (SegSum.cons (w := 180) h15614 (SegSum.cons (w := 180) h15615 (SegSum.cons (w := 720) h15732 (SegSum.cons (w := 720) h15733 (SegSum.cons (w := 720) h15734 (SegSum.cons (w := 720) h15735 (SegSum.cons (w := 360) h15740 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S29
