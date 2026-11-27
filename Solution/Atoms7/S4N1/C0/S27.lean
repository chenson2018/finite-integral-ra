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

namespace RACert.S4N1.C0.S27

open RACert RACert.Problem

theorem cover5280 : P.CoversSplit 24 10 5280 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5280_0 : P.sumLeaves 24 5406720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5280) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5280 (by decide)
  decide +kernel

theorem h5280 : P.leaf 34 5280 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5280_0 (.nil)) (by decide) (by decide))

theorem h5281 : P.leaf 34 5281 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (4, 1, 410), (30, 1, 466), (31, 1, 468), (8, 0, 475), (6, 1, 478), (11, 1, 459), (12, 1, 460), (14, 0, 487), (33, 0, 482), (26, 1, 515), (35, 0, 524), (16, 1, 529), (3, 1, 419), (21, 0, 531), (20, 1, 433), (18, 1, 536), (29, 15, 558), (27, 9, 559)]) (q := 608) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5283 : P.leaf 34 5283 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (31, 1, 468), (34, 1, 475), (6, 1, 478), (12, 1, 460), (26, 1, 515), (30, 1, 515), (27, 1, 522), (32, 1, 522), (35, 0, 524), (16, 1, 529), (18, 1, 536), (33, 0, 566), (28, 1, 858), (29, 1, 865)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5284 : P.CoversSplit 24 10 5284 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5284_0 : P.sumLeaves 24 5410816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5284) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5284 (by decide)
  decide +kernel

theorem h5284 : P.leaf 34 5284 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5284_0 (.nil)) (by decide) (by decide))

theorem h5285 : P.leaf 34 5285 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (35, 8, 475), (11, 4, 508), (8, 0, 524), (16, 1, 529), (33, 0, 566), (31, 5, 468), (14, 0, 531), (21, 0, 482), (18, 4, 487), (20, 1, 537), (27, 9, 559), (5, 1, 601), (3, 1, 419), (2, 1, 412), (26, 1, 515), (34, 1, 622), (9, 1, 522), (32, 1, 522), (7, 1, 628), (28, 1, 858), (29, 1, 865), (13, 1, 971), (15, 1, 1021), (4, 1, 1265), (6, 1, 459), (12, 1, 818)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5287 : P.leaf 34 5287 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (16, 1, 529), (18, 1, 536), (33, 0, 566), (31, 1, 1301), (26, 1, 515), (30, 1, 515), (28, 1, 858)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5292 : P.CoversSplit 24 10 5292 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5292_0 : P.sumLeaves 24 5419008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5292) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5292 (by decide)
  decide +kernel

theorem h5292 : P.leaf 34 5292 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5292_0 (.nil)) (by decide) (by decide))

theorem h5293 : P.leaf 34 5293 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 4, 508), (35, 0, 524), (16, 1, 529), (33, 0, 566), (18, 4, 536), (4, 1, 1265), (31, 1, 1301), (26, 1, 515), (28, 1, 858)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5295 : P.leaf 34 5295 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (16, 1, 529), (18, 1, 536), (33, 0, 566), (31, 1, 1301), (26, 1, 515), (30, 1, 515), (28, 1, 858)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5297 : P.leaf 34 5297 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (31, 1, 468), (8, 0, 475), (6, 1, 478), (12, 1, 460), (11, 1, 459), (14, 0, 487), (33, 0, 482), (21, 0, 531), (35, 0, 531), (20, 1, 433), (34, 1, 524), (29, 15, 558), (9, 1, 559), (15, 1, 489), (26, 1, 517), (27, 1, 573)]) (q := 608) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5299 : P.leaf 34 5299 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (31, 1, 468), (34, 1, 475), (6, 1, 478), (12, 1, 460), (35, 0, 867), (16, 1, 872), (18, 1, 879), (33, 0, 909), (30, 1, 1251), (32, 1, 1264), (8, 0, 1266), (3, 1, 419), (4, 1, 426), (14, 0, 531), (21, 0, 531), (20, 1, 433)]) (q := 608) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5300 : P.leaf 34 5300 = 13344 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 5300) (ss := [(2, 1, 466), (5, 1, 404), (33, 8, 468), (35, 8, 475), (29, 28, 508), (9, 1, 510), (8, 1, 867), (16, 1, 872), (18, 1, 879), (30, 1, 1251), (31, 1, 1251), (28, 1, 858), (32, 1, 1259), (34, 1, 1259)]) (ids := [1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [1, 2, 3, 1, 4, 5, 1, 1, 6, 7, 8, 9, 10, 11, 1, 12, 1, 13, 14, 15, 16, 17, 20, 21, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 2]) (W := 13344) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h5301 : P.leaf 34 5301 = 103680 := by
  exact leaf_contract_factors (k := 34) (b := 22) (H := 5301) (ss := [(35, 8, 475), (9, 1, 559), (8, 1, 867), (5, 1, 524), (16, 1, 872), (33, 1, 909), (18, 1, 879), (30, 1, 1251), (31, 1, 1251), (32, 1, 1264), (34, 1, 1259), (29, 1, 865)]) (ids := [0, 1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 24, 25, 26, 22, 23]) (cs := [2, 3, 4, 1, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 1, 13, 1, 14, 15, 16, 17, 18, 22, 23, 19, 20, 21, 1, 1, 1, 1, 1, 1, 1]) (bs := [20, 2]) (W := 103680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5303 : P.CoversSplit 24 10 5303 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 860, 865, 866, 867, 909, 1202, 1209, 1258, 1259]) (by decide +kernel)

noncomputable def f5303 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5430272 + i)

theorem c5303_0 : rowSum f5303 0 1024 = 755712 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5303) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5303 (by decide)
  decide +kernel

theorem sum5303 : rowSum f5303 0 1024 = 755712 :=
  c5303_0

theorem h5303 : P.leaf 34 5303 = 755712 :=
  leaf_weighted (k := 24) (d := 10) (H := 5303) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5303) (by decide) (by decide +kernel)) sum5303

theorem h5304 : P.leaf 34 5304 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (33, 14, 486), (35, 14, 487), (29, 28, 508), (14, 0, 867), (34, 5, 524), (31, 5, 566), (16, 10, 872), (21, 0, 874), (18, 11, 879), (20, 1, 880), (12, 1, 951), (5, 1, 958), (3, 1, 409), (4, 1, 410), (28, 1, 858), (15, 1, 509), (26, 1, 517), (27, 1, 573), (30, 1, 858), (32, 1, 865), (8, 0, 972), (9, 1, 678)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5305 : P.leaf 34 5305 = 0 := by
  exact leaf_contract_zero (ss := [(35, 14, 487), (14, 0, 867), (34, 5, 524), (16, 1, 872), (33, 0, 909), (31, 12, 486), (12, 5, 566), (5, 1, 411), (10, 1, 811), (6, 1, 460), (29, 1, 865), (15, 1, 558), (27, 1, 573), (28, 1, 860), (26, 1, 517), (32, 1, 865), (8, 0, 874), (18, 11, 475), (20, 1, 482), (21, 0, 488), (7, 1, 628), (9, 1, 678), (13, 1, 971), (30, 1, 1209), (11, 1, 1265), (4, 1, 426)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5307 : P.leaf 34 5307 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 867), (34, 5, 524), (5, 1, 426), (16, 1, 872), (18, 1, 879), (33, 0, 909), (31, 1, 566), (30, 1, 1251), (32, 1, 1264), (8, 0, 1266), (14, 0, 531), (20, 1, 482), (12, 1, 486), (21, 0, 488), (7, 1, 628), (6, 1, 460), (10, 1, 811), (11, 1, 818), (13, 1, 971)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5308 : P.leaf 34 5308 = 75840 := by
  exact leaf_contract_factors (k := 34) (b := 22) (H := 5308) (ss := [(2, 1, 466), (29, 28, 508), (35, 1, 867), (5, 1, 524), (16, 1, 872), (33, 1, 909), (18, 1, 879), (30, 1, 1251), (31, 1, 1251), (28, 1, 858), (32, 1, 1259), (34, 1, 1259)]) (ids := [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [1, 2, 3, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 1, 14, 1, 15, 16, 17, 18, 19, 22, 23, 20, 21, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [20, 2]) (W := 75840) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5309 : P.CoversSplit 24 10 5309 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 573, 858, 860, 865, 867, 909, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem c5309_0 : P.sumLeaves 24 5436416 1024 = 687488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5309) (lo := 0) (len := 1024) (W := 687488) check rows elimOK (by decide) (by decide) cover5309 (by decide)
  decide +kernel

theorem h5309 : P.leaf 34 5309 = 687488 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 687488)]) (.cons c5309_0 (.nil)) (by decide) (by decide))

theorem cover5311 : P.CoversSplit 24 10 5311 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 860, 865, 867, 909, 1202, 1209, 1258, 1259]) (by decide +kernel)

noncomputable def f5311 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5438464 + i)

theorem c5311_0 : rowSum f5311 0 1024 = 3077856 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5311) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5311 (by decide)
  decide +kernel

theorem sum5311 : rowSum f5311 0 1024 = 3077856 :=
  c5311_0

theorem h5311 : P.leaf 34 5311 = 3077856 :=
  leaf_weighted (k := 24) (d := 10) (H := 5311) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5311) (by decide) (by decide +kernel)) sum5311

theorem cover5312 : P.CoversSplit 24 10 5312 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5312_0 : P.sumLeaves 24 5439488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5312) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5312 (by decide)
  decide +kernel

theorem h5312 : P.leaf 34 5312 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5312_0 (.nil)) (by decide) (by decide))

theorem h5313 : P.leaf 34 5313 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (4, 1, 410), (30, 1, 466), (11, 1, 472), (6, 1, 460), (12, 1, 460), (8, 0, 475), (3, 1, 418), (14, 0, 487), (33, 1, 482)]) (q := 488) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5314 : P.CoversSplit 24 10 5314 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5314_0 : P.sumLeaves 24 5441536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5314) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5314 (by decide)
  decide +kernel

theorem h5314 : P.leaf 34 5314 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5314_0 (.nil)) (by decide) (by decide))

theorem cover5315 : P.CoversSplit 24 10 5315 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5315_0 : P.sumLeaves 24 5442560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5315) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5315 (by decide)
  decide +kernel

theorem h5315 : P.leaf 34 5315 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5315_0 (.nil)) (by decide) (by decide))

theorem cover5316 : P.CoversSplit 24 10 5316 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5316_0 : P.sumLeaves 24 5443584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5316) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5316 (by decide)
  decide +kernel

theorem h5316 : P.leaf 34 5316 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5316_0 (.nil)) (by decide) (by decide))

theorem h5317 : P.leaf 34 5317 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (35, 8, 475), (4, 1, 508), (18, 1, 487), (32, 1, 523), (3, 1, 417), (33, 8, 536), (17, 1, 565), (8, 0, 867), (27, 1, 573), (6, 1, 459), (26, 1, 515), (9, 1, 559), (34, 1, 573), (5, 1, 426), (21, 0, 580), (14, 1, 482), (20, 1, 586), (31, 1, 615)]) (q := 629) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5318 : P.CoversSplit 24 10 5318 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5318_0 : P.sumLeaves 24 5445632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5318) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5318 (by decide)
  decide +kernel

theorem h5318 : P.leaf 34 5318 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5318_0 (.nil)) (by decide) (by decide))

theorem cover5319 : P.CoversSplit 24 10 5319 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5319_0 : P.sumLeaves 24 5446656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5319) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5319 (by decide)
  decide +kernel

theorem h5319 : P.leaf 34 5319 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5319_0 (.nil)) (by decide) (by decide))

theorem cover5320 : P.CoversSplit 24 10 5320 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c5320_0 : P.sumLeaves 24 5447680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5320) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5320 (by decide)
  decide +kernel

theorem h5320 : P.leaf 34 5320 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5320_0 (.nil)) (by decide) (by decide))

theorem h5321 : P.leaf 34 5321 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (18, 1, 475), (35, 14, 487), (4, 1, 508), (32, 1, 523), (3, 1, 417), (33, 14, 536), (17, 1, 565), (12, 1, 803), (14, 0, 867), (6, 1, 460), (27, 1, 573), (26, 1, 515), (34, 1, 573), (10, 1, 811), (29, 1, 865), (2, 1, 410), (15, 1, 558), (28, 1, 858), (16, 1, 872), (8, 0, 874), (5, 1, 411), (20, 1, 482), (21, 0, 488), (7, 1, 628), (9, 1, 678), (13, 1, 971), (31, 1, 1209)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5322 : P.CoversSplit 24 10 5322 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5322_0 : P.sumLeaves 24 5449728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5322) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5322 (by decide)
  decide +kernel

theorem h5322 : P.leaf 34 5322 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5322_0 (.nil)) (by decide) (by decide))

theorem cover5323 : P.CoversSplit 24 10 5323 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c5323_0 : P.sumLeaves 24 5450752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5323) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover5323 (by decide)
  decide +kernel

theorem h5323 : P.leaf 34 5323 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c5323_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5280, 6), (5281, 24), (5283, 12), (5284, 24), (5285, 48), (5287, 24), (5292, 12), (5293, 24), (5295, 12), (5297, 24), (5299, 24), (5300, 24), (5301, 48), (5303, 24), (5304, 24), (5305, 48), (5307, 24), (5308, 24), (5309, 48), (5311, 24), (5312, 24), (5313, 48), (5314, 48), (5315, 48), (5316, 48), (5317, 48), (5318, 48), (5319, 48), (5320, 48), (5321, 48), (5322, 48), (5323, 48)]

theorem segOK : checkSeg 16 perms 5280 5324 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5280 5324 1074 132122112 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 132122112)
    (SegSum.cons (w := 6) h5280 (SegSum.cons (w := 24) h5281 (SegSum.cons (w := 12) h5283 (SegSum.cons (w := 24) h5284 (SegSum.cons (w := 48) h5285 (SegSum.cons (w := 24) h5287 (SegSum.cons (w := 12) h5292 (SegSum.cons (w := 24) h5293 (SegSum.cons (w := 12) h5295 (SegSum.cons (w := 24) h5297 (SegSum.cons (w := 24) h5299 (SegSum.cons (w := 24) h5300 (SegSum.cons (w := 48) h5301 (SegSum.cons (w := 24) h5303 (SegSum.cons (w := 24) h5304 (SegSum.cons (w := 48) h5305 (SegSum.cons (w := 24) h5307 (SegSum.cons (w := 24) h5308 (SegSum.cons (w := 48) h5309 (SegSum.cons (w := 24) h5311 (SegSum.cons (w := 24) h5312 (SegSum.cons (w := 48) h5313 (SegSum.cons (w := 48) h5314 (SegSum.cons (w := 48) h5315 (SegSum.cons (w := 48) h5316 (SegSum.cons (w := 48) h5317 (SegSum.cons (w := 48) h5318 (SegSum.cons (w := 48) h5319 (SegSum.cons (w := 48) h5320 (SegSum.cons (w := 48) h5321 (SegSum.cons (w := 48) h5322 (SegSum.cons (w := 48) h5323 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S27
