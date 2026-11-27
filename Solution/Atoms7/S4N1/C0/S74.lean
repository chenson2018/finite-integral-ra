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

namespace RACert.S4N1.C0.S74

open RACert RACert.Problem

theorem cover22251 : P.CoversSplit 24 10 22251 0xfffffffff0f00000fffffffff0f00000fffffffff0f00000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cccccccc8080000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(14, [923, 1217], [916, 1266])]) (by decide +kernel)

theorem c22251_0 : P.sumLeaves 24 22785024 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22251) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22251 (by decide)
  decide +kernel

theorem contract22251_1 : P.leaf 30 356020 = 48 := by
  exact leaf_contract_factors (k := 30) (b := 6) (H := 356020) (ss := [(18, 1, 524), (30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (12, 1, 958), (27, 0, 1259), (4, 1, 566), (8, 0, 573), (5, 1, 551), (9, 0, 573), (29, 0, 573), (14, 0, 580), (20, 1, 482), (21, 0, 488), (7, 1, 628), (6, 1, 460), (15, 0, 678), (2, 1, 411), (23, 1, 803), (10, 1, 811), (11, 1, 818), (28, 1, 860), (13, 1, 971), (16, 1, 1314)]) (ids := [17, 23, 1, 20, 22, 24]) (cs := [1, 4, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 2, 1, 0, 5, 1, 6, 3, 7, 0, 1, 0, 1, 1]) (bs := [2, 4]) (W := 48) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22251_1 : P.sumLeaves 24 22785280 64 = 48 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356020) rows (by decide) (by decide)).symm.trans contract22251_1

theorem contract22251_2 : P.leaf 30 356021 = 1792 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 356021) (ss := [(18, 1, 524), (27, 1, 573), (14, 0, 1266), (12, 1, 487), (11, 1, 818), (6, 1, 460), (10, 1, 811), (8, 0, 874), (5, 1, 433), (20, 1, 482), (21, 0, 488), (7, 1, 628), (13, 1, 971), (31, 1, 1217), (16, 1, 1314)]) (ids := [0, 1, 2, 7, 13, 15, 17, 20, 21, 22, 24, 26, 27, 28, 23]) (cs := [2, 3, 4, 1, 1, 1, 0, 5, 1, 1, 1, 1, 0, 6, 1, 7, 1, 8, 1, 0, 9, 10, 11, 16, 12, 1, 13, 14, 15, 1]) (bs := [14, 1]) (W := 1792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22251_2 : P.sumLeaves 24 22785344 64 = 1792 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356021) rows (by decide) (by decide)).symm.trans contract22251_2

theorem c22251_3 : P.sumLeaves 24 22785408 566 = 4801065 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22251) (lo := 384) (len := 566) (W := 4801065) check rows elimOK (by decide) (by decide) cover22251 (by decide)
  decide +kernel

theorem c22251_4 : P.sumLeaves 24 22785974 74 = 9372046 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22251) (lo := 950) (len := 74) (W := 9372046) check rows elimOK (by decide) (by decide) cover22251 (by decide)
  decide +kernel

theorem h22251 : P.leaf 34 22251 = 14174951 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 48), (64, 1792), (566, 4801065), (74, 9372046)]) (.cons c22251_0 (.cons c22251_1 (.cons c22251_2 (.cons c22251_3 (.cons c22251_4 (.nil)))))) (by decide) (by decide))

theorem cover22252 : P.CoversSplit 24 10 22252 0xccccccccc8c80000ccccccccc8c80000ccccccccc8880000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 573, 916, 1210, 1251, 1259, 1601]) (ps := [(12, [860], [909]), (14, [1217], [1266])]) (by decide +kernel)

theorem c22252_0 : P.sumLeaves 24 22786048 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22252) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover22252 (by decide)
  decide +kernel

theorem contract22252_1 : P.leaf 30 356037 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (27, 1, 508), (4, 1, 536), (29, 1, 916), (14, 0, 1266), (12, 1, 867), (11, 1, 818), (10, 1, 811), (21, 1, 874), (8, 1, 580), (20, 1, 880)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22252_1 : P.sumLeaves 24 22786368 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356037) rows (by decide) (by decide)).symm.trans contract22252_1

theorem c22252_2 : P.sumLeaves 24 22786432 640 = 8003683 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22252) (lo := 384) (len := 640) (W := 8003683) check rows elimOK (by decide) (by decide) cover22252 (by decide)
  decide +kernel

theorem h22252 : P.leaf 34 22252 = 8003683 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 8003683)]) (.cons c22252_0 (.cons c22252_1 (.cons c22252_2 (.nil)))) (by decide) (by decide))

theorem cover22253 : P.CoversSplit 24 10 22253 0xffffffffeaea0000ffffffffeaea0000ffffffffeaaa0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 860, 916, 1210, 1251, 1259, 1601]) (ps := [(12, [860], [909]), (14, [1217], [1266])]) (by decide +kernel)

theorem c22253_0 : P.sumLeaves 24 22787072 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22253) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22253 (by decide)
  decide +kernel

theorem contract22253_1 : P.leaf 30 356052 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (4, 1, 536), (30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (27, 0, 1259), (8, 0, 573), (5, 1, 426), (9, 0, 573), (29, 0, 573), (21, 0, 580), (20, 1, 586), (15, 14, 678), (10, 1, 874), (14, 1, 874)]) (q := 916) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22253_1 : P.sumLeaves 24 22787328 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356052) rows (by decide) (by decide)).symm.trans contract22253_1

theorem contract22253_2 : P.leaf 30 356053 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (4, 1, 536), (27, 1, 573), (29, 1, 916), (14, 0, 1266), (12, 1, 867), (11, 1, 818), (21, 0, 923), (8, 1, 874), (20, 1, 929)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22253_2 : P.sumLeaves 24 22787392 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356053) rows (by decide) (by decide)).symm.trans contract22253_2

theorem c22253_3 : P.sumLeaves 24 22787456 562 = 7431752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22253) (lo := 384) (len := 562) (W := 7431752) check rows elimOK (by decide) (by decide) cover22253 (by decide)
  decide +kernel

theorem c22253_4 : P.sumLeaves 24 22788018 78 = 13915844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22253) (lo := 946) (len := 78) (W := 13915844) check rows elimOK (by decide) (by decide) cover22253 (by decide)
  decide +kernel

theorem h22253 : P.leaf 34 22253 = 21347596 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (562, 7431752), (78, 13915844)]) (.cons c22253_0 (.cons c22253_1 (.cons c22253_2 (.cons c22253_3 (.cons c22253_4 (.nil)))))) (by decide) (by decide))

theorem cover22254 : P.CoversSplit 24 10 22254 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 860, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(14, [1217], [1266])]) (by decide +kernel)

theorem c22254_0 : P.sumLeaves 24 22788096 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22254) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22254 (by decide)
  decide +kernel

theorem contract22254_1 : P.leaf 30 356068 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 524), (30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (27, 0, 1259), (10, 1, 508), (4, 1, 566), (8, 0, 573), (9, 0, 573), (20, 1, 538), (29, 0, 573), (14, 0, 580), (5, 1, 433), (21, 0, 580), (7, 1, 628), (15, 0, 678), (3, 1, 486), (12, 1, 811)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22254_1 : P.sumLeaves 24 22788352 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356068) rows (by decide) (by decide)).symm.trans contract22254_1

theorem contract22254_2 : P.leaf 30 356069 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 524), (27, 1, 573), (29, 1, 916), (14, 0, 1266), (12, 1, 867), (21, 1, 874), (8, 1, 580), (20, 1, 880)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22254_2 : P.sumLeaves 24 22788416 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356069) rows (by decide) (by decide)).symm.trans contract22254_2

theorem c22254_3 : P.sumLeaves 24 22788480 557 = 13255463 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22254) (lo := 384) (len := 557) (W := 13255463) check rows elimOK (by decide) (by decide) cover22254 (by decide)
  decide +kernel

theorem c22254_4 : P.sumLeaves 24 22789037 83 = 23575704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22254) (lo := 941) (len := 83) (W := 23575704) check rows elimOK (by decide) (by decide) cover22254 (by decide)
  decide +kernel

theorem h22254 : P.leaf 34 22254 = 36831167 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (557, 13255463), (83, 23575704)]) (.cons c22254_0 (.cons c22254_1 (.cons c22254_2 (.cons c22254_3 (.cons c22254_4 (.nil)))))) (by decide) (by decide))

theorem cover22255 : P.CoversSplit 24 10 22255 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(14, [1217], [1266])]) (by decide +kernel)

theorem c22255_0 : P.sumLeaves 24 22789120 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22255) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22255 (by decide)
  decide +kernel

theorem contract22255_1 : P.leaf 30 356084 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 524), (30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (27, 0, 1259), (4, 1, 566), (8, 0, 573), (9, 0, 573), (29, 0, 573), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (15, 0, 678), (12, 1, 825)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22255_1 : P.sumLeaves 24 22789376 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356084) rows (by decide) (by decide)).symm.trans contract22255_1

theorem contract22255_2 : P.leaf 30 356085 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 524), (27, 1, 573), (29, 1, 916), (14, 0, 1266), (12, 1, 867), (8, 0, 923), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22255_2 : P.sumLeaves 24 22789440 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356085) rows (by decide) (by decide)).symm.trans contract22255_2

theorem c22255_3 : P.sumLeaves 24 22789504 557 = 21593294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22255) (lo := 384) (len := 557) (W := 21593294) check rows elimOK (by decide) (by decide) cover22255 (by decide)
  decide +kernel

theorem c22255_4 : P.sumLeaves 24 22790061 83 = 41070244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22255) (lo := 941) (len := 83) (W := 41070244) check rows elimOK (by decide) (by decide) cover22255 (by decide)
  decide +kernel

theorem h22255 : P.leaf 34 22255 = 62663538 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (557, 21593294), (83, 41070244)]) (.cons c22255_0 (.cons c22255_1 (.cons c22255_2 (.cons c22255_3 (.cons c22255_4 (.nil)))))) (by decide) (by decide))

theorem cover22267 : P.CoversSplit 24 10 22267 0xfffffffff0f00000fffffffff0f00000fffffffff0f00000fffffffff0f000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cccccccc8080000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 860, 916, 1202, 1210, 1259, 1308, 1601, 1651]) (ps := [(14, [923, 1217], [916, 1266])]) (by decide +kernel)

theorem c22267_0 : P.sumLeaves 24 22801408 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22267) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22267 (by decide)
  decide +kernel

theorem contract22267_1 : P.leaf 30 356276 = 192 := by
  exact leaf_contract_factors (k := 30) (b := 8) (H := 356276) (ss := [(17, 0, 1259), (12, 1, 958), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (18, 1, 578), (14, 0, 580), (5, 1, 433), (20, 1, 482), (21, 0, 488), (7, 1, 628), (6, 1, 460), (15, 0, 678), (2, 1, 411), (23, 1, 803), (10, 1, 811), (11, 1, 818), (28, 1, 860), (13, 1, 971), (31, 1, 1217), (16, 1, 1314)]) (ids := [17, 23, 1, 2, 20, 22, 24, 28]) (cs := [1, 4, 5, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 2, 1, 0, 6, 1, 7, 3, 8, 0, 1, 0, 9, 1]) (bs := [2, 6]) (W := 192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22267_1 : P.sumLeaves 24 22801664 64 = 192 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356276) rows (by decide) (by decide)).symm.trans contract22267_1

theorem c22267_2 : P.sumLeaves 24 22801728 564 = 4222894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22267) (lo := 320) (len := 564) (W := 4222894) check rows elimOK (by decide) (by decide) cover22267 (by decide)
  decide +kernel

theorem c22267_3 : P.sumLeaves 24 22802292 140 = 18791189 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22267) (lo := 884) (len := 140) (W := 18791189) check rows elimOK (by decide) (by decide) cover22267 (by decide)
  decide +kernel

theorem h22267 : P.leaf 34 22267 = 23014275 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 192), (564, 4222894), (140, 18791189)]) (.cons c22267_0 (.cons c22267_1 (.cons c22267_2 (.cons c22267_3 (.nil))))) (by decide) (by decide))

theorem cover22268 : P.CoversSplit 24 10 22268 0xfcfcfcfcf8f80000fcfcfcfcf8f80000fcfcfcfcf8000000fcfcfcfcf80000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 867, 909, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [1266]), (14, [1217], [1266])]) (by decide +kernel)

theorem c22268_0 : P.sumLeaves 24 22802432 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22268) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22268 (by decide)
  decide +kernel

theorem contract22268_1 : P.leaf 30 356292 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (17, 0, 1259), (27, 0, 1259), (28, 1, 508), (8, 0, 573), (9, 0, 573), (29, 0, 573), (21, 0, 580), (20, 1, 537), (15, 14, 678), (10, 1, 874), (14, 1, 874), (31, 1, 909)]) (q := 916) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22268_1 : P.sumLeaves 24 22802688 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356292) rows (by decide) (by decide)).symm.trans contract22268_1

theorem contract22268_2 : P.leaf 30 356293 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (27, 1, 573), (29, 1, 916), (8, 0, 1266), (21, 0, 580), (20, 1, 537), (10, 1, 874), (14, 1, 874), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22268_2 : P.sumLeaves 24 22802752 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356293) rows (by decide) (by decide)).symm.trans contract22268_2

theorem c22268_3 : P.sumLeaves 24 22802816 567 = 11275180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22268) (lo := 384) (len := 567) (W := 11275180) check rows elimOK (by decide) (by decide) cover22268 (by decide)
  decide +kernel

theorem c22268_4 : P.sumLeaves 24 22803383 73 = 12758902 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22268) (lo := 951) (len := 73) (W := 12758902) check rows elimOK (by decide) (by decide) cover22268 (by decide)
  decide +kernel

theorem h22268 : P.leaf 34 22268 = 24034082 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (567, 11275180), (73, 12758902)]) (.cons c22268_0 (.cons c22268_1 (.cons c22268_2 (.cons c22268_3 (.cons c22268_4 (.nil)))))) (by decide) (by decide))

theorem cover22269 : P.CoversSplit 24 10 22269 0xfffffffffafa0000fffffffffafa0000fffffffffa000000fffffffffa0000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 573, 860, 867, 909, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [1266]), (14, [1217], [1266])]) (by decide +kernel)

theorem c22269_0 : P.sumLeaves 24 22803456 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22269) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22269 (by decide)
  decide +kernel

theorem contract22269_1 : P.leaf 30 356308 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (17, 0, 1259), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (21, 0, 580), (20, 1, 586), (15, 14, 678), (10, 1, 874), (14, 1, 874), (31, 1, 909)]) (q := 916) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22269_1 : P.sumLeaves 24 22803712 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356308) rows (by decide) (by decide)).symm.trans contract22269_1

theorem contract22269_2 : P.leaf 30 356309 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (27, 1, 573), (29, 1, 916), (8, 0, 1266), (21, 0, 580), (20, 1, 586), (10, 1, 874), (14, 1, 874), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22269_2 : P.sumLeaves 24 22803776 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356309) rows (by decide) (by decide)).symm.trans contract22269_2

theorem c22269_3 : P.sumLeaves 24 22803840 541 = 14708278 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22269) (lo := 384) (len := 541) (W := 14708278) check rows elimOK (by decide) (by decide) cover22269 (by decide)
  decide +kernel

theorem c22269_4 : P.sumLeaves 24 22804381 99 = 33824823 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22269) (lo := 925) (len := 99) (W := 33824823) check rows elimOK (by decide) (by decide) cover22269 (by decide)
  decide +kernel

theorem h22269 : P.leaf 34 22269 = 48533101 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (541, 14708278), (99, 33824823)]) (.cons c22269_0 (.cons c22269_1 (.cons c22269_2 (.cons c22269_3 (.cons c22269_4 (.nil)))))) (by decide) (by decide))

theorem cover22270 : P.CoversSplit 24 10 22270 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 860, 867, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916, 1266])]) (by decide +kernel)

theorem c22270_0 : P.sumLeaves 24 22804480 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22270) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22270 (by decide)
  decide +kernel

theorem contract22270_1 : P.leaf 30 356324 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (18, 1, 578), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (15, 0, 678), (3, 1, 486), (12, 1, 825), (10, 1, 852)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22270_1 : P.sumLeaves 24 22804736 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356324) rows (by decide) (by decide)).symm.trans contract22270_1

theorem contract22270_2 : P.leaf 30 356325 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (12, 1, 825)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22270_2 : P.sumLeaves 24 22804800 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356325) rows (by decide) (by decide)).symm.trans contract22270_2

theorem c22270_3 : P.sumLeaves 24 22804864 509 = 16706648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22270) (lo := 384) (len := 509) (W := 16706648) check rows elimOK (by decide) (by decide) cover22270 (by decide)
  decide +kernel

theorem c22270_4 : P.sumLeaves 24 22805373 131 = 45815035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22270) (lo := 893) (len := 131) (W := 45815035) check rows elimOK (by decide) (by decide) cover22270 (by decide)
  decide +kernel

theorem h22270 : P.leaf 34 22270 = 62521683 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (509, 16706648), (131, 45815035)]) (.cons c22270_0 (.cons c22270_1 (.cons c22270_2 (.cons c22270_3 (.cons c22270_4 (.nil)))))) (by decide) (by decide))

theorem cover22271 : P.CoversSplit 24 10 22271 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 860, 867, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916, 1266])]) (by decide +kernel)

theorem c22271_0 : P.sumLeaves 24 22805504 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22271) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22271 (by decide)
  decide +kernel

theorem contract22271_1 : P.leaf 30 356340 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (18, 1, 578), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (15, 0, 678), (12, 1, 825)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22271_1 : P.sumLeaves 24 22805760 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356340) rows (by decide) (by decide)).symm.trans contract22271_1

theorem contract22271_2 : P.leaf 30 356341 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (12, 1, 825)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22271_2 : P.sumLeaves 24 22805824 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356341) rows (by decide) (by decide)).symm.trans contract22271_2

theorem c22271_3 : P.sumLeaves 24 22805888 509 = 28436067 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22271) (lo := 384) (len := 509) (W := 28436067) check rows elimOK (by decide) (by decide) cover22271 (by decide)
  decide +kernel

theorem c22271_4 : P.sumLeaves 24 22806397 131 = 75623760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22271) (lo := 893) (len := 131) (W := 75623760) check rows elimOK (by decide) (by decide) cover22271 (by decide)
  decide +kernel

theorem h22271 : P.leaf 34 22271 = 104059827 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (509, 28436067), (131, 75623760)]) (.cons c22271_0 (.cons c22271_1 (.cons c22271_2 (.cons c22271_3 (.cons c22271_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22251, 24), (22252, 48), (22253, 48), (22254, 48), (22255, 48), (22267, 12), (22268, 48), (22269, 48), (22270, 48), (22271, 48)]

theorem segOK : checkSeg 16 perms 22251 22309 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22251 22309 420 18280114620 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18280114620)
    (SegSum.cons (w := 24) h22251 (SegSum.cons (w := 48) h22252 (SegSum.cons (w := 48) h22253 (SegSum.cons (w := 48) h22254 (SegSum.cons (w := 48) h22255 (SegSum.cons (w := 12) h22267 (SegSum.cons (w := 48) h22268 (SegSum.cons (w := 48) h22269 (SegSum.cons (w := 48) h22270 (SegSum.cons (w := 48) h22271 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S74
