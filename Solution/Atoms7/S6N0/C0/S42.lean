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

namespace RACert.S6N0.C0.S42

open RACert RACert.Problem

theorem cover78206 : P.CoversSplit 26 10 78206 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78206_0 : P.sumLeaves 26 80082944 1024 = 134384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78206) (lo := 0) (len := 1024) (W := 134384) check rows elimOK (by decide) (by decide) cover78206 (by decide)
  decide +kernel

theorem h78206 : P.leaf 36 78206 = 134384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 134384)]) (.cons c78206_0 (.nil)) (by decide) (by decide))

theorem cover78207 : P.CoversSplit 26 10 78207 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78207_0 : P.sumLeaves 26 80083968 1024 = 1760787 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78207) (lo := 0) (len := 1024) (W := 1760787) check rows elimOK (by decide) (by decide) cover78207 (by decide)
  decide +kernel

theorem h78207 : P.leaf 36 78207 = 1760787 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1760787)]) (.cons c78207_0 (.nil)) (by decide) (by decide))

theorem cover78245 : P.CoversSplit 26 10 78245 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000001000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (ps := [(15, [872], [559])]) (by decide +kernel)

theorem c78245_0 : P.sumLeaves 26 80122880 1024 = 5020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78245) (lo := 0) (len := 1024) (W := 5020) check rows elimOK (by decide) (by decide) cover78245 (by decide)
  decide +kernel

theorem h78245 : P.leaf 36 78245 = 5020 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5020)]) (.cons c78245_0 (.nil)) (by decide) (by decide))

theorem cover78246 : P.CoversSplit 26 10 78246 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78246_0 : P.sumLeaves 26 80123904 1024 = 5252 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78246) (lo := 0) (len := 1024) (W := 5252) check rows elimOK (by decide) (by decide) cover78246 (by decide)
  decide +kernel

theorem h78246 : P.leaf 36 78246 = 5252 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5252)]) (.cons c78246_0 (.nil)) (by decide) (by decide))

theorem cover78247 : P.CoversSplit 26 10 78247 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78247_0 : P.sumLeaves 26 80124928 1024 = 32924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78247) (lo := 0) (len := 1024) (W := 32924) check rows elimOK (by decide) (by decide) cover78247 (by decide)
  decide +kernel

theorem h78247 : P.leaf 36 78247 = 32924 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 32924)]) (.cons c78247_0 (.nil)) (by decide) (by decide))

theorem h78249 : P.leaf 36 78249 = 5120 := by
  exact leaf_contract_factors (k := 36) (b := 13) (H := 78249) (ss := [(16, 1, 466), (37, 1, 482), (19, 3, 524), (36, 1, 531), (33, 3, 536), (18, 1, 537), (11, 1, 879), (7, 1, 460), (12, 1, 460), (10, 1, 809), (13, 1, 818), (21, 1, 929), (17, 1, 1217), (14, 1, 858), (3, 1, 1273), (29, 1, 636), (28, 1, 629), (15, 1, 916), (30, 1, 972), (31, 1, 979), (35, 1, 1273), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 20, 6, 7, 18, 21, 22, 23, 24, 25]) (cs := [2, 1, 3, 4, 5, 1, 7, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6, 10, 11, 12, 13, 14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [5, 8]) (W := 5120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78251 : P.leaf 36 78251 = 14368 := by
  exact leaf_contract_factors (k := 36) (b := 15) (H := 78251) (ss := [(37, 1, 482), (19, 3, 524), (36, 1, 531), (3, 1, 536), (18, 1, 537), (16, 1, 867), (11, 1, 879), (10, 1, 810), (12, 1, 810), (13, 1, 825), (21, 1, 929), (17, 1, 1217), (14, 1, 858), (33, 1, 1273), (29, 1, 636), (28, 1, 629), (30, 1, 972), (31, 1, 979), (35, 1, 1273), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 5, 6, 7, 13, 18, 20, 23, 21, 22, 24, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 10, 1, 11, 13, 14, 12, 15, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [11, 4]) (W := 14368) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78253 : P.leaf 36 78253 = 10240 := by
  exact leaf_contract_factors (k := 36) (b := 14) (H := 78253) (ss := [(19, 3, 524), (36, 1, 531), (33, 3, 536), (16, 1, 867), (37, 1, 874), (11, 1, 879), (12, 1, 880), (10, 1, 809), (3, 1, 1273), (29, 1, 636), (28, 1, 629), (15, 1, 916), (14, 1, 858), (21, 1, 916), (13, 1, 818), (30, 1, 972), (31, 1, 979), (18, 1, 1210), (17, 1, 1217), (35, 1, 1273), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 20, 5, 6, 7, 18, 21, 22, 23, 24, 25]) (cs := [2, 1, 3, 4, 5, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 6, 11, 12, 13, 14, 15, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [5, 9]) (W := 10240) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78254 : P.leaf 36 78254 = 13952 := by
  exact leaf_contract_factors (k := 36) (b := 14) (H := 78254) (ss := [(19, 3, 524), (36, 1, 531), (3, 1, 536), (35, 16, 867), (37, 1, 874), (16, 11, 879), (12, 1, 880), (10, 1, 809), (11, 1, 809), (8, 1, 465), (14, 1, 465), (18, 1, 517), (6, 1, 419), (29, 1, 636), (28, 1, 629), (17, 1, 859), (30, 1, 972), (31, 1, 979), (21, 1, 1259), (33, 1, 1273), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 2, 3, 7, 13, 18, 20, 23, 5, 11, 21, 22, 24, 25]) (cs := [2, 1, 3, 4, 1, 10, 1, 5, 1, 1, 1, 11, 1, 6, 1, 1, 1, 1, 7, 1, 8, 12, 13, 9, 14, 15, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [8, 6]) (W := 13952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78255 : P.leaf 36 78255 = 69488 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 78255) (ss := [(19, 3, 524), (36, 1, 531), (3, 1, 536), (16, 1, 867), (37, 1, 874), (11, 1, 879), (12, 1, 880), (33, 1, 1273), (29, 1, 636), (28, 1, 629), (30, 1, 972), (31, 1, 979), (35, 1, 1273), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 9, 1, 1, 10, 11, 12, 1, 13, 14, 1, 15, 16, 17, 18, 19, 20, 21, 22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [19, 2]) (W := 69488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78262 : P.CoversSplit 26 10 78262 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78262_0 : P.sumLeaves 26 80140288 1024 = 19391 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78262) (lo := 0) (len := 1024) (W := 19391) check rows elimOK (by decide) (by decide) cover78262 (by decide)
  decide +kernel

theorem h78262 : P.leaf 36 78262 = 19391 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19391)]) (.cons c78262_0 (.nil)) (by decide) (by decide))

theorem cover78263 : P.CoversSplit 26 10 78263 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78263_0 : P.sumLeaves 26 80141312 1024 = 161699 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78263) (lo := 0) (len := 1024) (W := 161699) check rows elimOK (by decide) (by decide) cover78263 (by decide)
  decide +kernel

theorem h78263 : P.leaf 36 78263 = 161699 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 161699)]) (.cons c78263_0 (.nil)) (by decide) (by decide))

theorem h78265 : P.leaf 36 78265 = 24128 := by
  exact leaf_contract_factors (k := 36) (b := 16) (H := 78265) (ss := [(37, 1, 482), (36, 1, 531), (18, 1, 537), (11, 1, 879), (7, 1, 460), (12, 1, 460), (10, 1, 809), (13, 1, 818), (21, 1, 929), (17, 1, 1217), (33, 1, 1273), (29, 1, 636), (28, 1, 629), (30, 1, 972), (31, 1, 979), (15, 1, 916), (35, 1, 1273), (16, 1, 1210), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 12, 17, 18, 20, 23, 6, 21, 22, 24, 25]) (cs := [2, 3, 4, 5, 6, 1, 13, 7, 1, 1, 1, 1, 8, 1, 1, 1, 1, 9, 10, 1, 11, 14, 15, 12, 16, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [11, 5]) (W := 24128) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78267 : P.leaf 36 78267 = 78016 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 78267) (ss := [(37, 1, 482), (36, 1, 531), (18, 1, 537), (11, 1, 879), (10, 1, 810), (12, 1, 810), (13, 1, 825), (21, 1, 929), (17, 1, 1217), (33, 1, 1273), (29, 1, 636), (28, 1, 629), (30, 1, 972), (31, 1, 979), (35, 1, 1273), (16, 1, 1210), (32, 1, 1315), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 17, 18, 20, 23, 21, 22, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 10, 11, 1, 1, 1, 12, 13, 1, 14, 16, 17, 15, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [14, 4]) (W := 78016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78268 : P.CoversSplit 26 10 78268 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78268_0 : P.sumLeaves 26 80146432 1024 = 17680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78268) (lo := 0) (len := 1024) (W := 17680) check rows elimOK (by decide) (by decide) cover78268 (by decide)
  decide +kernel

theorem h78268 : P.leaf 36 78268 = 17680 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17680)]) (.cons c78268_0 (.nil)) (by decide) (by decide))

theorem cover78269 : P.CoversSplit 26 10 78269 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78269_0 : P.sumLeaves 26 80147456 1024 = 65456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78269) (lo := 0) (len := 1024) (W := 65456) check rows elimOK (by decide) (by decide) cover78269 (by decide)
  decide +kernel

theorem h78269 : P.leaf 36 78269 = 65456 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65456)]) (.cons c78269_0 (.nil)) (by decide) (by decide))

theorem cover78270 : P.CoversSplit 26 10 78270 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78270_0 : P.sumLeaves 26 80148480 1024 = 72648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78270) (lo := 0) (len := 1024) (W := 72648) check rows elimOK (by decide) (by decide) cover78270 (by decide)
  decide +kernel

theorem h78270 : P.leaf 36 78270 = 72648 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 72648)]) (.cons c78270_0 (.nil)) (by decide) (by decide))

theorem cover78271 : P.CoversSplit 26 10 78271 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78271_0 : P.sumLeaves 26 80149504 1024 = 376088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78271) (lo := 0) (len := 1024) (W := 376088) check rows elimOK (by decide) (by decide) cover78271 (by decide)
  decide +kernel

theorem h78271 : P.leaf 36 78271 = 376088 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 376088)]) (.cons c78271_0 (.nil)) (by decide) (by decide))

theorem cover78285 : P.CoversSplit 26 10 78285 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78285_0 : P.sumLeaves 26 80163840 1024 = 13920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78285) (lo := 0) (len := 1024) (W := 13920) check rows elimOK (by decide) (by decide) cover78285 (by decide)
  decide +kernel

theorem h78285 : P.leaf 36 78285 = 13920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13920)]) (.cons c78285_0 (.nil)) (by decide) (by decide))

theorem h78286 : P.leaf 36 78286 = 13440 := by
  exact leaf_contract_factors (k := 36) (b := 14) (H := 78286) (ss := [(10, 1, 467), (3, 1, 472), (37, 1, 531), (35, 16, 867), (17, 1, 874), (5, 1, 418), (8, 1, 515), (16, 1, 515), (29, 1, 636), (11, 1, 809), (12, 1, 810), (14, 1, 858), (36, 1, 923), (28, 1, 629), (30, 1, 972), (31, 1, 979), (18, 1, 1210), (21, 1, 1272), (32, 1, 1315), (33, 1, 1322), (19, 1, 1259), (34, 1, 1658)]) (ids := [2, 4, 20, 7, 13, 18, 23, 0, 5, 11, 21, 22, 24, 25]) (cs := [9, 1, 2, 1, 3, 10, 1, 5, 1, 1, 1, 11, 1, 6, 1, 1, 1, 1, 7, 1, 4, 12, 13, 8, 14, 15, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [3, 4, 7]) (W := 13440) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78287 : P.CoversSplit 26 10 78287 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78287_0 : P.sumLeaves 26 80165888 1024 = 90016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78287) (lo := 0) (len := 1024) (W := 90016) check rows elimOK (by decide) (by decide) cover78287 (by decide)
  decide +kernel

theorem h78287 : P.leaf 36 78287 = 90016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 90016)]) (.cons c78287_0 (.nil)) (by decide) (by decide))

theorem h78300 : P.leaf 36 78300 = 26048 := by
  exact leaf_contract_factors (k := 36) (b := 16) (H := 78300) (ss := [(32, 10, 467), (15, 1, 472), (10, 1, 479), (37, 1, 531), (28, 1, 629), (36, 1, 629), (29, 1, 636), (35, 1, 867), (17, 1, 874), (12, 1, 810), (11, 1, 809), (14, 1, 858), (16, 1, 858), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (13, 1, 818), (33, 1, 1322), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 6, 17, 18, 20, 23, 5, 7, 21, 22, 24, 25]) (cs := [2, 3, 4, 5, 6, 12, 7, 13, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9, 1, 10, 14, 15, 11, 16, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [10, 6]) (W := 26048) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78301 : P.CoversSplit 26 10 78301 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78301_0 : P.sumLeaves 26 80180224 1024 = 104840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78301) (lo := 0) (len := 1024) (W := 104840) check rows elimOK (by decide) (by decide) cover78301 (by decide)
  decide +kernel

theorem h78301 : P.leaf 36 78301 = 104840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 104840)]) (.cons c78301_0 (.nil)) (by decide) (by decide))

theorem h78302 : P.leaf 36 78302 = 73152 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 78302) (ss := [(10, 1, 467), (37, 1, 531), (35, 1, 867), (29, 1, 636), (17, 1, 874), (12, 1, 810), (11, 1, 809), (14, 1, 858), (16, 1, 858), (36, 1, 923), (28, 1, 629), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (32, 1, 1315), (33, 1, 1322), (34, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 6, 7, 11, 13, 17, 18, 20, 23, 5, 21, 22, 24, 25]) (cs := [2, 3, 4, 5, 6, 15, 7, 8, 1, 1, 1, 9, 1, 10, 1, 1, 1, 11, 12, 1, 13, 16, 17, 14, 18, 19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [13, 5]) (W := 73152) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78303 : P.CoversSplit 26 10 78303 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78303_0 : P.sumLeaves 26 80182272 1024 = 665272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78303) (lo := 0) (len := 1024) (W := 665272) check rows elimOK (by decide) (by decide) cover78303 (by decide)
  decide +kernel

theorem h78303 : P.leaf 36 78303 = 665272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 665272)]) (.cons c78303_0 (.nil)) (by decide) (by decide))

theorem cover78317 : P.CoversSplit 26 10 78317 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78317_0 : P.sumLeaves 26 80196608 1024 = 68352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78317) (lo := 0) (len := 1024) (W := 68352) check rows elimOK (by decide) (by decide) cover78317 (by decide)
  decide +kernel

theorem h78317 : P.leaf 36 78317 = 68352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68352)]) (.cons c78317_0 (.nil)) (by decide) (by decide))

theorem cover78318 : P.CoversSplit 26 10 78318 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78318_0 : P.sumLeaves 26 80197632 1024 = 73872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78318) (lo := 0) (len := 1024) (W := 73872) check rows elimOK (by decide) (by decide) cover78318 (by decide)
  decide +kernel

theorem h78318 : P.leaf 36 78318 = 73872 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 73872)]) (.cons c78318_0 (.nil)) (by decide) (by decide))

theorem cover78319 : P.CoversSplit 26 10 78319 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78319_0 : P.sumLeaves 26 80198656 1024 = 638200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78319) (lo := 0) (len := 1024) (W := 638200) check rows elimOK (by decide) (by decide) cover78319 (by decide)
  decide +kernel

theorem h78319 : P.leaf 36 78319 = 638200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 638200)]) (.cons c78319_0 (.nil)) (by decide) (by decide))

theorem cover78334 : P.CoversSplit 26 10 78334 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78334_0 : P.sumLeaves 26 80214016 1024 = 350692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78334) (lo := 0) (len := 1024) (W := 350692) check rows elimOK (by decide) (by decide) cover78334 (by decide)
  decide +kernel

theorem h78334 : P.leaf 36 78334 = 350692 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 350692)]) (.cons c78334_0 (.nil)) (by decide) (by decide))

theorem cover78335 : P.CoversSplit 26 10 78335 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78335_0 : P.sumLeaves 26 80215040 1024 = 6302754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78335) (lo := 0) (len := 1024) (W := 6302754) check rows elimOK (by decide) (by decide) cover78335 (by decide)
  decide +kernel

theorem h78335 : P.leaf 36 78335 = 6302754 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6302754)]) (.cons c78335_0 (.nil)) (by decide) (by decide))

theorem h78593 : P.leaf 36 78593 = 64 := by
  exact leaf_contract_factors (k := 36) (b := 6) (H := 78593) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (28, 1, 474), (2, 1, 475), (4, 1, 410), (5, 1, 411), (3, 1, 417), (6, 1, 412), (12, 1, 479), (7, 1, 460), (9, 1, 480), (15, 1, 473), (30, 1, 481), (31, 1, 487), (29, 1, 489), (8, 1, 515), (19, 1, 522), (32, 1, 530), (33, 1, 536), (20, 1, 572), (34, 1, 579), (10, 1, 809), (13, 1, 818), (14, 1, 858), (21, 1, 916), (36, 1, 923), (35, 1, 930), (37, 1, 979), (18, 1, 1210)]) (ids := [20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 6]) (W := 64) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78595 : P.leaf 36 78595 = 512 := by
  exact leaf_contract_factors (k := 36) (b := 9) (H := 78595) (ss := [(12, 1, 479), (2, 1, 482), (5, 1, 411), (3, 1, 419), (6, 1, 419), (31, 1, 488), (28, 1, 523), (30, 1, 481), (9, 1, 529), (19, 1, 522), (32, 1, 530), (33, 1, 537), (29, 1, 489), (34, 1, 579), (10, 1, 810), (16, 1, 867), (8, 1, 515), (17, 1, 516), (14, 1, 858), (11, 1, 879), (21, 1, 929), (13, 1, 818), (35, 1, 930), (36, 1, 972), (37, 1, 979), (18, 1, 1210), (20, 1, 1609)]) (ids := [2, 5, 13, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6, 7, 8, 9, 10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 9]) (W := 512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

def seg : List (ℕ × ℕ) := [(78206, 360), (78207, 360), (78245, 360), (78246, 360), (78247, 720), (78249, 720), (78251, 720), (78253, 720), (78254, 720), (78255, 720), (78262, 180), (78263, 360), (78265, 720), (78267, 720), (78268, 720), (78269, 720), (78270, 720), (78271, 720), (78285, 720), (78286, 720), (78287, 720), (78300, 720), (78301, 720), (78302, 720), (78303, 720), (78317, 360), (78318, 720), (78319, 720), (78334, 360), (78335, 360), (78593, 30), (78595, 240)]

theorem segOK : checkSeg 20 perms 78206 78599 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78206 78599 18450 4952418540 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4952418540)
    (SegSum.cons (w := 360) h78206 (SegSum.cons (w := 360) h78207 (SegSum.cons (w := 360) h78245 (SegSum.cons (w := 360) h78246 (SegSum.cons (w := 720) h78247 (SegSum.cons (w := 720) h78249 (SegSum.cons (w := 720) h78251 (SegSum.cons (w := 720) h78253 (SegSum.cons (w := 720) h78254 (SegSum.cons (w := 720) h78255 (SegSum.cons (w := 180) h78262 (SegSum.cons (w := 360) h78263 (SegSum.cons (w := 720) h78265 (SegSum.cons (w := 720) h78267 (SegSum.cons (w := 720) h78268 (SegSum.cons (w := 720) h78269 (SegSum.cons (w := 720) h78270 (SegSum.cons (w := 720) h78271 (SegSum.cons (w := 720) h78285 (SegSum.cons (w := 720) h78286 (SegSum.cons (w := 720) h78287 (SegSum.cons (w := 720) h78300 (SegSum.cons (w := 720) h78301 (SegSum.cons (w := 720) h78302 (SegSum.cons (w := 720) h78303 (SegSum.cons (w := 360) h78317 (SegSum.cons (w := 720) h78318 (SegSum.cons (w := 720) h78319 (SegSum.cons (w := 360) h78334 (SegSum.cons (w := 360) h78335 (SegSum.cons (w := 30) h78593 (SegSum.cons (w := 240) h78595 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S42
