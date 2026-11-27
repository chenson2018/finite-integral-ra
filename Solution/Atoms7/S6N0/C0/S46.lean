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

namespace RACert.S6N0.C0.S46

open RACert RACert.Problem

theorem cover79279 : P.CoversSplit 26 10 79279 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79279_0 : P.sumLeaves 26 81181696 1024 = 473696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79279) (lo := 0) (len := 1024) (W := 473696) check rows elimOK (by decide) (by decide) cover79279 (by decide)
  decide +kernel

theorem h79279 : P.leaf 36 79279 = 473696 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 473696)]) (.cons c79279_0 (.nil)) (by decide) (by decide))

theorem cover79287 : P.CoversSplit 26 10 79287 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c79287_0 : P.sumLeaves 26 81189888 1024 = 914628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79287) (lo := 0) (len := 1024) (W := 914628) check rows elimOK (by decide) (by decide) cover79287 (by decide)
  decide +kernel

theorem h79287 : P.leaf 36 79287 = 914628 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 914628)]) (.cons c79287_0 (.nil)) (by decide) (by decide))

theorem cover79292 : P.CoversSplit 26 10 79292 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79292_0 : P.sumLeaves 26 81195008 1024 = 320956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79292) (lo := 0) (len := 1024) (W := 320956) check rows elimOK (by decide) (by decide) cover79292 (by decide)
  decide +kernel

theorem h79292 : P.leaf 36 79292 = 320956 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 320956)]) (.cons c79292_0 (.nil)) (by decide) (by decide))

theorem cover79293 : P.CoversSplit 26 10 79293 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79293_0 : P.sumLeaves 26 81196032 1024 = 943900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79293) (lo := 0) (len := 1024) (W := 943900) check rows elimOK (by decide) (by decide) cover79293 (by decide)
  decide +kernel

theorem h79293 : P.leaf 36 79293 = 943900 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 943900)]) (.cons c79293_0 (.nil)) (by decide) (by decide))

theorem cover79294 : P.CoversSplit 26 10 79294 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79294_0 : P.sumLeaves 26 81197056 1024 = 605376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79294) (lo := 0) (len := 1024) (W := 605376) check rows elimOK (by decide) (by decide) cover79294 (by decide)
  decide +kernel

theorem h79294 : P.leaf 36 79294 = 605376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 605376)]) (.cons c79294_0 (.nil)) (by decide) (by decide))

theorem cover79295 : P.CoversSplit 26 10 79295 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79295_0 : P.sumLeaves 26 81198080 1024 = 1988188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79295) (lo := 0) (len := 1024) (W := 1988188) check rows elimOK (by decide) (by decide) cover79295 (by decide)
  decide +kernel

theorem h79295 : P.leaf 36 79295 = 1988188 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1988188)]) (.cons c79295_0 (.nil)) (by decide) (by decide))

theorem h79308 : P.leaf 36 79308 = 53960 := by
  exact leaf_contract_factors (k := 36) (b := 17) (H := 79308) (ss := [(32, 1, 467), (8, 1, 472), (3, 1, 479), (37, 1, 531), (28, 1, 629), (36, 1, 629), (29, 1, 636), (17, 1, 874), (5, 1, 418), (16, 1, 515), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (19, 1, 1259), (33, 1, 1322), (34, 1, 1658), (35, 1, 1665)]) (ids := [0, 2, 4, 5, 7, 8, 9, 10, 11, 12, 18, 20, 21, 23, 22, 24, 25]) (cs := [2, 1, 3, 1, 4, 5, 1, 6, 7, 8, 9, 10, 11, 1, 1, 1, 1, 1, 12, 1, 13, 14, 16, 15, 17, 18, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [14, 3]) (W := 53960) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79309 : P.CoversSplit 26 10 79309 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79309_0 : P.sumLeaves 26 81212416 1024 = 230856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79309) (lo := 0) (len := 1024) (W := 230856) check rows elimOK (by decide) (by decide) cover79309 (by decide)
  decide +kernel

theorem h79309 : P.leaf 36 79309 = 230856 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 230856)]) (.cons c79309_0 (.nil)) (by decide) (by decide))

theorem cover79310 : P.CoversSplit 26 10 79310 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79310_0 : P.sumLeaves 26 81213440 1024 = 95864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79310) (lo := 0) (len := 1024) (W := 95864) check rows elimOK (by decide) (by decide) cover79310 (by decide)
  decide +kernel

theorem h79310 : P.leaf 36 79310 = 95864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 95864)]) (.cons c79310_0 (.nil)) (by decide) (by decide))

theorem cover79311 : P.CoversSplit 26 10 79311 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79311_0 : P.sumLeaves 26 81214464 1024 = 440632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79311) (lo := 0) (len := 1024) (W := 440632) check rows elimOK (by decide) (by decide) cover79311 (by decide)
  decide +kernel

theorem h79311 : P.leaf 36 79311 = 440632 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 440632)]) (.cons c79311_0 (.nil)) (by decide) (by decide))

theorem h79324 : P.leaf 36 79324 = 670560 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79324) (ss := [(32, 1, 467), (37, 1, 531), (28, 1, 629), (36, 1, 629), (29, 1, 636), (17, 1, 874), (30, 1, 972), (31, 1, 979), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (33, 1, 1322), (34, 1, 1658), (35, 1, 1665)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 17, 18, 20, 21, 23, 22, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1, 15, 1, 1, 16, 17, 1, 18, 19, 21, 20, 22, 23, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [19, 3]) (W := 670560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79325 : P.CoversSplit 26 10 79325 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79325_0 : P.sumLeaves 26 81228800 1024 = 1085992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79325) (lo := 0) (len := 1024) (W := 1085992) check rows elimOK (by decide) (by decide) cover79325 (by decide)
  decide +kernel

theorem h79325 : P.leaf 36 79325 = 1085992 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1085992)]) (.cons c79325_0 (.nil)) (by decide) (by decide))

theorem cover79326 : P.CoversSplit 26 10 79326 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79326_0 : P.sumLeaves 26 81229824 1024 = 1148064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79326) (lo := 0) (len := 1024) (W := 1148064) check rows elimOK (by decide) (by decide) cover79326 (by decide)
  decide +kernel

theorem h79326 : P.leaf 36 79326 = 1148064 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1148064)]) (.cons c79326_0 (.nil)) (by decide) (by decide))

theorem cover79327 : P.CoversSplit 26 10 79327 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79327_0 : P.sumLeaves 26 81230848 1024 = 2050886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79327) (lo := 0) (len := 1024) (W := 2050886) check rows elimOK (by decide) (by decide) cover79327 (by decide)
  decide +kernel

theorem h79327 : P.leaf 36 79327 = 2050886 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2050886)]) (.cons c79327_0 (.nil)) (by decide) (by decide))

theorem cover79340 : P.CoversSplit 26 10 79340 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79340_0 : P.sumLeaves 26 81244160 1024 = 1098268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79340) (lo := 0) (len := 1024) (W := 1098268) check rows elimOK (by decide) (by decide) cover79340 (by decide)
  decide +kernel

theorem h79340 : P.leaf 36 79340 = 1098268 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1098268)]) (.cons c79340_0 (.nil)) (by decide) (by decide))

theorem cover79341 : P.CoversSplit 26 10 79341 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79341_0 : P.sumLeaves 26 81245184 1024 = 1280980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79341) (lo := 0) (len := 1024) (W := 1280980) check rows elimOK (by decide) (by decide) cover79341 (by decide)
  decide +kernel

theorem h79341 : P.leaf 36 79341 = 1280980 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1280980)]) (.cons c79341_0 (.nil)) (by decide) (by decide))

theorem cover79342 : P.CoversSplit 26 10 79342 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79342_0 : P.sumLeaves 26 81246208 1024 = 2153662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79342) (lo := 0) (len := 1024) (W := 2153662) check rows elimOK (by decide) (by decide) cover79342 (by decide)
  decide +kernel

theorem h79342 : P.leaf 36 79342 = 2153662 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2153662)]) (.cons c79342_0 (.nil)) (by decide) (by decide))

theorem cover79343 : P.CoversSplit 26 10 79343 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79343_0 : P.sumLeaves 26 81247232 1024 = 2861806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79343) (lo := 0) (len := 1024) (W := 2861806) check rows elimOK (by decide) (by decide) cover79343 (by decide)
  decide +kernel

theorem h79343 : P.leaf 36 79343 = 2861806 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2861806)]) (.cons c79343_0 (.nil)) (by decide) (by decide))

theorem cover79358 : P.CoversSplit 26 10 79358 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79358_0 : P.sumLeaves 26 81262592 1024 = 5471645 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79358) (lo := 0) (len := 1024) (W := 5471645) check rows elimOK (by decide) (by decide) cover79358 (by decide)
  decide +kernel

theorem h79358 : P.leaf 36 79358 = 5471645 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5471645)]) (.cons c79358_0 (.nil)) (by decide) (by decide))

theorem cover79359 : P.CoversSplit 26 10 79359 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79359_0 : P.sumLeaves 26 81263616 1024 = 8222582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79359) (lo := 0) (len := 1024) (W := 8222582) check rows elimOK (by decide) (by decide) cover79359 (by decide)
  decide +kernel

theorem h79359 : P.leaf 36 79359 = 8222582 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8222582)]) (.cons c79359_0 (.nil)) (by decide) (by decide))

theorem cover79451 : P.CoversSplit 26 10 79451 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 587, 622, 873, 930, 972, 1273, 1665]) (by decide +kernel)

theorem c79451_0 : P.sumLeaves 26 81357824 1024 = 28280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79451) (lo := 0) (len := 1024) (W := 28280) check rows elimOK (by decide) (by decide) cover79451 (by decide)
  decide +kernel

theorem h79451 : P.leaf 36 79451 = 28280 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28280)]) (.cons c79451_0 (.nil)) (by decide) (by decide))

theorem cover79454 : P.CoversSplit 26 10 79454 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 587, 622, 873, 880, 930, 1273, 1315, 1658]) (by decide +kernel)

theorem c79454_0 : P.sumLeaves 26 81360896 1024 = 198336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79454) (lo := 0) (len := 1024) (W := 198336) check rows elimOK (by decide) (by decide) cover79454 (by decide)
  decide +kernel

theorem h79454 : P.leaf 36 79454 = 198336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 198336)]) (.cons c79454_0 (.nil)) (by decide) (by decide))

theorem cover79455 : P.CoversSplit 26 10 79455 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 587, 622, 930, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c79455_0 : P.sumLeaves 26 81361920 1024 = 212668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79455) (lo := 0) (len := 1024) (W := 212668) check rows elimOK (by decide) (by decide) cover79455 (by decide)
  decide +kernel

theorem h79455 : P.leaf 36 79455 = 212668 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 212668)]) (.cons c79455_0 (.nil)) (by decide) (by decide))

theorem cover79486 : P.CoversSplit 26 10 79486 0xcc00cc00000000000000000000000000000000000000000000000000000000000000000000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 587, 622, 873, 874, 930, 972, 1273, 1658]) (ps := [(21, [929], [1658])]) (by decide +kernel)

noncomputable def f79486 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81393664 + i)

theorem c79486_0 : rowSum f79486 0 1024 = 1927200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79486) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79486 (by decide)
  decide +kernel

theorem sum79486 : rowSum f79486 0 1024 = 1927200 :=
  c79486_0

theorem h79486 : P.leaf 36 79486 = 1927200 :=
  leaf_weighted (k := 26) (d := 10) (H := 79486) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79486) (by decide) (by decide +kernel)) sum79486

theorem cover79487 : P.CoversSplit 26 10 79487 0xcc00cc00000000000000000000000000000000000000000000000000000000000000000000000000cc00c800000000000000000000000000000000000000000000000000003300320000000000000000000000000000000000000000000000000000000000000000000000000033003200000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 587, 622, 930, 972, 1273, 1658, 1665]) (ps := [(21, [929], [1658])]) (by decide +kernel)

noncomputable def f79487 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81394688 + i)

theorem c79487_0 : rowSum f79487 0 1024 = 2340579 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79487) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79487 (by decide)
  decide +kernel

theorem sum79487 : rowSum f79487 0 1024 = 2340579 :=
  c79487_0

theorem h79487 : P.leaf 36 79487 = 2340579 :=
  leaf_weighted (k := 26) (d := 10) (H := 79487) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79487) (by decide) (by decide +kernel)) sum79487

theorem cover79511 : P.CoversSplit 26 10 79511 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000000000000000000000000000000000000000000000000000000000000000300000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 615, 930, 979, 1315, 1658]) (by decide +kernel)

theorem c79511_0 : P.sumLeaves 26 81419264 320 = 224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79511) (lo := 0) (len := 320) (W := 224) check rows elimOK (by decide) (by decide) cover79511 (by decide)
  decide +kernel

theorem contract79511_1 : P.leaf 32 1272181 = 9072 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1272181) (ss := [(4, 1, 426), (21, 1, 426), (32, 3, 531), (3, 1, 537), (29, 0, 587), (33, 0, 489), (31, 0, 538), (13, 1, 488), (6, 1, 510), (27, 1, 636), (11, 1, 818), (17, 1, 874), (12, 1, 880), (16, 1, 1210), (18, 1, 1217)]) (ids := [0, 5, 6, 7, 13, 17, 18, 23, 28, 3, 20, 24, 26, 8, 12, 21, 22]) (cs := [2, 1, 1, 11, 1, 3, 4, 5, 15, 1, 1, 1, 16, 6, 1, 1, 1, 7, 8, 1, 12, 17, 18, 9, 13, 1, 14, 0, 10, 0, 1, 0]) (bs := [9, 4, 4]) (W := 9072) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79511_1 : P.sumLeaves 26 81419584 64 = 9072 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272181) rows (by decide) (by decide)).symm.trans contract79511_1

theorem c79511_2 : P.sumLeaves 26 81419648 512 = 576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79511) (lo := 384) (len := 512) (W := 576) check rows elimOK (by decide) (by decide) cover79511 (by decide)
  decide +kernel

theorem contract79511_3 : P.leaf 32 1272190 = 85248 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1272190) (ss := [(21, 1, 475), (29, 1, 489), (31, 1, 489), (32, 3, 531), (3, 1, 537), (33, 1, 538), (9, 1, 573), (6, 1, 580), (17, 1, 874), (12, 1, 880), (13, 1, 825), (15, 1, 916), (18, 1, 1217), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 2, 3, 5, 6, 8, 9, 12, 14, 20, 21, 22, 24, 26, 28, 23, 25]) (cs := [2, 1, 3, 4, 1, 5, 6, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 1, 11, 12, 13, 17, 14, 18, 15, 1, 16, 1, 1, 1]) (bs := [15, 2]) (W := 85248) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79511_3 : P.sumLeaves 26 81420160 64 = 85248 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272190) rows (by decide) (by decide)).symm.trans contract79511_3

theorem contract79511_4 : P.leaf 32 1272191 = 101376 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1272191) (ss := [(21, 1, 475), (29, 1, 489), (31, 1, 489), (32, 3, 531), (3, 1, 537), (33, 1, 538), (9, 1, 573), (17, 1, 874), (12, 1, 880), (13, 1, 825), (15, 1, 916), (18, 1, 1217), (6, 1, 419), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 2, 3, 5, 6, 8, 9, 12, 14, 20, 21, 28, 22, 23, 24, 25, 26]) (cs := [2, 1, 3, 4, 1, 5, 6, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 1, 11, 12, 14, 15, 16, 17, 18, 1, 13, 1, 1, 1]) (bs := [12, 5]) (W := 101376) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79511_4 : P.sumLeaves 26 81420224 64 = 101376 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272191) rows (by decide) (by decide)).symm.trans contract79511_4

theorem h79511 : P.leaf 36 79511 = 196496 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 224), (64, 9072), (512, 576), (64, 85248), (64, 101376)]) (.cons c79511_0 (.cons c79511_1 (.cons c79511_2 (.cons c79511_3 (.cons c79511_4 (.nil)))))) (by decide) (by decide))

theorem h79513 : P.leaf 36 79513 = 79360 := by
  exact leaf_contract_factors (k := 36) (b := 17) (H := 79513) (ss := [(17, 1, 467), (35, 1, 475), (21, 1, 524), (32, 3, 531), (18, 1, 536), (33, 3, 537), (12, 1, 880), (36, 1, 923), (13, 1, 825), (7, 1, 460), (3, 1, 1322), (29, 1, 587), (9, 1, 573), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (37, 1, 1322), (20, 1, 1609)]) (ids := [0, 2, 3, 4, 6, 8, 12, 14, 20, 22, 32, 9, 21, 23, 24, 25, 26]) (cs := [2, 1, 3, 4, 5, 1, 6, 1, 7, 13, 1, 1, 8, 1, 9, 1, 1, 1, 1, 1, 10, 14, 11, 15, 16, 17, 18, 1, 1, 1, 1, 1, 12, 1, 1, 1]) (bs := [11, 6]) (W := 79360) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79515 : P.CoversSplit 26 10 79515 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 587, 615, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem c79515_0 : P.sumLeaves 26 81423360 1024 = 144000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79515) (lo := 0) (len := 1024) (W := 144000) check rows elimOK (by decide) (by decide) cover79515 (by decide)
  decide +kernel

theorem h79515 : P.leaf 36 79515 = 144000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 144000)]) (.cons c79515_0 (.nil)) (by decide) (by decide))

theorem h79517 : P.leaf 36 79517 = 317232 := by
  exact leaf_contract_factors (k := 36) (b := 20) (H := 79517) (ss := [(35, 1, 475), (21, 1, 524), (32, 3, 531), (18, 1, 536), (3, 1, 537), (17, 1, 874), (12, 1, 880), (36, 1, 923), (33, 1, 1322), (29, 1, 587), (9, 1, 573), (15, 1, 916), (31, 1, 930), (19, 1, 1259), (37, 1, 1322), (20, 1, 1609)]) (ids := [0, 2, 3, 4, 5, 6, 8, 9, 11, 12, 14, 20, 21, 22, 24, 26, 28, 32, 23, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 1, 8, 9, 1, 10, 11, 1, 12, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 21, 17, 1, 18, 1, 1, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 317232) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79519 : P.CoversSplit 26 10 79519 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 587, 615, 930, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79519_0 : P.sumLeaves 26 81427456 896 = 3136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79519) (lo := 0) (len := 896) (W := 3136) check rows elimOK (by decide) (by decide) cover79519 (by decide)
  decide +kernel

theorem contract79519_1 : P.leaf 32 1272318 = 169728 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1272318) (ss := [(21, 1, 524), (32, 3, 531), (3, 1, 537), (29, 1, 587), (9, 1, 573), (17, 1, 874), (12, 1, 880), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 2, 3, 4, 5, 6, 8, 9, 11, 12, 14, 20, 21, 22, 24, 26, 28, 23, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 1, 8, 9, 1, 10, 11, 1, 12, 1, 1, 1, 1, 1, 13, 14, 15, 19, 16, 20, 17, 1, 18, 1, 1, 1]) (bs := [17, 2]) (W := 169728) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79519_1 : P.sumLeaves 26 81428352 64 = 169728 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272318) rows (by decide) (by decide)).symm.trans contract79519_1

theorem contract79519_2 : P.leaf 32 1272319 = 202368 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1272319) (ss := [(21, 1, 524), (32, 3, 531), (3, 1, 537), (29, 1, 587), (9, 1, 573), (17, 1, 874), (12, 1, 880), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 2, 3, 4, 5, 6, 8, 9, 11, 12, 14, 20, 21, 26, 28, 22, 23, 24, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 1, 8, 9, 1, 10, 11, 1, 12, 1, 1, 1, 1, 1, 13, 14, 17, 18, 19, 20, 15, 1, 16, 1, 1, 1]) (bs := [15, 4]) (W := 202368) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79519_2 : P.sumLeaves 26 81428416 64 = 202368 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272319) rows (by decide) (by decide)).symm.trans contract79519_2

theorem h79519 : P.leaf 36 79519 = 375232 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 3136), (64, 169728), (64, 202368)]) (.cons c79519_0 (.cons c79519_1 (.cons c79519_2 (.nil)))) (by decide) (by decide))

theorem cover79542 : P.CoversSplit 26 10 79542 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003000000000000000000000000000000000000000000000000000000000003300300000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 873, 930, 972, 979, 1658]) (by decide +kernel)

theorem c79542_0 : P.sumLeaves 26 81451008 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79542) (lo := 0) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover79542 (by decide)
  decide +kernel

theorem contract79542_1 : P.leaf 32 1272673 = 1064 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 1272673) (ss := [(4, 1, 426), (21, 1, 426), (29, 7, 468), (8, 7, 486), (2, 1, 488), (3, 1, 537), (7, 0, 587), (12, 0, 461), (11, 1, 458), (17, 0, 517), (16, 1, 465), (31, 0, 587), (33, 0, 587), (27, 6, 636), (20, 9, 1609)]) (ids := [3, 4, 7, 8, 11, 12, 13, 16, 17, 20, 21, 22, 23, 24, 26, 28, 30]) (cs := [1, 1, 1, 2, 3, 0, 0, 4, 5, 1, 0, 6, 7, 8, 1, 0, 9, 10, 4, 1, 11, 12, 13, 14, 15, 3, 16, 0, 17, 0, 18, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c79542_1 : P.sumLeaves 26 81451072 64 = 1064 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272673) rows (by decide) (by decide)).symm.trans contract79542_1

theorem c79542_2 : P.sumLeaves 26 81451136 576 = 6772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79542) (lo := 128) (len := 576) (W := 6772) check rows elimOK (by decide) (by decide) cover79542 (by decide)
  decide +kernel

theorem contract79542_3 : P.leaf 32 1272683 = 10240 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 1272683) (ss := [(29, 7, 468), (21, 1, 475), (8, 7, 486), (2, 1, 488), (7, 1, 489), (31, 1, 489), (3, 1, 537), (33, 1, 538), (9, 1, 573), (4, 1, 580), (12, 1, 825), (13, 1, 461), (17, 1, 874), (18, 1, 517), (15, 1, 916), (19, 1, 1259), (20, 1, 1609)]) (ids := [4, 20, 24, 26, 28, 30, 3, 8, 9, 12, 14, 21, 22, 23, 25]) (cs := [1, 1, 1, 8, 2, 1, 1, 1, 9, 10, 1, 1, 11, 1, 12, 1, 1, 1, 1, 1, 3, 13, 14, 15, 4, 16, 5, 1, 6, 1, 7, 1]) (bs := [6, 9]) (W := 10240) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79542_3 : P.sumLeaves 26 81451712 64 = 10240 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272683) rows (by decide) (by decide)).symm.trans contract79542_3

theorem c79542_4 : P.sumLeaves 26 81451776 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79542) (lo := 768) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover79542 (by decide)
  decide +kernel

theorem contract79542_5 : P.leaf 32 1272686 = 78336 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1272686) (ss := [(29, 7, 468), (21, 1, 475), (8, 7, 486), (7, 1, 489), (31, 1, 489), (33, 1, 538), (9, 1, 573), (6, 1, 580), (13, 1, 461), (18, 1, 517), (12, 1, 825), (17, 1, 874), (15, 1, 916), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 9, 14, 20, 24, 26, 28, 30, 8, 12, 21, 22, 23, 25]) (cs := [2, 3, 4, 5, 1, 1, 1, 1, 13, 6, 1, 1, 14, 1, 7, 1, 1, 1, 1, 1, 8, 15, 16, 17, 9, 18, 10, 1, 11, 1, 12, 1]) (bs := [11, 6]) (W := 78336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79542_5 : P.sumLeaves 26 81451904 64 = 78336 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272686) rows (by decide) (by decide)).symm.trans contract79542_5

theorem contract79542_6 : P.leaf 32 1272687 = 120832 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1272687) (ss := [(29, 7, 468), (21, 1, 475), (8, 7, 486), (7, 1, 489), (31, 1, 489), (33, 1, 538), (9, 1, 573), (12, 1, 825), (13, 1, 461), (17, 1, 874), (18, 1, 517), (15, 1, 916), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 8, 9, 12, 14, 20, 28, 30, 21, 22, 23, 24, 25, 26]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 1, 11, 14, 15, 16, 17, 18, 19, 1, 12, 1, 13, 1]) (bs := [12, 6]) (W := 120832) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79542_6 : P.sumLeaves 26 81451968 64 = 120832 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272687) rows (by decide) (by decide)).symm.trans contract79542_6

theorem h79542 : P.leaf 36 79542 = 217244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 1064), (576, 6772), (64, 10240), (128, 0), (64, 78336), (64, 120832)]) (.cons c79542_0 (.cons c79542_1 (.cons c79542_2 (.cons c79542_3 (.cons c79542_4 (.cons c79542_5 (.cons c79542_6 (.nil)))))))) (by decide) (by decide))

theorem cover79543 : P.CoversSplit 26 10 79543 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003000000000000000000000000000000000000000000000000000000000003300300000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 873, 930, 972, 979, 1658]) (by decide +kernel)

theorem c79543_0 : P.sumLeaves 26 81452032 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79543) (lo := 0) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover79543 (by decide)
  decide +kernel

theorem contract79543_1 : P.leaf 32 1272689 = 1316 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 1272689) (ss := [(4, 1, 426), (21, 1, 426), (2, 1, 488), (3, 1, 537), (29, 0, 587), (33, 0, 489), (31, 0, 538), (27, 6, 636), (11, 1, 818), (17, 1, 874), (12, 1, 880), (13, 7, 825), (16, 1, 1210), (18, 8, 1217), (20, 9, 1609)]) (ids := [3, 4, 5, 6, 7, 8, 12, 13, 17, 20, 21, 22, 23, 24, 26, 28, 30]) (cs := [1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 4, 8, 9, 1, 1, 5, 10, 6, 1, 11, 12, 13, 14, 15, 3, 16, 0, 17, 0, 18, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c79543_1 : P.sumLeaves 26 81452096 64 = 1316 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272689) rows (by decide) (by decide)).symm.trans contract79543_1

theorem c79543_2 : P.sumLeaves 26 81452160 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79543) (lo := 128) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover79543 (by decide)
  decide +kernel

theorem contract79543_3 : P.leaf 32 1272693 = 20412 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1272693) (ss := [(4, 1, 426), (21, 1, 426), (29, 0, 587), (33, 0, 489), (31, 0, 538), (27, 1, 636), (11, 1, 818), (17, 1, 874), (12, 1, 880), (13, 1, 825), (6, 1, 510), (16, 1, 1210), (18, 1, 1217)]) (ids := [0, 1, 3, 5, 6, 7, 13, 17, 18, 20, 23, 24, 26, 28, 30, 8, 12, 21, 22]) (cs := [2, 3, 1, 4, 1, 5, 6, 7, 17, 1, 1, 1, 18, 8, 1, 1, 1, 9, 10, 1, 11, 19, 20, 12, 13, 1, 14, 0, 15, 0, 16, 0]) (bs := [15, 4]) (W := 20412) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79543_3 : P.sumLeaves 26 81452352 64 = 20412 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272693) rows (by decide) (by decide)).symm.trans contract79543_3

theorem c79543_4 : P.sumLeaves 26 81452416 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79543) (lo := 384) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover79543 (by decide)
  decide +kernel

theorem contract79543_5 : P.leaf 32 1272699 = 40576 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1272699) (ss := [(21, 1, 475), (2, 1, 488), (29, 1, 489), (31, 1, 489), (3, 1, 537), (33, 1, 538), (9, 1, 573), (4, 1, 580), (17, 1, 874), (12, 1, 880), (15, 1, 916), (19, 1, 1259), (20, 1, 1609)]) (ids := [3, 4, 5, 6, 8, 9, 11, 12, 14, 16, 20, 21, 22, 24, 26, 28, 30, 23, 25]) (cs := [1, 1, 1, 2, 3, 4, 5, 1, 6, 7, 1, 8, 9, 1, 10, 1, 11, 1, 1, 1, 12, 13, 14, 19, 15, 20, 16, 1, 17, 1, 18, 1]) (bs := [17, 2]) (W := 40576) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79543_5 : P.sumLeaves 26 81452736 64 = 40576 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272699) rows (by decide) (by decide)).symm.trans contract79543_5

theorem c79543_6 : P.sumLeaves 26 81452800 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79543) (lo := 768) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover79543 (by decide)
  decide +kernel

theorem contract79543_7 : P.leaf 32 1272702 = 284384 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1272702) (ss := [(21, 1, 475), (29, 1, 489), (31, 1, 489), (33, 1, 538), (9, 1, 573), (6, 1, 580), (17, 1, 874), (12, 1, 880), (13, 1, 825), (15, 1, 916), (18, 1, 1217), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 5, 6, 8, 9, 12, 14, 20, 21, 22, 24, 26, 28, 30, 23, 25]) (cs := [2, 3, 4, 5, 1, 6, 7, 1, 8, 9, 1, 1, 10, 1, 11, 1, 1, 1, 1, 1, 12, 13, 14, 19, 15, 20, 16, 1, 17, 1, 18, 1]) (bs := [17, 2]) (W := 284384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79543_7 : P.sumLeaves 26 81452928 64 = 284384 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272702) rows (by decide) (by decide)).symm.trans contract79543_7

theorem contract79543_8 : P.leaf 32 1272703 = 430720 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1272703) (ss := [(21, 1, 475), (29, 1, 489), (31, 1, 489), (33, 1, 538), (9, 1, 573), (17, 1, 874), (12, 1, 880), (13, 1, 825), (15, 1, 916), (18, 1, 1217), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 12, 14, 20, 28, 30, 21, 22, 23, 24, 25, 26]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 1, 1, 11, 1, 12, 1, 1, 1, 1, 1, 13, 16, 17, 18, 19, 20, 21, 1, 14, 1, 15, 1]) (bs := [14, 6]) (W := 430720) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79543_8 : P.sumLeaves 26 81452992 64 = 430720 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272703) rows (by decide) (by decide)).symm.trans contract79543_8

theorem h79543 : P.leaf 36 79543 = 777408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 1316), (192, 0), (64, 20412), (320, 0), (64, 40576), (128, 0), (64, 284384), (64, 430720)]) (.cons c79543_0 (.cons c79543_1 (.cons c79543_2 (.cons c79543_3 (.cons c79543_4 (.cons c79543_5 (.cons c79543_6 (.cons c79543_7 (.cons c79543_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79279, 720), (79287, 180), (79292, 720), (79293, 720), (79294, 720), (79295, 720), (79308, 720), (79309, 720), (79310, 720), (79311, 720), (79324, 720), (79325, 720), (79326, 720), (79327, 720), (79340, 360), (79341, 360), (79342, 720), (79343, 720), (79358, 360), (79359, 360), (79451, 360), (79454, 720), (79455, 720), (79486, 360), (79487, 360), (79511, 360), (79513, 720), (79515, 720), (79517, 360), (79519, 360), (79542, 180), (79543, 360)]

theorem segOK : checkSeg 20 perms 79279 79544 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79279 79544 18000 19482970320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19482970320)
    (SegSum.cons (w := 720) h79279 (SegSum.cons (w := 180) h79287 (SegSum.cons (w := 720) h79292 (SegSum.cons (w := 720) h79293 (SegSum.cons (w := 720) h79294 (SegSum.cons (w := 720) h79295 (SegSum.cons (w := 720) h79308 (SegSum.cons (w := 720) h79309 (SegSum.cons (w := 720) h79310 (SegSum.cons (w := 720) h79311 (SegSum.cons (w := 720) h79324 (SegSum.cons (w := 720) h79325 (SegSum.cons (w := 720) h79326 (SegSum.cons (w := 720) h79327 (SegSum.cons (w := 360) h79340 (SegSum.cons (w := 360) h79341 (SegSum.cons (w := 720) h79342 (SegSum.cons (w := 720) h79343 (SegSum.cons (w := 360) h79358 (SegSum.cons (w := 360) h79359 (SegSum.cons (w := 360) h79451 (SegSum.cons (w := 720) h79454 (SegSum.cons (w := 720) h79455 (SegSum.cons (w := 360) h79486 (SegSum.cons (w := 360) h79487 (SegSum.cons (w := 360) h79511 (SegSum.cons (w := 720) h79513 (SegSum.cons (w := 720) h79515 (SegSum.cons (w := 360) h79517 (SegSum.cons (w := 360) h79519 (SegSum.cons (w := 180) h79542 (SegSum.cons (w := 360) h79543 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S46
