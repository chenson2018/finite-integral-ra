/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S50

open RACert RACert.Problem

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

theorem cover79308 : P.CoversSplit 26 10 79308 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 531, 629, 636, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c79308_0 : P.sumLeaves 26 81211392 1024 = 53960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79308) (lo := 0) (len := 1024) (W := 53960) check rows elimOK (by decide) (by decide) cover79308 (by decide)
  decide +kernel

theorem h79308 : P.leaf 36 79308 = 53960 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 53960)]) (.cons c79308_0 (.nil)) (by decide) (by decide))

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

theorem cover79324 : P.CoversSplit 26 10 79324 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 531, 629, 636, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c79324_0 : P.sumLeaves 26 81227776 1024 = 670560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79324) (lo := 0) (len := 1024) (W := 670560) check rows elimOK (by decide) (by decide) cover79324 (by decide)
  decide +kernel

theorem h79324 : P.leaf 36 79324 = 670560 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 670560)]) (.cons c79324_0 (.nil)) (by decide) (by decide))

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

theorem cover79486 : P.CoversSplit 26 10 79486 0xcc00cc0000000000000000000000000000000000000000000000000000000000cc00c80000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 622, 873, 874, 930, 972, 1273, 1658]) (by decide +kernel)

theorem c79486_0 : P.sumLeaves 26 81393664 1024 = 1927200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79486) (lo := 0) (len := 1024) (W := 1927200) check rows elimOK (by decide) (by decide) cover79486 (by decide)
  decide +kernel

theorem h79486 : P.leaf 36 79486 = 1927200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1927200)]) (.cons c79486_0 (.nil)) (by decide) (by decide))

theorem cover79487 : P.CoversSplit 26 10 79487 0xcc00cc0000000000000000000000000000000000000000000000000000000000cc00c80000000000cc00c800000000000000000000000000000000000000000000000000003300320000000000000000000000000000000000000000000000000000000000330032000000000033003200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 622, 930, 972, 1273, 1658, 1665]) (by decide +kernel)

theorem c79487_0 : P.sumLeaves 26 81394688 1024 = 2340579 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79487) (lo := 0) (len := 1024) (W := 2340579) check rows elimOK (by decide) (by decide) cover79487 (by decide)
  decide +kernel

theorem h79487 : P.leaf 36 79487 = 2340579 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2340579)]) (.cons c79487_0 (.nil)) (by decide) (by decide))

theorem cover79511 : P.CoversSplit 26 10 79511 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000000000000000000000000000000000000000000000000000000000000000300000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 615, 930, 979, 1315, 1658]) (by decide +kernel)

theorem c79511_0 : P.sumLeaves 26 81419264 1024 = 196496 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79511) (lo := 0) (len := 1024) (W := 196496) check rows elimOK (by decide) (by decide) cover79511 (by decide)
  decide +kernel

theorem h79511 : P.leaf 36 79511 = 196496 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 196496)]) (.cons c79511_0 (.nil)) (by decide) (by decide))

theorem cover79513 : P.CoversSplit 26 10 79513 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 530, 587, 615, 923, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem c79513_0 : P.sumLeaves 26 81421312 1024 = 79360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79513) (lo := 0) (len := 1024) (W := 79360) check rows elimOK (by decide) (by decide) cover79513 (by decide)
  decide +kernel

theorem h79513 : P.leaf 36 79513 = 79360 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 79360)]) (.cons c79513_0 (.nil)) (by decide) (by decide))

theorem cover79515 : P.CoversSplit 26 10 79515 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 587, 615, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem c79515_0 : P.sumLeaves 26 81423360 1024 = 144000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79515) (lo := 0) (len := 1024) (W := 144000) check rows elimOK (by decide) (by decide) cover79515 (by decide)
  decide +kernel

theorem h79515 : P.leaf 36 79515 = 144000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 144000)]) (.cons c79515_0 (.nil)) (by decide) (by decide))

theorem cover79517 : P.CoversSplit 26 10 79517 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 530, 587, 615, 923, 930, 1273, 1322]) (by decide +kernel)

theorem c79517_0 : P.sumLeaves 26 81425408 1024 = 317232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79517) (lo := 0) (len := 1024) (W := 317232) check rows elimOK (by decide) (by decide) cover79517 (by decide)
  decide +kernel

theorem h79517 : P.leaf 36 79517 = 317232 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 317232)]) (.cons c79517_0 (.nil)) (by decide) (by decide))

theorem cover79519 : P.CoversSplit 26 10 79519 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 587, 615, 930, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79519_0 : P.sumLeaves 26 81427456 1024 = 375232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79519) (lo := 0) (len := 1024) (W := 375232) check rows elimOK (by decide) (by decide) cover79519 (by decide)
  decide +kernel

theorem h79519 : P.leaf 36 79519 = 375232 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 375232)]) (.cons c79519_0 (.nil)) (by decide) (by decide))

theorem cover79542 : P.CoversSplit 26 10 79542 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003000000000000000000000000000000000000000000000000000000000003300300000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 873, 930, 972, 979, 1658]) (by decide +kernel)

theorem c79542_0 : P.sumLeaves 26 81451008 1024 = 217244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79542) (lo := 0) (len := 1024) (W := 217244) check rows elimOK (by decide) (by decide) cover79542 (by decide)
  decide +kernel

theorem h79542 : P.leaf 36 79542 = 217244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 217244)]) (.cons c79542_0 (.nil)) (by decide) (by decide))

theorem cover79543 : P.CoversSplit 26 10 79543 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003000000000000000000000000000000000000000000000000000000000003300300000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 873, 930, 972, 979, 1658]) (by decide +kernel)

theorem c79543_0 : P.sumLeaves 26 81452032 1024 = 777408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79543) (lo := 0) (len := 1024) (W := 777408) check rows elimOK (by decide) (by decide) cover79543 (by decide)
  decide +kernel

theorem h79543 : P.leaf 36 79543 = 777408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 777408)]) (.cons c79543_0 (.nil)) (by decide) (by decide))

theorem cover79544 : P.CoversSplit 26 10 79544 0xc000c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 587, 873, 874, 923, 930, 972, 1273]) (by decide +kernel)

theorem c79544_0 : P.sumLeaves 26 81453056 1024 = 10752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79544) (lo := 0) (len := 1024) (W := 10752) check rows elimOK (by decide) (by decide) cover79544 (by decide)
  decide +kernel

theorem h79544 : P.leaf 36 79544 = 10752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10752)]) (.cons c79544_0 (.nil)) (by decide) (by decide))

theorem cover79545 : P.CoversSplit 26 10 79545 0xc000c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 587, 923, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem c79545_0 : P.sumLeaves 26 81454080 1024 = 216480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79545) (lo := 0) (len := 1024) (W := 216480) check rows elimOK (by decide) (by decide) cover79545 (by decide)
  decide +kernel

theorem h79545 : P.leaf 36 79545 = 216480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 216480)]) (.cons c79545_0 (.nil)) (by decide) (by decide))

theorem cover79546 : P.CoversSplit 26 10 79546 0xc000c00000000000c000c0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 873, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79546_0 : P.sumLeaves 26 81455104 1024 = 222112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79546) (lo := 0) (len := 1024) (W := 222112) check rows elimOK (by decide) (by decide) cover79546 (by decide)
  decide +kernel

theorem h79546 : P.leaf 36 79546 = 222112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 222112)]) (.cons c79546_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79293, 720), (79294, 720), (79295, 720), (79308, 720), (79309, 720), (79310, 720), (79311, 720), (79324, 720), (79325, 720), (79326, 720), (79327, 720), (79340, 360), (79341, 360), (79342, 720), (79343, 720), (79358, 360), (79359, 360), (79451, 360), (79454, 720), (79455, 720), (79486, 360), (79487, 360), (79511, 360), (79513, 720), (79515, 720), (79517, 360), (79519, 360), (79542, 180), (79543, 360), (79544, 720), (79545, 720), (79546, 720)]

theorem segOK : checkSeg 20 perms 79293 79547 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79293 79547 18540 19069715520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19069715520)
    (SegSum.cons (w := 720) h79293 (SegSum.cons (w := 720) h79294 (SegSum.cons (w := 720) h79295 (SegSum.cons (w := 720) h79308 (SegSum.cons (w := 720) h79309 (SegSum.cons (w := 720) h79310 (SegSum.cons (w := 720) h79311 (SegSum.cons (w := 720) h79324 (SegSum.cons (w := 720) h79325 (SegSum.cons (w := 720) h79326 (SegSum.cons (w := 720) h79327 (SegSum.cons (w := 360) h79340 (SegSum.cons (w := 360) h79341 (SegSum.cons (w := 720) h79342 (SegSum.cons (w := 720) h79343 (SegSum.cons (w := 360) h79358 (SegSum.cons (w := 360) h79359 (SegSum.cons (w := 360) h79451 (SegSum.cons (w := 720) h79454 (SegSum.cons (w := 720) h79455 (SegSum.cons (w := 360) h79486 (SegSum.cons (w := 360) h79487 (SegSum.cons (w := 360) h79511 (SegSum.cons (w := 720) h79513 (SegSum.cons (w := 720) h79515 (SegSum.cons (w := 360) h79517 (SegSum.cons (w := 360) h79519 (SegSum.cons (w := 180) h79542 (SegSum.cons (w := 360) h79543 (SegSum.cons (w := 720) h79544 (SegSum.cons (w := 720) h79545 (SegSum.cons (w := 720) h79546 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S50
