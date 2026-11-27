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

namespace RACert.S6N0.C0.S16

open RACert RACert.Problem

theorem cover11480 : P.CoversSplit 26 10 11480 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11480_0 : P.sumLeaves 26 11755520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11480) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11480 (by decide)
  decide +kernel

theorem h11480 : P.leaf 36 11480 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11480_0 (.nil)) (by decide) (by decide))

theorem cover11481 : P.CoversSplit 26 10 11481 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11481_0 : P.sumLeaves 26 11756544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11481) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11481 (by decide)
  decide +kernel

theorem h11481 : P.leaf 36 11481 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11481_0 (.nil)) (by decide) (by decide))

theorem cover11482 : P.CoversSplit 26 10 11482 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11482_0 : P.sumLeaves 26 11757568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11482) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11482 (by decide)
  decide +kernel

theorem h11482 : P.leaf 36 11482 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11482_0 (.nil)) (by decide) (by decide))

theorem cover11483 : P.CoversSplit 26 10 11483 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11483_0 : P.sumLeaves 26 11758592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11483) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11483 (by decide)
  decide +kernel

theorem h11483 : P.leaf 36 11483 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11483_0 (.nil)) (by decide) (by decide))

theorem cover11484 : P.CoversSplit 26 10 11484 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11484_0 : P.sumLeaves 26 11759616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11484) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11484 (by decide)
  decide +kernel

theorem h11484 : P.leaf 36 11484 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11484_0 (.nil)) (by decide) (by decide))

theorem cover11485 : P.CoversSplit 26 10 11485 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11485_0 : P.sumLeaves 26 11760640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11485) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11485 (by decide)
  decide +kernel

theorem h11485 : P.leaf 36 11485 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11485_0 (.nil)) (by decide) (by decide))

theorem cover11486 : P.CoversSplit 26 10 11486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11486_0 : P.sumLeaves 26 11761664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11486) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11486 (by decide)
  decide +kernel

theorem h11486 : P.leaf 36 11486 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11486_0 (.nil)) (by decide) (by decide))

theorem cover11487 : P.CoversSplit 26 10 11487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11487_0 : P.sumLeaves 26 11762688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11487) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11487 (by decide)
  decide +kernel

theorem h11487 : P.leaf 36 11487 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11487_0 (.nil)) (by decide) (by decide))

theorem cover11507 : P.CoversSplit 26 10 11507 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11507_0 : P.sumLeaves 26 11783168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11507) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11507 (by decide)
  decide +kernel

theorem h11507 : P.leaf 36 11507 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11507_0 (.nil)) (by decide) (by decide))

theorem cover11510 : P.CoversSplit 26 10 11510 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11510_0 : P.sumLeaves 26 11786240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11510) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11510 (by decide)
  decide +kernel

theorem h11510 : P.leaf 36 11510 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11510_0 (.nil)) (by decide) (by decide))

theorem cover11511 : P.CoversSplit 26 10 11511 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11511_0 : P.sumLeaves 26 11787264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11511) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11511 (by decide)
  decide +kernel

theorem h11511 : P.leaf 36 11511 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11511_0 (.nil)) (by decide) (by decide))

theorem cover11512 : P.CoversSplit 26 10 11512 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11512_0 : P.sumLeaves 26 11788288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11512) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11512 (by decide)
  decide +kernel

theorem h11512 : P.leaf 36 11512 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11512_0 (.nil)) (by decide) (by decide))

theorem cover11513 : P.CoversSplit 26 10 11513 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11513_0 : P.sumLeaves 26 11789312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11513) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11513 (by decide)
  decide +kernel

theorem h11513 : P.leaf 36 11513 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11513_0 (.nil)) (by decide) (by decide))

theorem cover11514 : P.CoversSplit 26 10 11514 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11514_0 : P.sumLeaves 26 11790336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11514) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11514 (by decide)
  decide +kernel

theorem h11514 : P.leaf 36 11514 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11514_0 (.nil)) (by decide) (by decide))

theorem cover11515 : P.CoversSplit 26 10 11515 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11515_0 : P.sumLeaves 26 11791360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11515) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11515 (by decide)
  decide +kernel

theorem h11515 : P.leaf 36 11515 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11515_0 (.nil)) (by decide) (by decide))

theorem cover11518 : P.CoversSplit 26 10 11518 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11518_0 : P.sumLeaves 26 11794432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11518) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11518 (by decide)
  decide +kernel

theorem h11518 : P.leaf 36 11518 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11518_0 (.nil)) (by decide) (by decide))

theorem cover11519 : P.CoversSplit 26 10 11519 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11519_0 : P.sumLeaves 26 11795456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11519) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11519 (by decide)
  decide +kernel

theorem h11519 : P.leaf 36 11519 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11519_0 (.nil)) (by decide) (by decide))

theorem cover11600 : P.CoversSplit 26 10 11600 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11600_0 : P.sumLeaves 26 11878400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11600) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11600 (by decide)
  decide +kernel

theorem h11600 : P.leaf 36 11600 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11600_0 (.nil)) (by decide) (by decide))

theorem cover11601 : P.CoversSplit 26 10 11601 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11601_0 : P.sumLeaves 26 11879424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11601) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11601 (by decide)
  decide +kernel

theorem h11601 : P.leaf 36 11601 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11601_0 (.nil)) (by decide) (by decide))

theorem cover11603 : P.CoversSplit 26 10 11603 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11603_0 : P.sumLeaves 26 11881472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11603) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11603 (by decide)
  decide +kernel

theorem h11603 : P.leaf 36 11603 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11603_0 (.nil)) (by decide) (by decide))

theorem h11604 : P.leaf 36 11604 = 256 := by
  exact leaf_contract_factors (k := 36) (b := 8) (H := 11604) (ss := [(2, 1, 468), (3, 1, 418), (4, 1, 410), (5, 1, 418), (36, 1, 482), (6, 1, 433), (31, 1, 486), (13, 1, 488), (20, 1, 523), (17, 1, 529), (37, 1, 531), (29, 1, 489), (7, 1, 461), (28, 1, 629), (8, 1, 516), (9, 1, 572), (10, 1, 811), (11, 1, 818), (12, 1, 825), (21, 1, 867), (18, 1, 879), (14, 1, 860), (33, 1, 881), (15, 1, 916), (35, 1, 930), (30, 1, 972), (32, 1, 1315), (34, 1, 1658)]) (ids := [14, 17, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 8]) (W := 256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h11605 : P.leaf 36 11605 = 2048 := by
  exact leaf_contract_factors (k := 36) (b := 11) (H := 11605) (ss := [(2, 1, 475), (4, 1, 425), (5, 1, 425), (36, 1, 482), (6, 1, 433), (31, 1, 487), (13, 1, 488), (17, 1, 529), (37, 1, 531), (29, 1, 489), (7, 1, 461), (20, 1, 580), (28, 1, 629), (9, 1, 572), (10, 1, 811), (11, 1, 818), (12, 1, 825), (18, 1, 879), (33, 1, 881), (35, 1, 930), (30, 1, 972), (32, 1, 1315), (21, 1, 1609), (15, 1, 916), (34, 1, 1658)]) (ids := [1, 6, 12, 14, 17, 20, 21, 22, 23, 24, 25]) (cs := [1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6, 1, 1, 7, 8, 9, 10, 11, 12, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 11]) (W := 2048) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover11607 : P.CoversSplit 26 10 11607 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 629, 636, 881, 930, 972, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c11607_0 : P.sumLeaves 26 11885568 1024 = 28160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11607) (lo := 0) (len := 1024) (W := 28160) check rows elimOK (by decide) (by decide) cover11607 (by decide)
  decide +kernel

theorem h11607 : P.leaf 36 11607 = 28160 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28160)]) (.cons c11607_0 (.nil)) (by decide) (by decide))

theorem cover11612 : P.CoversSplit 26 10 11612 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1265, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c11612_0 : P.sumLeaves 26 11890688 1024 = 2432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11612) (lo := 0) (len := 1024) (W := 2432) check rows elimOK (by decide) (by decide) cover11612 (by decide)
  decide +kernel

theorem h11612 : P.leaf 36 11612 = 2432 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2432)]) (.cons c11612_0 (.nil)) (by decide) (by decide))

theorem cover11613 : P.CoversSplit 26 10 11613 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1265, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c11613_0 : P.sumLeaves 26 11891712 1024 = 45344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11613) (lo := 0) (len := 1024) (W := 45344) check rows elimOK (by decide) (by decide) cover11613 (by decide)
  decide +kernel

theorem h11613 : P.leaf 36 11613 = 45344 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 45344)]) (.cons c11613_0 (.nil)) (by decide) (by decide))

theorem cover11615 : P.CoversSplit 26 10 11615 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1265, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c11615_0 : P.sumLeaves 26 11893760 1024 = 930832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11615) (lo := 0) (len := 1024) (W := 930832) check rows elimOK (by decide) (by decide) cover11615 (by decide)
  decide +kernel

theorem h11615 : P.leaf 36 11615 = 930832 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 930832)]) (.cons c11615_0 (.nil)) (by decide) (by decide))

theorem cover11616 : P.CoversSplit 26 10 11616 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11616_0 : P.sumLeaves 26 11894784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11616) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11616 (by decide)
  decide +kernel

theorem h11616 : P.leaf 36 11616 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11616_0 (.nil)) (by decide) (by decide))

theorem cover11617 : P.CoversSplit 26 10 11617 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11617_0 : P.sumLeaves 26 11895808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11617) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11617 (by decide)
  decide +kernel

theorem h11617 : P.leaf 36 11617 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11617_0 (.nil)) (by decide) (by decide))

theorem cover11618 : P.CoversSplit 26 10 11618 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11618_0 : P.sumLeaves 26 11896832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11618) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11618 (by decide)
  decide +kernel

theorem h11618 : P.leaf 36 11618 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11618_0 (.nil)) (by decide) (by decide))

theorem cover11619 : P.CoversSplit 26 10 11619 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11619_0 : P.sumLeaves 26 11897856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11619) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11619 (by decide)
  decide +kernel

theorem h11619 : P.leaf 36 11619 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11619_0 (.nil)) (by decide) (by decide))

theorem cover11620 : P.CoversSplit 26 10 11620 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11620_0 : P.sumLeaves 26 11898880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11620) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11620 (by decide)
  decide +kernel

theorem h11620 : P.leaf 36 11620 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11620_0 (.nil)) (by decide) (by decide))

theorem cover11621 : P.CoversSplit 26 10 11621 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11621_0 : P.sumLeaves 26 11899904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11621) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11621 (by decide)
  decide +kernel

theorem h11621 : P.leaf 36 11621 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11621_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(11480, 720), (11481, 720), (11482, 720), (11483, 720), (11484, 720), (11485, 720), (11486, 720), (11487, 720), (11507, 360), (11510, 360), (11511, 360), (11512, 360), (11513, 360), (11514, 720), (11515, 720), (11518, 360), (11519, 360), (11600, 180), (11601, 360), (11603, 180), (11604, 360), (11605, 720), (11607, 360), (11612, 180), (11613, 360), (11615, 180), (11616, 720), (11617, 720), (11618, 720), (11619, 720), (11620, 720), (11621, 720)]

theorem segOK : checkSeg 20 perms 11480 11622 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 11480 11622 16920 196015680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 196015680)
    (SegSum.cons (w := 720) h11480 (SegSum.cons (w := 720) h11481 (SegSum.cons (w := 720) h11482 (SegSum.cons (w := 720) h11483 (SegSum.cons (w := 720) h11484 (SegSum.cons (w := 720) h11485 (SegSum.cons (w := 720) h11486 (SegSum.cons (w := 720) h11487 (SegSum.cons (w := 360) h11507 (SegSum.cons (w := 360) h11510 (SegSum.cons (w := 360) h11511 (SegSum.cons (w := 360) h11512 (SegSum.cons (w := 360) h11513 (SegSum.cons (w := 720) h11514 (SegSum.cons (w := 720) h11515 (SegSum.cons (w := 360) h11518 (SegSum.cons (w := 360) h11519 (SegSum.cons (w := 180) h11600 (SegSum.cons (w := 360) h11601 (SegSum.cons (w := 180) h11603 (SegSum.cons (w := 360) h11604 (SegSum.cons (w := 720) h11605 (SegSum.cons (w := 360) h11607 (SegSum.cons (w := 180) h11612 (SegSum.cons (w := 360) h11613 (SegSum.cons (w := 180) h11615 (SegSum.cons (w := 720) h11616 (SegSum.cons (w := 720) h11617 (SegSum.cons (w := 720) h11618 (SegSum.cons (w := 720) h11619 (SegSum.cons (w := 720) h11620 (SegSum.cons (w := 720) h11621 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S16
