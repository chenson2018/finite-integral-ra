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

namespace RACert.S6N0.C0.S47

open RACert RACert.Problem

theorem h79544 : P.leaf 36 79544 = 10752 := by
  exact leaf_contract_factors (k := 36) (b := 14) (H := 79544) (ss := [(2, 1, 467), (35, 1, 475), (21, 1, 524), (18, 1, 536), (37, 1, 874), (29, 1, 587), (8, 1, 517), (9, 1, 573), (12, 1, 880), (7, 1, 459), (11, 1, 459), (4, 1, 410), (3, 1, 409), (13, 1, 825), (15, 1, 916), (36, 1, 923), (31, 1, 930), (30, 1, 972), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [3, 4, 20, 24, 26, 30, 32, 8, 12, 14, 21, 22, 23, 25]) (cs := [1, 1, 1, 2, 3, 1, 1, 1, 9, 1, 1, 1, 10, 1, 11, 1, 1, 1, 1, 1, 4, 12, 13, 14, 5, 15, 6, 1, 1, 1, 7, 1, 8, 1, 1, 1]) (bs := [7, 7]) (W := 10752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79545 : P.leaf 36 79545 = 216480 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 79545) (ss := [(35, 1, 475), (21, 1, 524), (18, 1, 536), (12, 1, 880), (36, 1, 923), (13, 1, 825), (7, 1, 460), (33, 1, 1322), (29, 1, 587), (9, 1, 573), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (37, 1, 1322), (17, 1, 1217), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 6, 8, 9, 12, 14, 20, 22, 24, 26, 30, 32, 21, 23, 25]) (cs := [2, 3, 4, 5, 6, 1, 7, 1, 8, 9, 1, 1, 10, 1, 11, 1, 1, 1, 1, 1, 12, 18, 13, 19, 14, 20, 15, 1, 1, 1, 16, 1, 17, 1, 1, 1]) (bs := [16, 3]) (W := 216480) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79546 : P.CoversSplit 26 10 79546 0xc000c00000000000c000c0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 873, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79546_0 : P.sumLeaves 26 81455104 960 = 100128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79546) (lo := 0) (len := 960) (W := 100128) check rows elimOK (by decide) (by decide) cover79546 (by decide)
  decide +kernel

theorem contract79546_1 : P.leaf 32 1272751 = 121984 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1272751) (ss := [(21, 1, 524), (29, 1, 587), (9, 1, 573), (12, 1, 880), (13, 1, 825), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 12, 14, 15, 16, 20, 22, 26, 30, 21, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 1, 1, 11, 1, 12, 13, 14, 1, 1, 1, 15, 19, 16, 20, 21, 22, 17, 1, 1, 1, 18, 1]) (bs := [17, 4]) (W := 121984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79546_1 : P.sumLeaves 26 81456064 64 = 121984 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272751) rows (by decide) (by decide)).symm.trans contract79546_1

theorem h79546 : P.leaf 36 79546 = 222112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 100128), (64, 121984)]) (.cons c79546_0 (.cons c79546_1 (.nil))) (by decide) (by decide))

theorem cover79547 : P.CoversSplit 26 10 79547 0xc000c00000000000c000c0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79547_0 : P.sumLeaves 26 81456128 960 = 218024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79547) (lo := 0) (len := 960) (W := 218024) check rows elimOK (by decide) (by decide) cover79547 (by decide)
  decide +kernel

theorem contract79547_1 : P.leaf 32 1272767 = 250880 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1272767) (ss := [(21, 1, 524), (29, 1, 587), (9, 1, 573), (12, 1, 880), (13, 1, 825), (15, 1, 916), (31, 1, 930), (30, 1, 972), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 12, 14, 15, 16, 20, 22, 26, 30, 21, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 1, 1, 11, 1, 12, 13, 14, 1, 1, 1, 15, 19, 16, 20, 21, 22, 17, 1, 1, 1, 18, 1]) (bs := [17, 4]) (W := 250880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79547_1 : P.sumLeaves 26 81457088 64 = 250880 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1272767) rows (by decide) (by decide)).symm.trans contract79547_1

theorem h79547 : P.leaf 36 79547 = 468904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 218024), (64, 250880)]) (.cons c79547_0 (.cons c79547_1 (.nil))) (by decide) (by decide))

theorem h79548 : P.leaf 36 79548 = 427552 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79548) (ss := [(35, 1, 475), (21, 1, 524), (18, 1, 536), (37, 1, 874), (29, 1, 587), (8, 1, 517), (9, 1, 573), (12, 1, 880), (15, 1, 916), (36, 1, 923), (31, 1, 930), (17, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 8, 9, 11, 12, 14, 20, 21, 24, 26, 28, 30, 32, 22, 23, 25]) (cs := [2, 3, 4, 5, 6, 7, 1, 1, 8, 9, 1, 10, 11, 1, 12, 1, 1, 1, 1, 1, 13, 14, 20, 21, 15, 22, 16, 1, 17, 1, 18, 1, 19, 1, 1, 1]) (bs := [18, 3]) (W := 427552) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79549 : P.leaf 36 79549 = 906736 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79549) (ss := [(35, 1, 475), (21, 1, 524), (18, 1, 536), (12, 1, 880), (36, 1, 923), (33, 1, 1322), (29, 1, 587), (9, 1, 573), (15, 1, 916), (31, 1, 930), (19, 1, 1259), (37, 1, 1322), (17, 1, 1217), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 11, 12, 14, 20, 21, 22, 24, 26, 28, 30, 32, 23, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 1, 11, 12, 1, 13, 1, 1, 1, 1, 1, 14, 15, 16, 22, 17, 23, 18, 1, 19, 1, 20, 1, 21, 1, 1, 1]) (bs := [20, 2]) (W := 906736) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79550 : P.CoversSplit 26 10 79550 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 873, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79550_0 : P.sumLeaves 26 81459200 1024 = 694000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79550) (lo := 0) (len := 1024) (W := 694000) check rows elimOK (by decide) (by decide) cover79550 (by decide)
  decide +kernel

theorem h79550 : P.leaf 36 79550 = 694000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 694000)]) (.cons c79550_0 (.nil)) (by decide) (by decide))

theorem cover79551 : P.CoversSplit 26 10 79551 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 873, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79551_0 : P.sumLeaves 26 81460224 1024 = 1278776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79551) (lo := 0) (len := 1024) (W := 1278776) check rows elimOK (by decide) (by decide) cover79551 (by decide)
  decide +kernel

theorem h79551 : P.leaf 36 79551 = 1278776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1278776)]) (.cons c79551_0 (.nil)) (by decide) (by decide))

theorem cover79561 : P.CoversSplit 26 10 79561 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 481, 587, 923, 930, 972, 1273, 1315, 1665]) (ps := [(9, [480], [587]), (15, [474], [930])]) (by decide +kernel)

theorem c79561_0 : P.sumLeaves 26 81470464 1024 = 13056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79561) (lo := 0) (len := 1024) (W := 13056) check rows elimOK (by decide) (by decide) cover79561 (by decide)
  decide +kernel

theorem h79561 : P.leaf 36 79561 = 13056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13056)]) (.cons c79561_0 (.nil)) (by decide) (by decide))

theorem cover79563 : P.CoversSplit 26 10 79563 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 524, 530, 587, 930, 972, 1266, 1273, 1315, 1665]) (ps := [(9, [529], [587]), (19, [523], [1273])]) (by decide +kernel)

theorem c79563_0 : P.sumLeaves 26 81472512 1024 = 146112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79563) (lo := 0) (len := 1024) (W := 146112) check rows elimOK (by decide) (by decide) cover79563 (by decide)
  decide +kernel

theorem h79563 : P.leaf 36 79563 = 146112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 146112)]) (.cons c79563_0 (.nil)) (by decide) (by decide))

theorem h79564 : P.leaf 36 79564 = 83328 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 79564) (ss := [(9, 1, 466), (32, 1, 467), (8, 1, 472), (35, 1, 475), (3, 1, 479), (4, 1, 487), (16, 1, 515), (17, 1, 516), (29, 1, 587), (37, 1, 874), (15, 1, 916), (21, 1, 573), (36, 1, 923), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 20, 21, 24, 26, 28, 32, 12, 22, 23, 25]) (cs := [2, 1, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 16, 1, 1, 1, 1, 1, 1, 1, 10, 11, 17, 18, 12, 19, 13, 1, 14, 1, 1, 1, 15, 1, 1, 1]) (bs := [14, 4]) (W := 83328) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79565 : P.CoversSplit 26 10 79565 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 530, 587, 923, 930, 972, 1273, 1315, 1665]) (by decide +kernel)

theorem c79565_0 : P.sumLeaves 26 81474560 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79565) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover79565 (by decide)
  decide +kernel

theorem contract79565_1 : P.leaf 32 1273046 = 4200 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1273046) (ss := [(4, 1, 487), (3, 1, 537), (17, 1, 874), (21, 1, 929), (18, 1, 1217), (8, 1, 516), (20, 0, 1665), (9, 0, 1609), (32, 1, 529), (15, 0, 573), (19, 0, 573), (29, 0, 573), (25, 1, 915), (31, 0, 916), (33, 0, 930), (27, 1, 489)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 24, 26, 28, 22]) (cs := [2, 1, 1, 3, 4, 5, 1, 0, 6, 7, 8, 9, 10, 0, 11, 1, 1, 0, 0, 1, 12, 13, 17, 1, 14, 1, 15, 0, 16, 0, 1, 0]) (bs := [15, 1]) (W := 4200) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79565_1 : P.sumLeaves 26 81474944 64 = 4200 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273046) rows (by decide) (by decide)).symm.trans contract79565_1

theorem contract79565_2 : P.leaf 32 1273047 = 4200 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1273047) (ss := [(4, 1, 487), (3, 1, 537), (17, 1, 874), (21, 1, 929), (18, 1, 1217), (8, 1, 516), (20, 0, 1665), (9, 0, 1609), (32, 1, 529), (15, 0, 573), (19, 0, 573), (29, 0, 573), (25, 1, 915), (31, 0, 916), (33, 0, 930), (27, 1, 489)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 24, 26, 28, 22]) (cs := [2, 1, 1, 3, 4, 5, 1, 0, 6, 7, 8, 9, 10, 0, 11, 1, 1, 0, 0, 1, 12, 13, 17, 1, 14, 1, 15, 0, 16, 0, 1, 0]) (bs := [15, 1]) (W := 4200) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79565_2 : P.sumLeaves 26 81475008 64 = 4200 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273047) rows (by decide) (by decide)).symm.trans contract79565_2

theorem c79565_3 : P.sumLeaves 26 81475072 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79565) (lo := 512) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover79565 (by decide)
  decide +kernel

theorem contract79565_4 : P.leaf 32 1273054 = 60448 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1273054) (ss := [(4, 1, 487), (29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (8, 1, 516), (19, 1, 1259), (3, 1, 417), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 14, 20, 21, 24, 26, 28, 12, 22, 23, 25]) (cs := [2, 1, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 16, 1, 10, 1, 1, 1, 1, 1, 11, 12, 17, 18, 13, 19, 14, 1, 15, 1, 1, 1]) (bs := [14, 4]) (W := 60448) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79565_4 : P.sumLeaves 26 81475456 64 = 60448 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273054) rows (by decide) (by decide)).symm.trans contract79565_4

theorem contract79565_5 : P.leaf 32 1273055 = 87488 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1273055) (ss := [(4, 1, 487), (29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (8, 1, 516), (19, 1, 1259), (3, 1, 417), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 14, 20, 21, 26, 28, 12, 22, 23, 24, 25]) (cs := [2, 1, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 15, 1, 10, 1, 1, 1, 1, 1, 11, 12, 16, 17, 18, 19, 13, 1, 14, 1, 1, 1]) (bs := [13, 5]) (W := 87488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79565_5 : P.sumLeaves 26 81475520 64 = 87488 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273055) rows (by decide) (by decide)).symm.trans contract79565_5

theorem h79565 : P.leaf 36 79565 = 156336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 4200), (64, 4200), (384, 0), (64, 60448), (64, 87488)]) (.cons c79565_0 (.cons c79565_1 (.cons c79565_2 (.cons c79565_3 (.cons c79565_4 (.cons c79565_5 (.nil))))))) (by decide) (by decide))

theorem h79566 : P.leaf 36 79566 = 111904 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 79566) (ss := [(3, 1, 479), (35, 1, 524), (37, 17, 874), (17, 1, 880), (8, 1, 515), (16, 1, 515), (4, 1, 417), (29, 1, 587), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (36, 1, 1266), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [3, 4, 5, 8, 9, 10, 11, 20, 21, 24, 26, 28, 32, 0, 12, 22, 23, 25]) (cs := [15, 1, 1, 2, 3, 4, 1, 1, 5, 6, 7, 8, 16, 1, 1, 1, 1, 1, 1, 1, 9, 10, 17, 18, 11, 19, 12, 1, 13, 1, 1, 1, 14, 1, 1, 1]) (bs := [13, 5]) (W := 111904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79567 : P.CoversSplit 26 10 79567 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 530, 587, 930, 972, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c79567_0 : P.sumLeaves 26 81476608 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79567) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover79567 (by decide)
  decide +kernel

theorem contract79567_1 : P.leaf 32 1273078 = 9456 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1273078) (ss := [(3, 1, 537), (17, 1, 874), (21, 1, 929), (18, 1, 1217), (8, 1, 516), (20, 0, 1665), (9, 0, 1609), (32, 1, 529), (15, 0, 573), (19, 0, 573), (29, 0, 573), (31, 0, 587), (25, 1, 915), (33, 0, 930), (27, 1, 538)]) (ids := [0, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 24, 26, 28, 22]) (cs := [2, 1, 3, 4, 5, 6, 1, 0, 7, 8, 9, 10, 11, 0, 12, 1, 1, 0, 0, 1, 13, 14, 18, 1, 15, 1, 16, 0, 17, 0, 1, 0]) (bs := [16, 1]) (W := 9456) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79567_1 : P.sumLeaves 26 81476992 64 = 9456 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273078) rows (by decide) (by decide)).symm.trans contract79567_1

theorem contract79567_2 : P.leaf 32 1273079 = 9456 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1273079) (ss := [(3, 1, 537), (17, 1, 874), (21, 1, 929), (18, 1, 1217), (8, 1, 516), (20, 0, 1665), (9, 0, 1609), (32, 1, 529), (15, 0, 573), (19, 0, 573), (29, 0, 573), (31, 0, 587), (25, 1, 915), (33, 0, 930), (27, 1, 538)]) (ids := [0, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 24, 26, 28, 22]) (cs := [2, 1, 3, 4, 5, 6, 1, 0, 7, 8, 9, 10, 11, 0, 12, 1, 1, 0, 0, 1, 13, 14, 18, 1, 15, 1, 16, 0, 17, 0, 1, 0]) (bs := [16, 1]) (W := 9456) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79567_2 : P.sumLeaves 26 81477056 64 = 9456 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273079) rows (by decide) (by decide)).symm.trans contract79567_2

theorem c79567_3 : P.sumLeaves 26 81477120 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79567) (lo := 512) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover79567 (by decide)
  decide +kernel

theorem contract79567_4 : P.leaf 32 1273086 = 169296 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1273086) (ss := [(29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (8, 1, 516), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 24, 26, 28, 22, 23, 25]) (cs := [2, 3, 4, 5, 6, 7, 1, 1, 8, 9, 10, 11, 12, 1, 13, 1, 1, 1, 1, 1, 14, 15, 19, 20, 16, 21, 17, 1, 18, 1, 1, 1]) (bs := [17, 3]) (W := 169296) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79567_4 : P.sumLeaves 26 81477504 64 = 169296 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273086) rows (by decide) (by decide)).symm.trans contract79567_4

theorem contract79567_5 : P.leaf 32 1273087 = 217600 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1273087) (ss := [(29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (8, 1, 516), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 26, 28, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 1, 1, 8, 9, 10, 11, 12, 1, 13, 1, 1, 1, 1, 1, 14, 15, 18, 19, 20, 21, 16, 1, 17, 1, 1, 1]) (bs := [16, 4]) (W := 217600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79567_5 : P.sumLeaves 26 81477568 64 = 217600 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273087) rows (by decide) (by decide)).symm.trans contract79567_5

theorem h79567 : P.leaf 36 79567 = 405808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 9456), (64, 9456), (384, 0), (64, 169296), (64, 217600)]) (.cons c79567_0 (.cons c79567_1 (.cons c79567_2 (.cons c79567_3 (.cons c79567_4 (.cons c79567_5 (.nil))))))) (by decide) (by decide))

theorem cover79579 : P.CoversSplit 26 10 79579 0xc000000000000000c00000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000003000010000000000300001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 930, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c79579_0 : P.sumLeaves 26 81488896 1024 = 314144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79579) (lo := 0) (len := 1024) (W := 314144) check rows elimOK (by decide) (by decide) cover79579 (by decide)
  decide +kernel

theorem h79579 : P.leaf 36 79579 = 314144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 314144)]) (.cons c79579_0 (.nil)) (by decide) (by decide))

theorem h79580 : P.leaf 36 79580 = 959352 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79580) (ss := [(32, 1, 467), (35, 1, 475), (37, 17, 874), (17, 1, 880), (29, 1, 587), (36, 1, 923), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 22, 24, 26, 28, 32, 23, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 17, 22, 18, 23, 19, 1, 20, 1, 1, 1, 21, 1, 1, 1]) (bs := [20, 2]) (W := 959352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79581 : P.CoversSplit 26 10 79581 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 530, 587, 923, 930, 972, 1273, 1315, 1665]) (by decide +kernel)

theorem c79581_0 : P.sumLeaves 26 81490944 960 = 506928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79581) (lo := 0) (len := 960) (W := 506928) check rows elimOK (by decide) (by decide) cover79581 (by decide)
  decide +kernel

theorem contract79581_1 : P.leaf 32 1273311 = 542752 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1273311) (ss := [(29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 26, 28, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 19, 20, 21, 22, 17, 1, 18, 1, 1, 1]) (bs := [17, 4]) (W := 542752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79581_1 : P.sumLeaves 26 81491904 64 = 542752 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273311) rows (by decide) (by decide)).symm.trans contract79581_1

theorem h79581 : P.leaf 36 79581 = 1049680 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 506928), (64, 542752)]) (.cons c79581_0 (.cons c79581_1 (.nil))) (by decide) (by decide))

theorem cover79582 : P.CoversSplit 26 10 79582 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 873, 880, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79582_0 : P.sumLeaves 26 81491968 960 = 558808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79582) (lo := 0) (len := 960) (W := 558808) check rows elimOK (by decide) (by decide) cover79582 (by decide)
  decide +kernel

theorem contract79582_1 : P.leaf 32 1273327 = 615264 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1273327) (ss := [(29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 26, 28, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 19, 20, 21, 22, 17, 1, 18, 1, 1, 1]) (bs := [17, 4]) (W := 615264) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79582_1 : P.sumLeaves 26 81492928 64 = 615264 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273327) rows (by decide) (by decide)).symm.trans contract79582_1

theorem h79582 : P.leaf 36 79582 = 1174072 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 558808), (64, 615264)]) (.cons c79582_0 (.cons c79582_1 (.nil))) (by decide) (by decide))

theorem cover79583 : P.CoversSplit 26 10 79583 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c79583_0 : P.sumLeaves 26 81492992 960 = 688804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79583) (lo := 0) (len := 960) (W := 688804) check rows elimOK (by decide) (by decide) cover79583 (by decide)
  decide +kernel

theorem contract79583_1 : P.leaf 32 1273343 = 615264 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1273343) (ss := [(29, 1, 587), (17, 1, 874), (21, 1, 929), (9, 1, 573), (15, 1, 916), (31, 1, 930), (18, 1, 1217), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 20, 21, 26, 28, 22, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 11, 12, 13, 1, 14, 1, 1, 1, 1, 1, 15, 16, 19, 20, 21, 22, 17, 1, 18, 1, 1, 1]) (bs := [17, 4]) (W := 615264) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79583_1 : P.sumLeaves 26 81493952 64 = 615264 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1273343) rows (by decide) (by decide)).symm.trans contract79583_1

theorem h79583 : P.leaf 36 79583 = 1304068 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 688804), (64, 615264)]) (.cons c79583_0 (.cons c79583_1 (.nil))) (by decide) (by decide))

theorem cover79596 : P.CoversSplit 26 10 79596 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 587, 873, 874, 923, 930, 1273]) (by decide +kernel)

noncomputable def f79596 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81506304 + i)

theorem c79596_0 : rowSum f79596 0 1024 = 1260168 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79596) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79596 (by decide)
  decide +kernel

theorem sum79596 : rowSum f79596 0 1024 = 1260168 :=
  c79596_0

theorem h79596 : P.leaf 36 79596 = 1260168 :=
  leaf_weighted (k := 26) (d := 10) (H := 79596) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79596) (by decide) (by decide +kernel)) sum79596

theorem cover79597 : P.CoversSplit 26 10 79597 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 587, 873, 923, 930, 972, 1273, 1665]) (by decide +kernel)

noncomputable def f79597 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81507328 + i)

theorem c79597_0 : rowSum f79597 0 1024 = 1893880 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79597) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79597 (by decide)
  decide +kernel

theorem sum79597 : rowSum f79597 0 1024 = 1893880 :=
  c79597_0

theorem h79597 : P.leaf 36 79597 = 1893880 :=
  leaf_weighted (k := 26) (d := 10) (H := 79597) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79597) (by decide) (by decide +kernel)) sum79597

theorem cover79598 : P.CoversSplit 26 10 79598 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 587, 873, 874, 930, 972, 1266, 1273]) (by decide +kernel)

theorem c79598_0 : P.sumLeaves 26 81508352 1024 = 2914188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79598) (lo := 0) (len := 1024) (W := 2914188) check rows elimOK (by decide) (by decide) cover79598 (by decide)
  decide +kernel

theorem h79598 : P.leaf 36 79598 = 2914188 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2914188)]) (.cons c79598_0 (.nil)) (by decide) (by decide))

theorem cover79599 : P.CoversSplit 26 10 79599 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 587, 873, 930, 972, 1266, 1273, 1665]) (by decide +kernel)

theorem c79599_0 : P.sumLeaves 26 81509376 1024 = 3599708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79599) (lo := 0) (len := 1024) (W := 3599708) check rows elimOK (by decide) (by decide) cover79599 (by decide)
  decide +kernel

theorem h79599 : P.leaf 36 79599 = 3599708 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3599708)]) (.cons c79599_0 (.nil)) (by decide) (by decide))

theorem cover79614 : P.CoversSplit 26 10 79614 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 873, 874, 930, 972, 1273, 1658]) (by decide +kernel)

noncomputable def f79614 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81524736 + i)

theorem c79614_0 : rowSum f79614 0 1024 = 6995992 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79614) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79614 (by decide)
  decide +kernel

theorem sum79614 : rowSum f79614 0 1024 = 6995992 :=
  c79614_0

theorem h79614 : P.leaf 36 79614 = 6995992 :=
  leaf_weighted (k := 26) (d := 10) (H := 79614) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79614) (by decide) (by decide +kernel)) sum79614

theorem cover79615 : P.CoversSplit 26 10 79615 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c8000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000330032000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 873, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f79615 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81525760 + i)

theorem c79615_0 : rowSum f79615 0 1024 = 7806480 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79615) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79615 (by decide)
  decide +kernel

theorem sum79615 : rowSum f79615 0 1024 = 7806480 :=
  c79615_0

theorem h79615 : P.leaf 36 79615 = 7806480 :=
  leaf_weighted (k := 26) (d := 10) (H := 79615) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79615) (by decide) (by decide +kernel)) sum79615

theorem cover79637 : P.CoversSplit 26 10 79637 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79637_0 : P.sumLeaves 26 81548288 1024 = 129728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79637) (lo := 0) (len := 1024) (W := 129728) check rows elimOK (by decide) (by decide) cover79637 (by decide)
  decide +kernel

theorem h79637 : P.leaf 36 79637 = 129728 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 129728)]) (.cons c79637_0 (.nil)) (by decide) (by decide))

theorem cover79639 : P.CoversSplit 26 10 79639 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79639_0 : P.sumLeaves 26 81550336 1024 = 607952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79639) (lo := 0) (len := 1024) (W := 607952) check rows elimOK (by decide) (by decide) cover79639 (by decide)
  decide +kernel

theorem h79639 : P.leaf 36 79639 = 607952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 607952)]) (.cons c79639_0 (.nil)) (by decide) (by decide))

theorem h79641 : P.leaf 36 79641 = 96000 := by
  exact leaf_contract_factors (k := 36) (b := 17) (H := 79641) (ss := [(17, 1, 467), (28, 1, 474), (9, 1, 480), (3, 1, 531), (5, 1, 418), (32, 1, 530), (30, 1, 481), (33, 1, 537), (34, 1, 579), (12, 1, 880), (7, 1, 460), (13, 1, 825), (15, 1, 916), (21, 1, 916), (36, 1, 923), (18, 1, 1217), (37, 1, 1322), (35, 1, 1273), (20, 1, 1609)]) (ids := [0, 2, 4, 6, 8, 12, 14, 17, 20, 22, 29, 9, 21, 23, 24, 25, 27]) (cs := [2, 1, 3, 1, 4, 1, 5, 1, 6, 13, 1, 1, 7, 1, 8, 1, 1, 9, 1, 1, 10, 14, 11, 15, 16, 17, 1, 18, 1, 12, 1, 1, 1, 1, 1, 1]) (bs := [11, 6]) (W := 96000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79643 : P.CoversSplit 26 10 79643 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 873, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c79643_0 : P.sumLeaves 26 81554432 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79643) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover79643 (by decide)
  decide +kernel

theorem contract79643_1 : P.leaf 32 1274303 = 651840 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1274303) (ss := [(28, 1, 481), (30, 1, 481), (32, 1, 530), (3, 1, 531), (33, 1, 537), (17, 1, 874), (5, 1, 418), (12, 1, 880), (13, 1, 825), (21, 1, 929), (18, 1, 1217), (20, 1, 1609)]) (ids := [0, 2, 4, 5, 6, 7, 8, 9, 12, 13, 14, 17, 20, 21, 22, 23, 29, 24, 25, 27]) (cs := [2, 1, 3, 1, 4, 5, 6, 7, 8, 9, 1, 1, 10, 11, 12, 1, 1, 13, 1, 1, 14, 15, 16, 17, 19, 20, 1, 21, 1, 18, 1, 1]) (bs := [17, 3]) (W := 651840) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79643_1 : P.sumLeaves 26 81555392 64 = 651840 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274303) rows (by decide) (by decide)).symm.trans contract79643_1

theorem h79643 : P.leaf 36 79643 = 651840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 651840)]) (.cons c79643_0 (.cons c79643_1 (.nil))) (by decide) (by decide))

theorem cover79644 : P.CoversSplit 26 10 79644 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 538, 923, 930, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79644_0 : P.sumLeaves 26 81555456 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79644) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover79644 (by decide)
  decide +kernel

theorem contract79644_1 : P.leaf 32 1274319 = 143808 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1274319) (ss := [(32, 1, 467), (28, 1, 530), (3, 1, 531), (17, 1, 874), (5, 1, 418), (8, 1, 517), (18, 1, 517), (12, 1, 880), (21, 1, 1272), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 17, 20, 21, 23, 27, 28, 29, 22, 24, 25]) (cs := [2, 1, 3, 1, 4, 5, 1, 6, 7, 8, 1, 9, 10, 11, 12, 1, 1, 13, 1, 1, 14, 15, 20, 16, 21, 22, 1, 17, 18, 19, 1, 1]) (bs := [18, 3]) (W := 143808) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79644_1 : P.sumLeaves 26 81556416 64 = 143808 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274319) rows (by decide) (by decide)).symm.trans contract79644_1

theorem h79644 : P.leaf 36 79644 = 143808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 143808)]) (.cons c79644_0 (.cons c79644_1 (.nil))) (by decide) (by decide))

theorem cover79645 : P.CoversSplit 26 10 79645 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79645_0 : P.sumLeaves 26 81556480 1024 = 1003976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79645) (lo := 0) (len := 1024) (W := 1003976) check rows elimOK (by decide) (by decide) cover79645 (by decide)
  decide +kernel

theorem h79645 : P.leaf 36 79645 = 1003976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1003976)]) (.cons c79645_0 (.nil)) (by decide) (by decide))

theorem cover79646 : P.CoversSplit 26 10 79646 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 873, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79646_0 : P.sumLeaves 26 81557504 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79646) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover79646 (by decide)
  decide +kernel

theorem contract79646_1 : P.leaf 32 1274346 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 531), (17, 1, 874), (5, 1, 418), (8, 1, 517), (18, 1, 517), (12, 1, 880), (21, 1, 1272), (33, 1, 1273), (30, 0, 1315), (14, 1, 873), (32, 1, 873), (28, 1, 530)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c79646_1 : P.sumLeaves 26 81558144 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274346) rows (by decide) (by decide)).symm.trans contract79646_1

theorem c79646_2 : P.sumLeaves 26 81558208 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79646) (lo := 704) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover79646 (by decide)
  decide +kernel

theorem contract79646_3 : P.leaf 32 1274351 = 542624 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1274351) (ss := [(28, 1, 530), (32, 1, 530), (3, 1, 531), (17, 1, 874), (5, 1, 418), (8, 1, 517), (18, 1, 517), (12, 1, 880), (21, 1, 1272), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 17, 20, 21, 23, 27, 28, 29, 22, 24, 25]) (cs := [2, 1, 3, 1, 4, 5, 1, 6, 7, 8, 1, 9, 10, 11, 12, 1, 1, 13, 1, 1, 14, 15, 20, 16, 21, 22, 1, 17, 18, 19, 1, 1]) (bs := [18, 3]) (W := 542624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79646_3 : P.sumLeaves 26 81558464 64 = 542624 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274351) rows (by decide) (by decide)).symm.trans contract79646_3

theorem h79646 : P.leaf 36 79646 = 542624 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 0), (256, 0), (64, 542624)]) (.cons c79646_0 (.cons c79646_1 (.cons c79646_2 (.cons c79646_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79544, 720), (79545, 720), (79546, 720), (79547, 720), (79548, 720), (79549, 720), (79550, 720), (79551, 720), (79561, 360), (79563, 720), (79564, 360), (79565, 720), (79566, 720), (79567, 720), (79579, 360), (79580, 720), (79581, 720), (79582, 720), (79583, 720), (79596, 180), (79597, 360), (79598, 720), (79599, 720), (79614, 360), (79615, 360), (79637, 720), (79639, 720), (79641, 720), (79643, 720), (79644, 360), (79645, 720), (79646, 360)]

theorem segOK : checkSeg 20 perms 79544 79647 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79544 79647 19620 19978368480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19978368480)
    (SegSum.cons (w := 720) h79544 (SegSum.cons (w := 720) h79545 (SegSum.cons (w := 720) h79546 (SegSum.cons (w := 720) h79547 (SegSum.cons (w := 720) h79548 (SegSum.cons (w := 720) h79549 (SegSum.cons (w := 720) h79550 (SegSum.cons (w := 720) h79551 (SegSum.cons (w := 360) h79561 (SegSum.cons (w := 720) h79563 (SegSum.cons (w := 360) h79564 (SegSum.cons (w := 720) h79565 (SegSum.cons (w := 720) h79566 (SegSum.cons (w := 720) h79567 (SegSum.cons (w := 360) h79579 (SegSum.cons (w := 720) h79580 (SegSum.cons (w := 720) h79581 (SegSum.cons (w := 720) h79582 (SegSum.cons (w := 720) h79583 (SegSum.cons (w := 180) h79596 (SegSum.cons (w := 360) h79597 (SegSum.cons (w := 720) h79598 (SegSum.cons (w := 720) h79599 (SegSum.cons (w := 360) h79614 (SegSum.cons (w := 360) h79615 (SegSum.cons (w := 720) h79637 (SegSum.cons (w := 720) h79639 (SegSum.cons (w := 720) h79641 (SegSum.cons (w := 720) h79643 (SegSum.cons (w := 360) h79644 (SegSum.cons (w := 720) h79645 (SegSum.cons (w := 360) h79646 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S47
