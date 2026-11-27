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

namespace RACert.S6N0.C0.S14

open RACert RACert.Problem

theorem cover7597 : P.CoversSplit 26 10 7597 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7597_0 : P.sumLeaves 26 7779328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7597) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7597 (by decide)
  decide +kernel

theorem h7597 : P.leaf 36 7597 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7597_0 (.nil)) (by decide) (by decide))

theorem cover7598 : P.CoversSplit 26 10 7598 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7598_0 : P.sumLeaves 26 7780352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7598) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7598 (by decide)
  decide +kernel

theorem h7598 : P.leaf 36 7598 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7598_0 (.nil)) (by decide) (by decide))

theorem cover7599 : P.CoversSplit 26 10 7599 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7599_0 : P.sumLeaves 26 7781376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7599) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7599 (by decide)
  decide +kernel

theorem h7599 : P.leaf 36 7599 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7599_0 (.nil)) (by decide) (by decide))

theorem cover7606 : P.CoversSplit 26 10 7606 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c7606_0 : P.sumLeaves 26 7788544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7606) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7606 (by decide)
  decide +kernel

theorem h7606 : P.leaf 36 7606 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7606_0 (.nil)) (by decide) (by decide))

theorem cover7607 : P.CoversSplit 26 10 7607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c7607_0 : P.sumLeaves 26 7789568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7607) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7607 (by decide)
  decide +kernel

theorem h7607 : P.leaf 36 7607 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7607_0 (.nil)) (by decide) (by decide))

theorem cover7610 : P.CoversSplit 26 10 7610 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7610_0 : P.sumLeaves 26 7792640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7610) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7610 (by decide)
  decide +kernel

theorem h7610 : P.leaf 36 7610 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7610_0 (.nil)) (by decide) (by decide))

theorem cover7611 : P.CoversSplit 26 10 7611 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7611_0 : P.sumLeaves 26 7793664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7611) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7611 (by decide)
  decide +kernel

theorem h7611 : P.leaf 36 7611 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7611_0 (.nil)) (by decide) (by decide))

theorem cover7612 : P.CoversSplit 26 10 7612 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7612_0 : P.sumLeaves 26 7794688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7612) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7612 (by decide)
  decide +kernel

theorem h7612 : P.leaf 36 7612 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7612_0 (.nil)) (by decide) (by decide))

theorem cover7613 : P.CoversSplit 26 10 7613 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7613_0 : P.sumLeaves 26 7795712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7613) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7613 (by decide)
  decide +kernel

theorem h7613 : P.leaf 36 7613 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7613_0 (.nil)) (by decide) (by decide))

theorem cover7614 : P.CoversSplit 26 10 7614 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7614_0 : P.sumLeaves 26 7796736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7614) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7614 (by decide)
  decide +kernel

theorem h7614 : P.leaf 36 7614 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7614_0 (.nil)) (by decide) (by decide))

theorem cover7615 : P.CoversSplit 26 10 7615 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7615_0 : P.sumLeaves 26 7797760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7615) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7615 (by decide)
  decide +kernel

theorem h7615 : P.leaf 36 7615 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7615_0 (.nil)) (by decide) (by decide))

theorem cover7660 : P.CoversSplit 26 10 7660 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7660_0 : P.sumLeaves 26 7843840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7660) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7660 (by decide)
  decide +kernel

theorem h7660 : P.leaf 36 7660 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7660_0 (.nil)) (by decide) (by decide))

theorem cover7661 : P.CoversSplit 26 10 7661 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7661_0 : P.sumLeaves 26 7844864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7661) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7661 (by decide)
  decide +kernel

theorem h7661 : P.leaf 36 7661 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7661_0 (.nil)) (by decide) (by decide))

theorem cover7662 : P.CoversSplit 26 10 7662 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7662_0 : P.sumLeaves 26 7845888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7662) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7662 (by decide)
  decide +kernel

theorem h7662 : P.leaf 36 7662 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7662_0 (.nil)) (by decide) (by decide))

theorem cover7663 : P.CoversSplit 26 10 7663 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7663_0 : P.sumLeaves 26 7846912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7663) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7663 (by decide)
  decide +kernel

theorem h7663 : P.leaf 36 7663 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7663_0 (.nil)) (by decide) (by decide))

theorem cover7678 : P.CoversSplit 26 10 7678 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7678_0 : P.sumLeaves 26 7862272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7678) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7678 (by decide)
  decide +kernel

theorem h7678 : P.leaf 36 7678 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7678_0 (.nil)) (by decide) (by decide))

theorem cover7679 : P.CoversSplit 26 10 7679 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c7679_0 : P.sumLeaves 26 7863296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7679) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem h7679 : P.leaf 36 7679 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7679_0 (.nil)) (by decide) (by decide))

theorem cover8064 : P.CoversSplit 26 10 8064 0x800000000000000f000000000000000f000000000000000f0000000000000008000000000000000f000000000000000a000000000000000f0000000000000008000000000000000f000000000000000f000000000000000c0000000000000008000000000000000f000000000000000a000000000000000c0000000000000008 :=
  coversProjected check rows (by decide) (by decide) (xs := [608, 615, 922, 930, 972, 979, 1265, 1658, 1665]) (ps := [(7, [466], [481, 489])]) (by decide +kernel)

theorem c8064_0 : P.sumLeaves 26 8257536 192 = 4 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8064) (lo := 0) (len := 192) (W := 4) check rows elimOK (by decide) (by decide) cover8064 (by decide)
  decide +kernel

theorem contract8064_1 : P.leaf 32 129027 = 0 := by
  exact leaf_contract_zero (ss := [(22, 1, 433), (7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (4, 1, 580), (2, 1, 409), (3, 1, 409), (5, 1, 411), (6, 1, 412), (10, 1, 458), (11, 1, 459), (12, 1, 460), (13, 1, 461), (14, 1, 465), (9, 1, 473), (28, 1, 481), (29, 1, 489), (16, 1, 515), (17, 1, 516), (18, 1, 517)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8064_1 : P.sumLeaves 26 8257728 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129027) rows (by decide) (by decide)).symm.trans contract8064_1

theorem c8064_2 : P.sumLeaves 26 8257792 128 = 204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8064) (lo := 256) (len := 128) (W := 204) check rows elimOK (by decide) (by decide) cover8064 (by decide)
  decide +kernel

theorem contract8064_3 : P.leaf 32 129030 = 425 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 129030) (ss := [(7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (3, 0, 922), (4, 0, 409), (5, 0, 409), (6, 0, 409), (2, 0, 417), (22, 1, 425), (20, 1, 579)]) (ids := [7, 8, 9, 10, 11, 12, 14, 15, 16, 19, 21, 22, 23, 24, 25, 26, 27]) (cs := [0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 0, 1, 11, 1, 12, 13, 14, 15, 16, 17, 18, 0, 0, 0, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c8064_3 : P.sumLeaves 26 8257920 64 = 425 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129030) rows (by decide) (by decide)).symm.trans contract8064_3

theorem contract8064_4 : P.leaf 32 129031 = 884 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 129031) (ss := [(7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (3, 0, 979), (4, 0, 409), (5, 0, 409), (6, 0, 409), (2, 0, 417), (22, 1, 425), (28, 1, 629)]) (ids := [7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 21, 22, 23, 25, 27, 24]) (cs := [0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 0, 11, 12, 1, 13, 14, 15, 18, 16, 1, 17, 0, 0, 0, 0]) (bs := [16, 1]) (W := 884) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c8064_4 : P.sumLeaves 26 8257984 64 = 884 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129031) rows (by decide) (by decide)).symm.trans contract8064_4

theorem c8064_5 : P.sumLeaves 26 8258048 64 = 68 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8064) (lo := 512) (len := 64) (W := 68) check rows elimOK (by decide) (by decide) cover8064 (by decide)
  decide +kernel

theorem contract8064_6 : P.leaf 32 129033 = 425 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 129033) (ss := [(7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (3, 0, 930), (4, 0, 409), (5, 0, 409), (6, 0, 409), (2, 0, 417), (22, 1, 425), (21, 1, 586)]) (ids := [7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 21, 22, 23, 24, 25, 26, 27]) (cs := [0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 0, 11, 1, 1, 12, 13, 14, 15, 16, 17, 18, 0, 0, 0, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c8064_6 : P.sumLeaves 26 8258112 64 = 425 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129033) rows (by decide) (by decide)).symm.trans contract8064_6

theorem c8064_7 : P.sumLeaves 26 8258176 64 = 136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8064) (lo := 640) (len := 64) (W := 136) check rows elimOK (by decide) (by decide) cover8064 (by decide)
  decide +kernel

theorem contract8064_8 : P.leaf 32 129035 = 884 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 129035) (ss := [(7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (3, 0, 972), (4, 0, 409), (5, 0, 409), (6, 0, 409), (2, 0, 417), (22, 1, 425), (29, 1, 636)]) (ids := [7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19, 21, 22, 23, 24, 26, 25]) (cs := [0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 0, 11, 12, 1, 13, 14, 15, 16, 18, 17, 1, 0, 0, 0, 0]) (bs := [16, 1]) (W := 884) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c8064_8 : P.sumLeaves 26 8258240 64 = 884 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129035) rows (by decide) (by decide)).symm.trans contract8064_8

theorem c8064_9 : P.sumLeaves 26 8258304 64 = 136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8064) (lo := 768) (len := 64) (W := 136) check rows elimOK (by decide) (by decide) cover8064 (by decide)
  decide +kernel

theorem contract8064_10 : P.leaf 32 129037 = 680 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 129037) (ss := [(7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (3, 0, 930), (4, 0, 409), (5, 0, 409), (6, 0, 409), (2, 0, 417), (22, 1, 425), (21, 1, 586)]) (ids := [7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 21, 22, 23, 25, 26, 27, 24]) (cs := [0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 0, 11, 1, 1, 12, 13, 14, 18, 15, 16, 17, 0, 0, 0, 0]) (bs := [16, 1]) (W := 680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c8064_10 : P.sumLeaves 26 8258368 64 = 680 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129037) rows (by decide) (by decide)).symm.trans contract8064_10

theorem contract8064_11 : P.leaf 32 129038 = 680 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 129038) (ss := [(7, 1, 466), (8, 1, 472), (15, 2, 474), (30, 2, 480), (31, 2, 487), (19, 3, 523), (32, 3, 529), (33, 3, 536), (3, 0, 922), (4, 0, 409), (5, 0, 409), (6, 0, 409), (2, 0, 417), (22, 1, 425), (20, 1, 579)]) (ids := [7, 8, 9, 10, 11, 12, 14, 15, 16, 19, 21, 22, 23, 24, 26, 27, 25]) (cs := [0, 0, 0, 0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 0, 8, 9, 10, 0, 1, 11, 1, 12, 13, 14, 15, 18, 16, 17, 0, 0, 0, 0]) (bs := [16, 1]) (W := 680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c8064_11 : P.sumLeaves 26 8258432 64 = 680 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 129038) rows (by decide) (by decide)).symm.trans contract8064_11

theorem c8064_12 : P.sumLeaves 26 8258496 64 = 2036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8064) (lo := 960) (len := 64) (W := 2036) check rows elimOK (by decide) (by decide) cover8064 (by decide)
  decide +kernel

theorem h8064 : P.leaf 36 8064 = 6562 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 4), (64, 0), (128, 204), (64, 425), (64, 884), (64, 68), (64, 425), (64, 136), (64, 884), (64, 136), (64, 680), (64, 680), (64, 2036)]) (.cons c8064_0 (.cons c8064_1 (.cons c8064_2 (.cons c8064_3 (.cons c8064_4 (.cons c8064_5 (.cons c8064_6 (.cons c8064_7 (.cons c8064_8 (.cons c8064_9 (.cons c8064_10 (.cons c8064_11 (.cons c8064_12 (.nil)))))))))))))) (by decide) (by decide))

theorem cover8065 : P.CoversSplit 26 10 8065 0x800000000000000f000000000000000f000000000000000f0000000000000008000000000000000f000000000000000a000000000000000f0000000000000008000000000000000f000000000000000f000000000000000c0000000000000008000000000000000f000000000000000a000000000000000c0000000000000008 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 922, 930, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f8065 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (8258560 + i)

theorem c8065_0 : rowSum f8065 0 1024 = 631525 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 8065) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover8065 (by decide)
  decide +kernel

theorem sum8065 : rowSum f8065 0 1024 = 631525 :=
  c8065_0

theorem h8065 : P.leaf 36 8065 = 631525 :=
  leaf_weighted (k := 26) (d := 10) (H := 8065) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 8065) (by decide) (by decide +kernel)) sum8065

theorem cover8066 : P.CoversSplit 26 10 8066 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8066_0 : P.sumLeaves 26 8259584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8066) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8066 (by decide)
  decide +kernel

theorem h8066 : P.leaf 36 8066 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8066_0 (.nil)) (by decide) (by decide))

theorem cover8067 : P.CoversSplit 26 10 8067 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8067_0 : P.sumLeaves 26 8260608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8067) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8067 (by decide)
  decide +kernel

theorem h8067 : P.leaf 36 8067 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8067_0 (.nil)) (by decide) (by decide))

theorem cover8070 : P.CoversSplit 26 10 8070 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8070_0 : P.sumLeaves 26 8263680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8070) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8070 (by decide)
  decide +kernel

theorem h8070 : P.leaf 36 8070 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8070_0 (.nil)) (by decide) (by decide))

theorem cover8071 : P.CoversSplit 26 10 8071 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8071_0 : P.sumLeaves 26 8264704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8071) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8071 (by decide)
  decide +kernel

theorem h8071 : P.leaf 36 8071 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8071_0 (.nil)) (by decide) (by decide))

theorem cover8078 : P.CoversSplit 26 10 8078 0xffff0000000000080f0f00000000000800ff00000000000800080000000000080f0f0a0a000000080a0a0a0a00000008000f000a00000008000800080000000800ff000000cc0008000f0000000c000800cc000000cc00080008000000080008000f000a000c0008000a000a00080008000c0008000c00080008000800080008 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f8078 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (8271872 + i)

theorem c8078_0 : rowSum f8078 0 1024 = 128506 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 8078) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover8078 (by decide)
  decide +kernel

theorem sum8078 : rowSum f8078 0 1024 = 128506 :=
  c8078_0

theorem h8078 : P.leaf 36 8078 = 128506 :=
  leaf_weighted (k := 26) (d := 10) (H := 8078) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 8078) (by decide) (by decide +kernel)) sum8078

theorem cover8079 : P.CoversSplit 26 10 8079 0xffff0000000000080f0f00000000000800ff00000000000800080000000000080f0f0a0a000000080a0a0a0a00000008000f000a00000008000800080000000800ff000000cc0008000f0000000c000800cc000000cc00080008000000080008000f000a000c0008000a000a00080008000c0008000c00080008000800080008 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f8079 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (8272896 + i)

theorem c8079_0 : rowSum f8079 0 1024 = 6808402 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 8079) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover8079 (by decide)
  decide +kernel

theorem sum8079 : rowSum f8079 0 1024 = 6808402 :=
  c8079_0

theorem h8079 : P.leaf 36 8079 = 6808402 :=
  leaf_weighted (k := 26) (d := 10) (H := 8079) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 8079) (by decide) (by decide +kernel)) sum8079

theorem cover8082 : P.CoversSplit 26 10 8082 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8082_0 : P.sumLeaves 26 8275968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8082) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8082 (by decide)
  decide +kernel

theorem h8082 : P.leaf 36 8082 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8082_0 (.nil)) (by decide) (by decide))

theorem cover8083 : P.CoversSplit 26 10 8083 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8083_0 : P.sumLeaves 26 8276992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8083) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8083 (by decide)
  decide +kernel

theorem h8083 : P.leaf 36 8083 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8083_0 (.nil)) (by decide) (by decide))

theorem cover8084 : P.CoversSplit 26 10 8084 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c8084_0 : P.sumLeaves 26 8278016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8084) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8084 (by decide)
  decide +kernel

theorem h8084 : P.leaf 36 8084 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8084_0 (.nil)) (by decide) (by decide))

theorem cover8085 : P.CoversSplit 26 10 8085 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c8085_0 : P.sumLeaves 26 8279040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8085) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8085 (by decide)
  decide +kernel

theorem h8085 : P.leaf 36 8085 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8085_0 (.nil)) (by decide) (by decide))

theorem cover8086 : P.CoversSplit 26 10 8086 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8086_0 : P.sumLeaves 26 8280064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8086) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8086 (by decide)
  decide +kernel

theorem h8086 : P.leaf 36 8086 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8086_0 (.nil)) (by decide) (by decide))

theorem cover8087 : P.CoversSplit 26 10 8087 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8087_0 : P.sumLeaves 26 8281088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8087) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8087 (by decide)
  decide +kernel

theorem h8087 : P.leaf 36 8087 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8087_0 (.nil)) (by decide) (by decide))

theorem cover8092 : P.CoversSplit 26 10 8092 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8092_0 : P.sumLeaves 26 8286208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8092) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8092 (by decide)
  decide +kernel

theorem h8092 : P.leaf 36 8092 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8092_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7597, 720), (7598, 720), (7599, 720), (7606, 360), (7607, 360), (7610, 360), (7611, 360), (7612, 720), (7613, 720), (7614, 720), (7615, 720), (7660, 180), (7661, 180), (7662, 360), (7663, 360), (7678, 180), (7679, 180), (8064, 60), (8065, 60), (8066, 360), (8067, 360), (8070, 360), (8071, 360), (8078, 120), (8079, 120), (8082, 180), (8083, 180), (8084, 360), (8085, 360), (8086, 720), (8087, 720), (8092, 360)]

theorem segOK : checkSeg 20 perms 7597 8093 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 7597 8093 12600 870714180 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 870714180)
    (SegSum.cons (w := 720) h7597 (SegSum.cons (w := 720) h7598 (SegSum.cons (w := 720) h7599 (SegSum.cons (w := 360) h7606 (SegSum.cons (w := 360) h7607 (SegSum.cons (w := 360) h7610 (SegSum.cons (w := 360) h7611 (SegSum.cons (w := 720) h7612 (SegSum.cons (w := 720) h7613 (SegSum.cons (w := 720) h7614 (SegSum.cons (w := 720) h7615 (SegSum.cons (w := 180) h7660 (SegSum.cons (w := 180) h7661 (SegSum.cons (w := 360) h7662 (SegSum.cons (w := 360) h7663 (SegSum.cons (w := 180) h7678 (SegSum.cons (w := 180) h7679 (SegSum.cons (w := 60) h8064 (SegSum.cons (w := 60) h8065 (SegSum.cons (w := 360) h8066 (SegSum.cons (w := 360) h8067 (SegSum.cons (w := 360) h8070 (SegSum.cons (w := 360) h8071 (SegSum.cons (w := 120) h8078 (SegSum.cons (w := 120) h8079 (SegSum.cons (w := 180) h8082 (SegSum.cons (w := 180) h8083 (SegSum.cons (w := 360) h8084 (SegSum.cons (w := 360) h8085 (SegSum.cons (w := 720) h8086 (SegSum.cons (w := 720) h8087 (SegSum.cons (w := 360) h8092 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S14
