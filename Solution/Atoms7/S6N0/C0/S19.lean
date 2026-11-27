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

namespace RACert.S6N0.C0.S19

open RACert RACert.Problem

theorem cover12146 : P.CoversSplit 26 10 12146 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12146_0 : P.sumLeaves 26 12437504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12146) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12146 (by decide)
  decide +kernel

theorem h12146 : P.leaf 36 12146 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12146_0 (.nil)) (by decide) (by decide))

theorem cover12147 : P.CoversSplit 26 10 12147 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12147_0 : P.sumLeaves 26 12438528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12147) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12147 (by decide)
  decide +kernel

theorem h12147 : P.leaf 36 12147 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12147_0 (.nil)) (by decide) (by decide))

theorem cover12150 : P.CoversSplit 26 10 12150 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12150_0 : P.sumLeaves 26 12441600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12150) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12150 (by decide)
  decide +kernel

theorem h12150 : P.leaf 36 12150 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12150_0 (.nil)) (by decide) (by decide))

theorem cover12151 : P.CoversSplit 26 10 12151 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12151_0 : P.sumLeaves 26 12442624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12151) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12151 (by decide)
  decide +kernel

theorem h12151 : P.leaf 36 12151 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12151_0 (.nil)) (by decide) (by decide))

theorem cover12152 : P.CoversSplit 26 10 12152 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12152_0 : P.sumLeaves 26 12443648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12152) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12152 (by decide)
  decide +kernel

theorem h12152 : P.leaf 36 12152 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12152_0 (.nil)) (by decide) (by decide))

theorem cover12153 : P.CoversSplit 26 10 12153 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12153_0 : P.sumLeaves 26 12444672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12153) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12153 (by decide)
  decide +kernel

theorem h12153 : P.leaf 36 12153 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12153_0 (.nil)) (by decide) (by decide))

theorem cover12154 : P.CoversSplit 26 10 12154 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12154_0 : P.sumLeaves 26 12445696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12154) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12154 (by decide)
  decide +kernel

theorem h12154 : P.leaf 36 12154 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12154_0 (.nil)) (by decide) (by decide))

theorem cover12155 : P.CoversSplit 26 10 12155 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12155_0 : P.sumLeaves 26 12446720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12155) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12155 (by decide)
  decide +kernel

theorem h12155 : P.leaf 36 12155 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12155_0 (.nil)) (by decide) (by decide))

theorem cover12158 : P.CoversSplit 26 10 12158 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12158_0 : P.sumLeaves 26 12449792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12158) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12158 (by decide)
  decide +kernel

theorem h12158 : P.leaf 36 12158 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12158_0 (.nil)) (by decide) (by decide))

theorem cover12159 : P.CoversSplit 26 10 12159 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12159_0 : P.sumLeaves 26 12450816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12159) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12159 (by decide)
  decide +kernel

theorem h12159 : P.leaf 36 12159 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12159_0 (.nil)) (by decide) (by decide))

theorem cover12272 : P.CoversSplit 26 10 12272 0xe000e00000000000e000e0000000000000000000000000000000000000000000aa00aa0000000000aa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000e000a00000000000a000a0000000000000000000000000000000000000000000aa00aa0000000000aa00aa00 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 510, 881, 930, 972, 979, 1315, 1658]) (ps := [(7, [481], [489]), (18, [1315], [880])]) (by decide +kernel)

theorem contract12272_0 : P.leaf 32 196352 = 500 := by
  apply (leaf_contract (k := 32) (b := 15) (H := 196352) (ss := [(22, 1, 433), (2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 0, 874), (10, 0, 461), (11, 0, 458), (12, 0, 458), (5, 4, 586), (7, 0, 811), (8, 1, 465), (9, 1, 473), (28, 1, 481), (23, 1, 809), (18, 0, 879), (33, 0, 930), (4, 3, 536)]) (ids := [1, 4, 12, 13, 14, 15, 17, 18, 22, 23, 24, 25, 27, 28, 30]) (cs := [1, 2, 2, 2, 3, 0, 1, 1, 0, 0, 0, 0, 4, 5, 6, 7, 0, 8, 9, 0, 1, 1, 10, 11, 12, 13, 1, 14, 15, 1, 16, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c12272_0 : P.sumLeaves 26 12566528 64 = 500 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196352) rows (by decide) (by decide)).symm.trans contract12272_0

theorem contract12272_1 : P.leaf 32 196353 = 1332 := by
  apply (leaf_contract (k := 32) (b := 14) (H := 196353) (ss := [(22, 1, 433), (2, 1, 468), (31, 1, 486), (4, 1, 580), (3, 1, 409), (5, 1, 411), (21, 13, 867), (13, 0, 874), (10, 0, 461), (7, 0, 458), (11, 0, 458), (12, 0, 458), (8, 1, 465), (9, 1, 473), (28, 1, 481), (23, 1, 809), (18, 0, 879), (33, 0, 930)]) (ids := [4, 12, 13, 14, 15, 17, 18, 22, 23, 24, 25, 27, 28, 30]) (cs := [1, 1, 1, 1, 2, 0, 1, 1, 0, 0, 0, 0, 3, 4, 5, 6, 0, 7, 8, 0, 1, 1, 9, 10, 11, 12, 1, 13, 14, 1, 15, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c12272_1 : P.sumLeaves 26 12566592 64 = 1332 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196353) rows (by decide) (by decide)).symm.trans contract12272_1

theorem c12272_2 : P.sumLeaves 26 12566656 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12272) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover12272 (by decide)
  decide +kernel

theorem contract12272_3 : P.leaf 32 196356 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 1, 874), (6, 1, 412), (7, 1, 458), (10, 1, 458), (3, 1, 409), (4, 1, 410), (5, 1, 411), (11, 1, 459), (12, 1, 460), (29, 1, 489), (18, 1, 879), (14, 1, 860), (33, 1, 881), (15, 1, 916)]) (q := 930) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c12272_3 : P.sumLeaves 26 12566784 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196356) rows (by decide) (by decide)).symm.trans contract12272_3

theorem contract12272_4 : P.leaf 32 196357 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 1, 874), (6, 1, 412), (7, 1, 458), (10, 1, 458), (3, 1, 409), (4, 1, 410), (5, 1, 411), (11, 1, 459), (12, 1, 460), (29, 1, 489), (18, 1, 879), (14, 1, 860), (33, 1, 881), (15, 1, 916)]) (q := 930) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c12272_4 : P.sumLeaves 26 12566848 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196357) rows (by decide) (by decide)).symm.trans contract12272_4

theorem c12272_5 : P.sumLeaves 26 12566912 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12272) (lo := 384) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover12272 (by decide)
  decide +kernel

theorem contract12272_6 : P.leaf 32 196362 = 2428 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 196362) (ss := [(2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 0, 874), (10, 0, 461), (11, 0, 458), (12, 0, 458), (7, 0, 811), (8, 1, 465), (9, 1, 473), (28, 1, 481), (23, 1, 809), (18, 0, 879), (33, 1, 881)]) (ids := [1, 2, 3, 4, 12, 13, 14, 15, 17, 18, 20, 22, 23, 24, 27, 28, 30, 25]) (cs := [1, 2, 3, 4, 5, 0, 1, 1, 0, 0, 0, 0, 6, 7, 8, 9, 0, 10, 11, 0, 12, 1, 13, 14, 15, 19, 1, 16, 17, 1, 18, 1]) (bs := [17, 1]) (W := 2428) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12272_6 : P.sumLeaves 26 12567168 64 = 2428 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196362) rows (by decide) (by decide)).symm.trans contract12272_6

theorem contract12272_7 : P.leaf 32 196363 = 6660 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 196363) (ss := [(2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 0, 874), (10, 0, 461), (11, 0, 458), (12, 0, 458), (7, 0, 811), (8, 1, 465), (9, 1, 473), (28, 1, 481), (23, 1, 809), (18, 0, 879), (33, 1, 881)]) (ids := [1, 2, 3, 4, 12, 13, 14, 15, 17, 18, 20, 22, 23, 24, 27, 28, 30, 25]) (cs := [1, 2, 3, 4, 5, 0, 1, 1, 0, 0, 0, 0, 6, 7, 8, 9, 0, 10, 11, 0, 12, 1, 13, 14, 15, 19, 1, 16, 17, 1, 18, 1]) (bs := [17, 1]) (W := 6660) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12272_7 : P.sumLeaves 26 12567232 64 = 6660 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196363) rows (by decide) (by decide)).symm.trans contract12272_7

theorem c12272_8 : P.sumLeaves 26 12567296 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12272) (lo := 768) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover12272 (by decide)
  decide +kernel

theorem contract12272_9 : P.leaf 32 196366 = 16384 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 196366) (ss := [(2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 1, 874), (6, 1, 412), (7, 1, 458), (10, 1, 458), (3, 1, 409), (4, 1, 410), (5, 1, 411), (11, 1, 459), (12, 1, 460), (29, 1, 489), (18, 1, 879), (14, 1, 860), (33, 1, 881), (15, 1, 916), (30, 1, 972)]) (ids := [6, 7, 14, 15, 17, 18, 20, 21, 22, 23, 24, 25, 26, 30]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6, 7, 1, 8, 9, 10, 11, 12, 13, 14, 1, 1, 1, 15, 1]) (bs := [0, 14]) (W := 16384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12272_9 : P.sumLeaves 26 12567424 64 = 16384 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196366) rows (by decide) (by decide)).symm.trans contract12272_9

theorem contract12272_10 : P.leaf 32 196367 = 16384 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 196367) (ss := [(2, 1, 468), (31, 1, 486), (21, 13, 867), (13, 1, 874), (6, 1, 412), (7, 1, 458), (10, 1, 458), (3, 1, 409), (4, 1, 410), (5, 1, 411), (11, 1, 459), (12, 1, 460), (29, 1, 489), (18, 1, 879), (14, 1, 860), (33, 1, 881), (15, 1, 916), (30, 1, 972)]) (ids := [6, 7, 14, 15, 17, 18, 20, 21, 22, 23, 24, 25, 26, 30]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6, 7, 1, 8, 9, 10, 11, 12, 13, 14, 1, 1, 1, 15, 1]) (bs := [0, 14]) (W := 16384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12272_10 : P.sumLeaves 26 12567488 64 = 16384 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196367) rows (by decide) (by decide)).symm.trans contract12272_10

theorem h12272 : P.leaf 36 12272 = 43688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 500), (64, 1332), (128, 0), (64, 0), (64, 0), (256, 0), (64, 2428), (64, 6660), (128, 0), (64, 16384), (64, 16384)]) (.cons c12272_0 (.cons c12272_1 (.cons c12272_2 (.cons c12272_3 (.cons c12272_4 (.cons c12272_5 (.cons c12272_6 (.cons c12272_7 (.cons c12272_8 (.cons c12272_9 (.cons c12272_10 (.nil)))))))))))) (by decide) (by decide))

theorem cover12273 : P.CoversSplit 26 10 12273 0xc000c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000200000000000200020000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 559, 881, 930, 972, 979, 1315, 1658]) (ps := [(13, [867], [923])]) (by decide +kernel)

theorem c12273_0 : P.sumLeaves 26 12567552 896 = 10478 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12273) (lo := 0) (len := 896) (W := 10478) check rows elimOK (by decide) (by decide) cover12273 (by decide)
  decide +kernel

theorem contract12273_1 : P.leaf 32 196382 = 100320 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 196382) (ss := [(2, 1, 475), (31, 1, 487), (13, 1, 867), (11, 1, 818), (7, 1, 461), (29, 1, 489), (10, 1, 811), (12, 1, 825), (18, 1, 879), (33, 1, 881), (21, 1, 929), (15, 1, 916), (30, 1, 972)]) (ids := [1, 2, 3, 4, 6, 7, 12, 14, 15, 17, 18, 20, 22, 26, 30, 21, 23, 24, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 8, 1, 9, 10, 1, 11, 12, 1, 13, 17, 14, 18, 19, 20, 15, 1, 1, 1, 16, 1]) (bs := [15, 4]) (W := 100320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12273_1 : P.sumLeaves 26 12568448 64 = 100320 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196382) rows (by decide) (by decide)).symm.trans contract12273_1

theorem contract12273_2 : P.leaf 32 196383 = 171264 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 196383) (ss := [(2, 1, 475), (31, 1, 487), (13, 1, 867), (11, 1, 818), (7, 1, 461), (29, 1, 489), (10, 1, 811), (12, 1, 825), (18, 1, 879), (33, 1, 881), (21, 1, 929), (15, 1, 916), (30, 1, 972)]) (ids := [1, 2, 3, 4, 6, 7, 12, 14, 15, 17, 18, 20, 22, 26, 30, 21, 23, 24, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 8, 1, 9, 10, 1, 11, 12, 1, 13, 17, 14, 18, 19, 20, 15, 1, 1, 1, 16, 1]) (bs := [15, 4]) (W := 171264) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12273_2 : P.sumLeaves 26 12568512 64 = 171264 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196383) rows (by decide) (by decide)).symm.trans contract12273_2

theorem h12273 : P.leaf 36 12273 = 282062 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 10478), (64, 100320), (64, 171264)]) (.cons c12273_0 (.cons c12273_1 (.cons c12273_2 (.nil)))) (by decide) (by decide))

theorem cover12275 : P.CoversSplit 26 10 12275 0xc000c00000000000c000c00000000000000000000000000000000000000000000c0008000000000008000800000000000000000000000000000000000000000000000000000000000000000000000000000000003000200000000000200020000000000000000000000000000000000000000000030002000000000002000200 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 608, 881, 930, 972, 979, 1315, 1658]) (ps := [(13, [867], [972])]) (by decide +kernel)

theorem c12275_0 : P.sumLeaves 26 12569600 896 = 379792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12275) (lo := 0) (len := 896) (W := 379792) check rows elimOK (by decide) (by decide) cover12275 (by decide)
  decide +kernel

theorem contract12275_1 : P.leaf 32 196414 = 281520 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 196414) (ss := [(2, 1, 482), (31, 1, 488), (29, 1, 489), (13, 1, 867), (7, 1, 461), (10, 1, 811), (11, 1, 818), (12, 1, 825), (18, 1, 880), (33, 1, 881), (21, 1, 929), (30, 1, 972)]) (ids := [1, 2, 3, 4, 6, 7, 12, 13, 14, 15, 17, 18, 20, 22, 23, 26, 30, 21, 24, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 8, 9, 10, 11, 1, 12, 13, 1, 14, 19, 15, 16, 20, 21, 17, 1, 1, 1, 18, 1]) (bs := [17, 3]) (W := 281520) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12275_1 : P.sumLeaves 26 12570496 64 = 281520 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196414) rows (by decide) (by decide)).symm.trans contract12275_1

theorem contract12275_2 : P.leaf 32 196415 = 369552 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 196415) (ss := [(2, 1, 482), (31, 1, 488), (29, 1, 489), (13, 1, 867), (7, 1, 461), (10, 1, 811), (11, 1, 818), (12, 1, 825), (18, 1, 880), (33, 1, 881), (21, 1, 929), (30, 1, 972)]) (ids := [1, 2, 3, 4, 6, 7, 12, 13, 14, 15, 17, 18, 20, 22, 23, 26, 30, 21, 24, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 8, 9, 10, 11, 1, 12, 13, 1, 14, 19, 15, 16, 20, 21, 17, 1, 1, 1, 18, 1]) (bs := [17, 3]) (W := 369552) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c12275_2 : P.sumLeaves 26 12570560 64 = 369552 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 196415) rows (by decide) (by decide)).symm.trans contract12275_2

theorem h12275 : P.leaf 36 12275 = 1030864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 379792), (64, 281520), (64, 369552)]) (.cons c12275_0 (.cons c12275_1 (.cons c12275_2 (.nil)))) (by decide) (by decide))

theorem cover12279 : P.CoversSplit 26 10 12279 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000c00080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000003300220000000000220022000000000000000000000000000000000000000000300020000000000020002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 881, 930, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f12279 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (12573696 + i)

theorem c12279_0 : rowSum f12279 0 1024 = 4892912 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12279 (by decide)
  decide +kernel

theorem sum12279 : rowSum f12279 0 1024 = 4892912 :=
  c12279_0

theorem h12279 : P.leaf 36 12279 = 4892912 :=
  leaf_weighted (k := 26) (d := 10) (H := 12279) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 12279) (by decide) (by decide +kernel)) sum12279

theorem cover12280 : P.CoversSplit 26 10 12280 0xf0f5f0f5f0f5a080f0f5f0f0f0f5a080f0f5f0f5f0c0a080a080a080a080a0800000000000000000000000000000000000000000000000000000000000000000f0f5f0f5f0c4a080f0f5f0f0f0c4a080f0c4f0c4f000a000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 881, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f12280 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (12574720 + i)

theorem c12280_0 : rowSum f12280 0 934 = 1323321 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12280) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12280 (by decide)
  decide +kernel

theorem c12280_1 : rowSum f12280 934 90 = 753226 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12280) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12280 (by decide)
  decide +kernel

theorem sum12280 : rowSum f12280 0 1024 = 2076547 :=
  rowSum_append (F := f12280) (lo := 0) (n := 934) (m := 90) (A := 1323321) (B := 753226) c12280_0 (c12280_1)

theorem h12280 : P.leaf 36 12280 = 2076547 :=
  leaf_weighted (k := 26) (d := 10) (H := 12280) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 12280) (by decide) (by decide +kernel)) sum12280

theorem cover12281 : P.CoversSplit 26 10 12281 0xf0f5f0f5f0f5a080f0f5f0f0f0f5a080f0f5f0f5f0c0a080a080a080a080a0800000000000000000000000000000000000000000000000000000000000000000f0f5f0f5f0c4a080f0f5f0f0f0c4a080f0c4f0c4f000a000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c12281_0 : P.sumLeaves 26 12575744 815 = 5846596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12281) (lo := 0) (len := 815) (W := 5846596) check rows elimOK (by decide) (by decide) cover12281 (by decide)
  decide +kernel

theorem c12281_1 : P.sumLeaves 26 12576559 208 = 8919110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12281) (lo := 815) (len := 208) (W := 8919110) check rows elimOK (by decide) (by decide) cover12281 (by decide)
  decide +kernel

theorem c12281_2 : P.sumLeaves 26 12576767 1 = 341236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12281) (lo := 1023) (len := 1) (W := 341236) check rows elimOK (by decide) (by decide) cover12281 (by decide)
  decide +kernel

theorem h12281 : P.leaf 36 12281 = 15106942 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(815, 5846596), (208, 8919110), (1, 341236)]) (.cons c12281_0 (.cons c12281_1 (.cons c12281_2 (.nil)))) (by decide) (by decide))

theorem cover12283 : P.CoversSplit 26 10 12283 0xf0f5f0f5f0f5a080f0f5f0f0f0f5a080f0f5f0f5f0c0a080a080a080a080a0805555000055550000000000000000000055550000554000000000000000000000f0f5f0f5f0c4a080f0f5f0f0f0c4a080f0c4f0c4f000a000a080a080a000a0005555000055440000000000000000000055440000550000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f12283 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (12577792 + i)

theorem c12283_0 : rowSum f12283 0 781 = 24820424 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12283) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12283 (by decide)
  decide +kernel

theorem c12283_1 : rowSum f12283 781 243 = 43271972 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12283) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12283 (by decide)
  decide +kernel

theorem sum12283 : rowSum f12283 0 1024 = 68092396 :=
  rowSum_append (F := f12283) (lo := 0) (n := 781) (m := 243) (A := 24820424) (B := 43271972) c12283_0 (c12283_1)

theorem h12283 : P.leaf 36 12283 = 68092396 :=
  leaf_weighted (k := 26) (d := 10) (H := 12283) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 12283) (by decide) (by decide +kernel)) sum12283

theorem cover12287 : P.CoversSplit 26 10 12287 0xfffafffafffaaa88fffafafafffaaa88fffafffaffc8aa88aa88aa88aa88aa88fafaaaaafafaaa88aaaaaaaaaaaaaa88fafaaaaafac8aa88aa88aa88aa88aa88fffafffaffc8aa88fffafafaffc8aa88ffc8ffc8ffc8aa88aa88aa88aa88aa88fafaaaaafac8aa88aaaaaaaaaa88aa88fac8aa88fac8aa88aa88aa88aa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f12287 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (12581888 + i)

theorem c12287_0 : rowSum f12287 0 313 = 55961775 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_1 : rowSum f12287 313 254 = 334149506 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_2 : rowSum f12287 567 296 = 413342006 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_3 : rowSum f12287 863 161 = 472837220 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 12287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem sum12287 : rowSum f12287 0 1024 = 1276290507 :=
  rowSum_append (F := f12287) (lo := 0) (n := 313) (m := 711) (A := 55961775) (B := 1220328732) c12287_0 (rowSum_append (F := f12287) (lo := 313) (n := 254) (m := 457) (A := 334149506) (B := 886179226) c12287_1 (rowSum_append (F := f12287) (lo := 567) (n := 296) (m := 161) (A := 413342006) (B := 472837220) c12287_2 (c12287_3)))

theorem h12287 : P.leaf 36 12287 = 1276290507 :=
  leaf_weighted (k := 26) (d := 10) (H := 12287) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 12287) (by decide) (by decide +kernel)) sum12287

theorem cover12486 : P.CoversSplit 26 10 12486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12486_0 : P.sumLeaves 26 12785664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12486) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12486 (by decide)
  decide +kernel

theorem h12486 : P.leaf 36 12486 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12486_0 (.nil)) (by decide) (by decide))

theorem cover12487 : P.CoversSplit 26 10 12487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12487_0 : P.sumLeaves 26 12786688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12487) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12487 (by decide)
  decide +kernel

theorem h12487 : P.leaf 36 12487 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12487_0 (.nil)) (by decide) (by decide))

theorem cover12495 : P.CoversSplit 26 10 12495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12495_0 : P.sumLeaves 26 12794880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12495) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12495 (by decide)
  decide +kernel

theorem h12495 : P.leaf 36 12495 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12495_0 (.nil)) (by decide) (by decide))

theorem cover12502 : P.CoversSplit 26 10 12502 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12502_0 : P.sumLeaves 26 12802048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12502) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12502 (by decide)
  decide +kernel

theorem h12502 : P.leaf 36 12502 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12502_0 (.nil)) (by decide) (by decide))

theorem cover12503 : P.CoversSplit 26 10 12503 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12503_0 : P.sumLeaves 26 12803072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12503) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12503 (by decide)
  decide +kernel

theorem h12503 : P.leaf 36 12503 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12503_0 (.nil)) (by decide) (by decide))

theorem cover12508 : P.CoversSplit 26 10 12508 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12508_0 : P.sumLeaves 26 12808192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12508) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12508 (by decide)
  decide +kernel

theorem h12508 : P.leaf 36 12508 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12508_0 (.nil)) (by decide) (by decide))

theorem cover12509 : P.CoversSplit 26 10 12509 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12509_0 : P.sumLeaves 26 12809216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12509) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12509 (by decide)
  decide +kernel

theorem h12509 : P.leaf 36 12509 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12509_0 (.nil)) (by decide) (by decide))

theorem cover12511 : P.CoversSplit 26 10 12511 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12511_0 : P.sumLeaves 26 12811264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12511) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12511 (by decide)
  decide +kernel

theorem h12511 : P.leaf 36 12511 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12511_0 (.nil)) (by decide) (by decide))

theorem cover12534 : P.CoversSplit 26 10 12534 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12534_0 : P.sumLeaves 26 12834816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12534) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12534 (by decide)
  decide +kernel

theorem h12534 : P.leaf 36 12534 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12534_0 (.nil)) (by decide) (by decide))

theorem cover12535 : P.CoversSplit 26 10 12535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12535_0 : P.sumLeaves 26 12835840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12535) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12535 (by decide)
  decide +kernel

theorem h12535 : P.leaf 36 12535 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12535_0 (.nil)) (by decide) (by decide))

theorem cover12536 : P.CoversSplit 26 10 12536 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12536_0 : P.sumLeaves 26 12836864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12536) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12536 (by decide)
  decide +kernel

theorem h12536 : P.leaf 36 12536 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12536_0 (.nil)) (by decide) (by decide))

theorem cover12537 : P.CoversSplit 26 10 12537 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12537_0 : P.sumLeaves 26 12837888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12537) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12537 (by decide)
  decide +kernel

theorem h12537 : P.leaf 36 12537 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12537_0 (.nil)) (by decide) (by decide))

theorem cover12538 : P.CoversSplit 26 10 12538 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12538_0 : P.sumLeaves 26 12838912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12538) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12538 (by decide)
  decide +kernel

theorem h12538 : P.leaf 36 12538 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12538_0 (.nil)) (by decide) (by decide))

theorem cover12539 : P.CoversSplit 26 10 12539 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12539_0 : P.sumLeaves 26 12839936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12539) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12539 (by decide)
  decide +kernel

theorem h12539 : P.leaf 36 12539 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12539_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(12146, 720), (12147, 720), (12150, 360), (12151, 360), (12152, 360), (12153, 360), (12154, 720), (12155, 720), (12158, 360), (12159, 360), (12272, 120), (12273, 360), (12275, 360), (12279, 120), (12280, 120), (12281, 360), (12283, 360), (12287, 120), (12486, 90), (12487, 180), (12495, 45), (12502, 720), (12503, 720), (12508, 360), (12509, 720), (12511, 360), (12534, 360), (12535, 360), (12536, 360), (12537, 360), (12538, 720), (12539, 720)]

theorem segOK : checkSeg 20 perms 12146 12542 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 12146 12542 13035 184420853520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 184420853520)
    (SegSum.cons (w := 720) h12146 (SegSum.cons (w := 720) h12147 (SegSum.cons (w := 360) h12150 (SegSum.cons (w := 360) h12151 (SegSum.cons (w := 360) h12152 (SegSum.cons (w := 360) h12153 (SegSum.cons (w := 720) h12154 (SegSum.cons (w := 720) h12155 (SegSum.cons (w := 360) h12158 (SegSum.cons (w := 360) h12159 (SegSum.cons (w := 120) h12272 (SegSum.cons (w := 360) h12273 (SegSum.cons (w := 360) h12275 (SegSum.cons (w := 120) h12279 (SegSum.cons (w := 120) h12280 (SegSum.cons (w := 360) h12281 (SegSum.cons (w := 360) h12283 (SegSum.cons (w := 120) h12287 (SegSum.cons (w := 90) h12486 (SegSum.cons (w := 180) h12487 (SegSum.cons (w := 45) h12495 (SegSum.cons (w := 720) h12502 (SegSum.cons (w := 720) h12503 (SegSum.cons (w := 360) h12508 (SegSum.cons (w := 720) h12509 (SegSum.cons (w := 360) h12511 (SegSum.cons (w := 360) h12534 (SegSum.cons (w := 360) h12535 (SegSum.cons (w := 360) h12536 (SegSum.cons (w := 360) h12537 (SegSum.cons (w := 720) h12538 (SegSum.cons (w := 720) h12539 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S19
