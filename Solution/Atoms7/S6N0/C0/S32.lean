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

namespace RACert.S6N0.C0.S32

open RACert RACert.Problem

theorem cover16212 : P.CoversSplit 26 10 16212 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16212_0 : P.sumLeaves 26 16601088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16212) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16212 (by decide)
  decide +kernel

theorem h16212 : P.leaf 36 16212 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16212_0 (.nil)) (by decide) (by decide))

theorem cover16213 : P.CoversSplit 26 10 16213 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16213_0 : P.sumLeaves 26 16602112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16213) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16213 (by decide)
  decide +kernel

theorem h16213 : P.leaf 36 16213 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16213_0 (.nil)) (by decide) (by decide))

theorem cover16214 : P.CoversSplit 26 10 16214 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16214_0 : P.sumLeaves 26 16603136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16214) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16214 (by decide)
  decide +kernel

theorem h16214 : P.leaf 36 16214 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16214_0 (.nil)) (by decide) (by decide))

theorem cover16215 : P.CoversSplit 26 10 16215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16215_0 : P.sumLeaves 26 16604160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16215) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16215 (by decide)
  decide +kernel

theorem h16215 : P.leaf 36 16215 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16215_0 (.nil)) (by decide) (by decide))

theorem cover16216 : P.CoversSplit 26 10 16216 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16216_0 : P.sumLeaves 26 16605184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16216) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16216 (by decide)
  decide +kernel

theorem h16216 : P.leaf 36 16216 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16216_0 (.nil)) (by decide) (by decide))

theorem cover16217 : P.CoversSplit 26 10 16217 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16217_0 : P.sumLeaves 26 16606208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16217) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16217 (by decide)
  decide +kernel

theorem h16217 : P.leaf 36 16217 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16217_0 (.nil)) (by decide) (by decide))

theorem cover16218 : P.CoversSplit 26 10 16218 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16218_0 : P.sumLeaves 26 16607232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16218) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16218 (by decide)
  decide +kernel

theorem h16218 : P.leaf 36 16218 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16218_0 (.nil)) (by decide) (by decide))

theorem cover16219 : P.CoversSplit 26 10 16219 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16219_0 : P.sumLeaves 26 16608256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16219) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16219 (by decide)
  decide +kernel

theorem h16219 : P.leaf 36 16219 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16219_0 (.nil)) (by decide) (by decide))

theorem cover16220 : P.CoversSplit 26 10 16220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16220_0 : P.sumLeaves 26 16609280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16220) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16220 (by decide)
  decide +kernel

theorem h16220 : P.leaf 36 16220 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16220_0 (.nil)) (by decide) (by decide))

theorem cover16221 : P.CoversSplit 26 10 16221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16221_0 : P.sumLeaves 26 16610304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16221) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16221 (by decide)
  decide +kernel

theorem h16221 : P.leaf 36 16221 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16221_0 (.nil)) (by decide) (by decide))

theorem cover16222 : P.CoversSplit 26 10 16222 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16222_0 : P.sumLeaves 26 16611328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16222) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16222 (by decide)
  decide +kernel

theorem h16222 : P.leaf 36 16222 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16222_0 (.nil)) (by decide) (by decide))

theorem cover16223 : P.CoversSplit 26 10 16223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16223_0 : P.sumLeaves 26 16612352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16223) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16223 (by decide)
  decide +kernel

theorem h16223 : P.leaf 36 16223 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16223_0 (.nil)) (by decide) (by decide))

theorem cover16240 : P.CoversSplit 26 10 16240 0xa000a000a000a00000000000000000000000000000000000000000000000000000005000000050000000500000005000000000000000000000000000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000000000000000000000000000000000050000000000000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c16240_0 : P.sumLeaves 26 16629760 320 = 2 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16240) (lo := 0) (len := 320) (W := 2) check rows elimOK (by decide) (by decide) cover16240 (by decide)
  decide +kernel

theorem contract16240_1 : P.leaf 32 259845 = 0 := by
  exact leaf_contract_zero (ss := [(7, 1, 474), (2, 1, 475), (28, 1, 579), (4, 1, 580), (3, 1, 409), (5, 1, 411), (6, 1, 412), (10, 1, 458), (11, 1, 459), (12, 1, 460), (13, 1, 461), (21, 1, 867), (9, 1, 572), (20, 1, 572), (31, 0, 930), (8, 1, 486), (29, 1, 489), (33, 0, 930), (27, 1, 881)]) (q := 1665) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c16240_1 : P.sumLeaves 26 16630080 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259845) rows (by decide) (by decide)).symm.trans contract16240_1

theorem c16240_2 : P.sumLeaves 26 16630144 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16240) (lo := 384) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover16240 (by decide)
  decide +kernel

theorem contract16240_3 : P.leaf 32 259850 = 16 := by
  exact leaf_contract_factors (k := 32) (b := 5) (H := 259850) (ss := [(7, 1, 474), (2, 1, 475), (32, 0, 579), (20, 1, 580), (13, 0, 923), (6, 0, 461), (3, 0, 412), (4, 0, 409), (5, 0, 409), (10, 0, 409), (11, 0, 410), (12, 0, 411), (22, 1, 426), (16, 1, 523), (17, 1, 529), (26, 1, 530), (23, 1, 817), (14, 1, 859), (18, 1, 879), (8, 1, 516), (21, 0, 929), (19, 0, 916), (28, 9, 572), (31, 1, 930), (9, 0, 1609), (15, 1, 473), (30, 1, 481)]) (ids := [25, 27, 31, 22, 23]) (cs := [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 5, 6, 1, 2, 0, 3, 1, 1, 0, 4]) (bs := [3, 2]) (W := 16) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16240_3 : P.sumLeaves 26 16630400 64 = 16 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259850) rows (by decide) (by decide)).symm.trans contract16240_3

theorem contract16240_4 : P.leaf 32 259851 = 48 := by
  exact leaf_contract_factors (k := 32) (b := 7) (H := 259851) (ss := [(7, 1, 474), (2, 1, 475), (13, 0, 923), (6, 0, 461), (3, 0, 412), (4, 0, 409), (5, 0, 409), (10, 0, 409), (11, 0, 410), (12, 0, 411), (22, 1, 426), (16, 1, 523), (17, 1, 529), (23, 1, 817), (18, 1, 879), (21, 0, 929), (19, 0, 916), (8, 1, 515), (14, 1, 858), (31, 1, 930), (32, 0, 972), (28, 9, 579), (9, 0, 1609), (15, 1, 473), (30, 1, 481)]) (ids := [18, 23, 25, 27, 31, 22, 24]) (cs := [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 2, 0, 1, 1, 7, 3, 8, 4, 0, 5, 1, 1, 0, 6]) (bs := [2, 3, 2]) (W := 48) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16240_4 : P.sumLeaves 26 16630464 64 = 48 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259851) rows (by decide) (by decide)).symm.trans contract16240_4

theorem c16240_5 : P.sumLeaves 26 16630528 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16240) (lo := 768) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover16240 (by decide)
  decide +kernel

theorem contract16240_6 : P.leaf 32 259855 = 17664 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 259855) (ss := [(7, 1, 474), (2, 1, 475), (28, 1, 579), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (10, 1, 458), (11, 1, 459), (12, 1, 460), (21, 1, 929), (9, 1, 572), (20, 1, 572), (31, 1, 930), (15, 1, 916), (30, 1, 972)]) (ids := [6, 12, 14, 15, 16, 22, 27, 17, 20, 21, 23, 24, 25, 30, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 6, 9, 1, 1, 10, 11, 7, 12, 13, 14, 1, 8, 1, 1, 15, 16]) (bs := [7, 8]) (W := 17664) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16240_6 : P.sumLeaves 26 16630720 64 = 17664 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259855) rows (by decide) (by decide)).symm.trans contract16240_6

theorem h16240 : P.leaf 36 16240 = 17730 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 2), (64, 0), (256, 0), (64, 16), (64, 48), (192, 0), (64, 17664)]) (.cons c16240_0 (.cons c16240_1 (.cons c16240_2 (.cons c16240_3 (.cons c16240_4 (.cons c16240_5 (.cons c16240_6 (.nil)))))))) (by decide) (by decide))

theorem cover16241 : P.CoversSplit 26 10 16241 0xa000a000a000a00000000000000000000000000000000000000000000000000000005000000050000000500000005000000000000000000000000000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000000000000000000000000000000000050000000000000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c16241_0 : P.sumLeaves 26 16630784 320 = 232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16241) (lo := 0) (len := 320) (W := 232) check rows elimOK (by decide) (by decide) cover16241 (by decide)
  decide +kernel

theorem contract16241_1 : P.leaf 32 259861 = 7920 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 259861) (ss := [(7, 1, 474), (2, 1, 475), (28, 1, 579), (4, 1, 580), (5, 1, 586), (13, 1, 923), (21, 1, 929), (9, 1, 572), (20, 1, 572), (33, 0, 930), (31, 1, 1665), (15, 1, 916), (11, 0, 930), (18, 1, 879), (30, 1, 972), (12, 0, 979), (23, 1, 817)]) (ids := [4, 6, 8, 12, 14, 15, 17, 22, 25, 27, 30, 1, 20, 23, 24]) (cs := [1, 13, 1, 1, 2, 1, 3, 1, 4, 0, 0, 1, 5, 1, 6, 7, 1, 8, 1, 1, 14, 1, 9, 15, 16, 10, 1, 11, 1, 1, 12, 0]) (bs := [11, 4]) (W := 7920) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16241_1 : P.sumLeaves 26 16631104 64 = 7920 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259861) rows (by decide) (by decide)).symm.trans contract16241_1

theorem c16241_2 : P.sumLeaves 26 16631168 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16241) (lo := 384) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover16241 (by decide)
  decide +kernel

theorem contract16241_3 : P.leaf 32 259866 = 12578 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 259866) (ss := [(7, 1, 474), (2, 1, 475), (32, 0, 579), (20, 1, 580), (13, 0, 923), (16, 1, 867), (17, 1, 874), (21, 0, 929), (19, 0, 916), (31, 1, 930), (9, 0, 1609), (15, 1, 473), (28, 0, 572), (30, 1, 481), (26, 1, 629)]) (ids := [1, 2, 3, 4, 6, 8, 9, 10, 12, 16, 20, 21, 22, 25, 27, 31, 23]) (cs := [1, 2, 3, 4, 5, 1, 6, 0, 7, 8, 9, 0, 10, 1, 1, 1, 11, 0, 1, 0, 12, 13, 14, 18, 1, 15, 0, 16, 1, 1, 0, 17]) (bs := [16, 1]) (W := 12578) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16241_3 : P.sumLeaves 26 16631424 64 = 12578 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259866) rows (by decide) (by decide)).symm.trans contract16241_3

theorem contract16241_4 : P.leaf 32 259867 = 41598 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 259867) (ss := [(7, 1, 474), (2, 1, 475), (13, 0, 923), (16, 1, 867), (17, 1, 874), (21, 0, 929), (19, 0, 916), (31, 1, 930), (32, 0, 972), (9, 0, 1609), (15, 1, 473), (28, 0, 1658), (30, 1, 481)]) (ids := [1, 2, 3, 4, 6, 8, 9, 10, 12, 16, 18, 20, 21, 22, 23, 25, 27, 31, 24]) (cs := [1, 2, 3, 4, 5, 1, 6, 0, 7, 8, 9, 0, 10, 1, 1, 1, 11, 0, 12, 0, 13, 14, 15, 16, 20, 17, 0, 18, 1, 1, 0, 19]) (bs := [18, 1]) (W := 41598) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16241_4 : P.sumLeaves 26 16631488 64 = 41598 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259867) rows (by decide) (by decide)).symm.trans contract16241_4

theorem c16241_5 : P.sumLeaves 26 16631552 256 = 555200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16241) (lo := 768) (len := 256) (W := 555200) check rows elimOK (by decide) (by decide) cover16241 (by decide)
  decide +kernel

theorem h16241 : P.leaf 36 16241 = 617528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 232), (64, 7920), (256, 0), (64, 12578), (64, 41598), (256, 555200)]) (.cons c16241_0 (.cons c16241_1 (.cons c16241_2 (.cons c16241_3 (.cons c16241_4 (.cons c16241_5 (.nil))))))) (by decide) (by decide))

theorem cover16242 : P.CoversSplit 26 10 16242 0xa000a000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c16242_0 : P.sumLeaves 26 16631808 1024 = 1188592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16242) (lo := 0) (len := 1024) (W := 1188592) check rows elimOK (by decide) (by decide) cover16242 (by decide)
  decide +kernel

theorem h16242 : P.leaf 36 16242 = 1188592 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1188592)]) (.cons c16242_0 (.nil)) (by decide) (by decide))

theorem cover16243 : P.CoversSplit 26 10 16243 0xa000a000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c16243_0 : P.sumLeaves 26 16632832 1024 = 4949352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16243) (lo := 0) (len := 1024) (W := 4949352) check rows elimOK (by decide) (by decide) cover16243 (by decide)
  decide +kernel

theorem h16243 : P.leaf 36 16243 = 4949352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4949352)]) (.cons c16243_0 (.nil)) (by decide) (by decide))

theorem cover16246 : P.CoversSplit 26 10 16246 0xff00ff00ff00fa00000000000000000000000000000000000000000000000000550050005500500055005000550050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 880, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16246_0 : P.sumLeaves 26 16635904 1024 = 20125516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16246) (lo := 0) (len := 1024) (W := 20125516) check rows elimOK (by decide) (by decide) cover16246 (by decide)
  decide +kernel

theorem h16246 : P.leaf 36 16246 = 20125516 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20125516)]) (.cons c16246_0 (.nil)) (by decide) (by decide))

theorem cover16247 : P.CoversSplit 26 10 16247 0xff00ff00ff00fa00000000000000000000000000000000000000000000000000550050005500500055005000550050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000110010000000000011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 930, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c16247_0 : P.sumLeaves 26 16636928 1024 = 54999608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16247) (lo := 0) (len := 1024) (W := 54999608) check rows elimOK (by decide) (by decide) cover16247 (by decide)
  decide +kernel

theorem h16247 : P.leaf 36 16247 = 54999608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 54999608)]) (.cons c16247_0 (.nil)) (by decide) (by decide))

theorem cover16248 : P.CoversSplit 26 10 16248 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000505000005040000050500000504000000000000000000000000000000000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 579, 874, 930, 972, 1273, 1322, 1665]) (ps := [(21, [867], [929])]) (by decide +kernel)

theorem c16248_0 : P.sumLeaves 26 16637952 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16248) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover16248 (by decide)
  decide +kernel

theorem contract16248_1 : P.leaf 32 259973 = 56576 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 259973) (ss := [(7, 1, 474), (2, 1, 475), (28, 1, 579), (4, 1, 580), (11, 1, 459), (5, 1, 586), (12, 1, 460), (21, 1, 867), (9, 1, 572), (20, 1, 572), (15, 1, 916), (13, 1, 923), (30, 1, 972), (31, 1, 1665)]) (ids := [1, 4, 6, 8, 12, 14, 15, 16, 17, 22, 25, 27, 30, 31, 20, 21, 23, 24]) (cs := [1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 1, 1, 6, 1, 7, 8, 9, 10, 1, 1, 16, 17, 11, 18, 19, 12, 1, 13, 1, 1, 14, 15]) (bs := [14, 4]) (W := 56576) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16248_1 : P.sumLeaves 26 16638272 64 = 56576 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259973) rows (by decide) (by decide)).symm.trans contract16248_1

theorem c16248_2 : P.sumLeaves 26 16638336 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16248) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover16248 (by decide)
  decide +kernel

theorem contract16248_3 : P.leaf 32 259975 = 133376 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 259975) (ss := [(7, 1, 474), (2, 1, 482), (28, 1, 579), (4, 1, 580), (11, 1, 459), (13, 1, 923), (12, 1, 460), (21, 1, 929), (9, 1, 572), (20, 1, 572), (15, 1, 916), (30, 1, 972)]) (ids := [1, 3, 4, 6, 8, 12, 14, 15, 16, 17, 20, 22, 25, 27, 29, 30, 31, 21, 23, 24]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 6, 1, 1, 1, 7, 1, 8, 9, 10, 11, 1, 1, 12, 19, 13, 20, 21, 14, 1, 15, 1, 16, 17, 18]) (bs := [17, 3]) (W := 133376) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16248_3 : P.sumLeaves 26 16638400 64 = 133376 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259975) rows (by decide) (by decide)).symm.trans contract16248_3

theorem c16248_4 : P.sumLeaves 26 16638464 320 = 60344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16248) (lo := 512) (len := 320) (W := 60344) check rows elimOK (by decide) (by decide) cover16248 (by decide)
  decide +kernel

theorem contract16248_5 : P.leaf 32 259981 = 133376 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 259981) (ss := [(7, 1, 474), (2, 1, 475), (28, 1, 579), (5, 1, 586), (12, 1, 460), (21, 1, 867), (9, 1, 572), (20, 1, 572), (15, 1, 916), (13, 1, 923), (11, 1, 459), (30, 1, 972)]) (ids := [1, 2, 4, 6, 8, 12, 14, 15, 16, 17, 20, 22, 25, 27, 29, 30, 31, 21, 23, 24]) (cs := [1, 2, 3, 1, 4, 1, 5, 1, 6, 1, 1, 1, 7, 1, 8, 9, 10, 11, 1, 1, 12, 19, 13, 20, 21, 14, 1, 15, 1, 16, 17, 18]) (bs := [17, 3]) (W := 133376) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16248_5 : P.sumLeaves 26 16638784 64 = 133376 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259981) rows (by decide) (by decide)).symm.trans contract16248_5

theorem c16248_6 : P.sumLeaves 26 16638848 128 = 408248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16248) (lo := 896) (len := 128) (W := 408248) check rows elimOK (by decide) (by decide) cover16248 (by decide)
  decide +kernel

theorem h16248 : P.leaf 36 16248 = 791920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 56576), (64, 0), (64, 133376), (320, 60344), (64, 133376), (128, 408248)]) (.cons c16248_0 (.cons c16248_1 (.cons c16248_2 (.cons c16248_3 (.cons c16248_4 (.cons c16248_5 (.cons c16248_6 (.nil)))))))) (by decide) (by decide))

theorem cover16249 : P.CoversSplit 26 10 16249 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000505000005040000050500000504000005050000050400000500000005000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000505000005040000050500000504000005000000050000000500000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 930, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem contract16249_0 : P.leaf 32 259984 = 3060 := by
  apply (leaf_contract (k := 32) (b := 16) (H := 259984) (ss := [(22, 1, 433), (7, 1, 474), (2, 1, 475), (3, 1, 531), (32, 0, 579), (4, 1, 580), (28, 0, 579), (30, 1, 481), (5, 1, 586), (13, 0, 923), (21, 0, 929), (9, 0, 916), (19, 0, 572), (15, 1, 473), (8, 1, 1210), (31, 1, 1665)]) (ids := [4, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22, 23, 24, 25, 27, 31]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 0, 6, 1, 7, 8, 9, 0, 10, 0, 1, 11, 12, 13, 14, 15, 0, 16, 1, 1, 0, 17]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c16249_0 : P.sumLeaves 26 16638976 64 = 3060 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259984) rows (by decide) (by decide)).symm.trans contract16249_0

theorem contract16249_1 : P.leaf 32 259985 = 6400 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 259985) (ss := [(22, 1, 433), (7, 1, 474), (2, 1, 475), (3, 1, 531), (4, 1, 580), (5, 1, 586), (13, 0, 923), (21, 0, 929), (9, 0, 916), (19, 0, 572), (15, 1, 473), (28, 0, 972), (32, 0, 579), (30, 1, 481), (8, 1, 1210), (31, 1, 1665)]) (ids := [4, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22, 23, 25, 27, 31, 24]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 0, 6, 1, 7, 8, 9, 0, 10, 0, 1, 11, 12, 13, 17, 14, 0, 15, 1, 1, 0, 16]) (bs := [15, 1]) (W := 6400) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16249_1 : P.sumLeaves 26 16639040 64 = 6400 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259985) rows (by decide) (by decide)).symm.trans contract16249_1

theorem contract16249_2 : P.leaf 32 259986 = 5496 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 259986) (ss := [(22, 1, 433), (7, 1, 474), (2, 1, 482), (3, 1, 531), (32, 0, 579), (4, 1, 580), (28, 0, 579), (30, 1, 481), (5, 1, 629), (13, 0, 923), (21, 0, 929), (9, 0, 916), (19, 0, 572), (15, 1, 473), (8, 1, 1217)]) (ids := [4, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22, 23, 24, 25, 27, 29, 31]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 0, 6, 1, 7, 8, 9, 0, 10, 0, 1, 11, 12, 13, 14, 15, 0, 16, 1, 17, 0, 18]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c16249_2 : P.sumLeaves 26 16639104 64 = 5496 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259986) rows (by decide) (by decide)).symm.trans contract16249_2

theorem contract16249_3 : P.leaf 32 259987 = 10944 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 259987) (ss := [(22, 1, 433), (7, 1, 474), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (13, 0, 923), (21, 0, 929), (9, 0, 916), (19, 0, 572), (15, 1, 473), (28, 0, 972), (32, 0, 579), (30, 1, 481), (8, 1, 1217)]) (ids := [4, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22, 23, 25, 27, 29, 31, 24]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 0, 6, 1, 7, 8, 9, 0, 10, 0, 1, 11, 12, 13, 18, 14, 0, 15, 1, 16, 0, 17]) (bs := [16, 1]) (W := 10944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16249_3 : P.sumLeaves 26 16639168 64 = 10944 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259987) rows (by decide) (by decide)).symm.trans contract16249_3

theorem c16249_4 : P.sumLeaves 26 16639232 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16249) (lo := 256) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover16249 (by decide)
  decide +kernel

theorem contract16249_5 : P.leaf 32 259989 = 180480 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 259989) (ss := [(7, 1, 474), (2, 1, 475), (28, 1, 579), (4, 1, 580), (5, 1, 586), (13, 1, 923), (21, 1, 929), (9, 1, 572), (20, 1, 572), (15, 1, 916), (30, 1, 972), (31, 1, 1665)]) (ids := [4, 6, 8, 9, 10, 12, 14, 15, 16, 17, 21, 22, 25, 27, 30, 31, 1, 20, 23, 24]) (cs := [1, 18, 1, 1, 2, 1, 3, 1, 4, 5, 6, 1, 7, 1, 8, 9, 10, 11, 1, 1, 19, 12, 13, 20, 21, 14, 1, 15, 1, 1, 16, 17]) (bs := [16, 4]) (W := 180480) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16249_5 : P.sumLeaves 26 16639296 64 = 180480 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259989) rows (by decide) (by decide)).symm.trans contract16249_5

theorem c16249_6 : P.sumLeaves 26 16639360 128 = 561728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16249) (lo := 384) (len := 128) (W := 561728) check rows elimOK (by decide) (by decide) cover16249 (by decide)
  decide +kernel

theorem contract16249_7 : P.leaf 32 259992 = 3608 := by
  apply (leaf_contract (k := 32) (b := 16) (H := 259992) (ss := [(7, 1, 474), (2, 1, 475), (32, 0, 579), (5, 1, 586), (13, 0, 923), (21, 0, 929), (22, 1, 426), (3, 1, 524), (9, 0, 916), (19, 0, 572), (15, 1, 473), (4, 1, 573), (28, 0, 579), (30, 1, 481), (8, 1, 1210), (31, 1, 1665)]) (ids := [4, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22, 23, 24, 25, 27, 31]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 0, 6, 1, 7, 8, 9, 0, 10, 0, 1, 11, 12, 13, 14, 15, 0, 16, 1, 1, 0, 17]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c16249_7 : P.sumLeaves 26 16639488 64 = 3608 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259992) rows (by decide) (by decide)).symm.trans contract16249_7

theorem contract16249_8 : P.leaf 32 259993 = 12832 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 259993) (ss := [(7, 1, 474), (2, 1, 475), (5, 1, 586), (13, 0, 923), (21, 0, 929), (22, 1, 426), (3, 1, 524), (9, 0, 916), (19, 0, 572), (15, 1, 473), (4, 1, 573), (28, 0, 972), (32, 0, 579), (30, 1, 481), (8, 1, 1210)]) (ids := [4, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22, 23, 25, 27, 29, 31, 24]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 0, 6, 1, 7, 8, 9, 0, 10, 0, 1, 11, 12, 13, 18, 14, 0, 15, 1, 16, 0, 17]) (bs := [16, 1]) (W := 12832) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16249_8 : P.sumLeaves 26 16639552 64 = 12832 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259993) rows (by decide) (by decide)).symm.trans contract16249_8

theorem c16249_9 : P.sumLeaves 26 16639616 384 = 2795060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16249) (lo := 640) (len := 384) (W := 2795060) check rows elimOK (by decide) (by decide) cover16249 (by decide)
  decide +kernel

theorem h16249 : P.leaf 36 16249 = 3579608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 3060), (64, 6400), (64, 5496), (64, 10944), (64, 0), (64, 180480), (128, 561728), (64, 3608), (64, 12832), (384, 2795060)]) (.cons c16249_0 (.cons c16249_1 (.cons c16249_2 (.cons c16249_3 (.cons c16249_4 (.cons c16249_5 (.cons c16249_6 (.cons c16249_7 (.cons c16249_8 (.cons c16249_9 (.nil))))))))))) (by decide) (by decide))

theorem cover16250 : P.CoversSplit 26 10 16250 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 874, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16250_0 : P.sumLeaves 26 16640000 1024 = 14342524 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16250) (lo := 0) (len := 1024) (W := 14342524) check rows elimOK (by decide) (by decide) cover16250 (by decide)
  decide +kernel

theorem h16250 : P.leaf 36 16250 = 14342524 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14342524)]) (.cons c16250_0 (.nil)) (by decide) (by decide))

theorem cover16251 : P.CoversSplit 26 10 16251 0xa0a0a0a0a0a0a0800000000000000000a0a0a0a0a080a08000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a0a0a0a080a0800000000000000000a000a000a000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16251_0 : P.sumLeaves 26 16641024 1024 = 28362824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16251) (lo := 0) (len := 1024) (W := 28362824) check rows elimOK (by decide) (by decide) cover16251 (by decide)
  decide +kernel

theorem h16251 : P.leaf 36 16251 = 28362824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28362824)]) (.cons c16251_0 (.nil)) (by decide) (by decide))

theorem cover16254 : P.CoversSplit 26 10 16254 0xfffffffafffffac80000000000000000fffffffaffccfac855005000550050005555505055555040555550505555504000000000000000005500500055005000fffffffaffccfac80000000000000000ff00ff00ff00fa0055005000550050000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 874, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (ps := [(21, [867], [1658])]) (by decide +kernel)

theorem c16254_0 : P.sumLeaves 26 16644096 538 = 26544622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 0) (len := 538) (W := 26544622) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem c16254_1 : P.sumLeaves 26 16644634 336 = 23361918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 538) (len := 336) (W := 23361918) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem c16254_2 : P.sumLeaves 26 16644970 150 = 60620436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16254) (lo := 874) (len := 150) (W := 60620436) check rows elimOK (by decide) (by decide) cover16254 (by decide)
  decide +kernel

theorem h16254 : P.leaf 36 16254 = 110526976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(538, 26544622), (336, 23361918), (150, 60620436)]) (.cons c16254_0 (.cons c16254_1 (.cons c16254_2 (.nil)))) (by decide) (by decide))

theorem cover16255 : P.CoversSplit 26 10 16255 0xfffffffafffffac80000000000000000fffffffaffccfac855005000550050005555505055555040555550505555504055555050554450405500500055005000fffffffaffccfac80000000000000000ff00ff00ff00fa0055005000550050005555505055445040555550505544504055005000550050005500500055005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16255_0 : P.sumLeaves 26 16645120 64 = 83812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 0) (len := 64) (W := 83812) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem contract16255_1 : P.leaf 32 260081 = 89388 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 260081) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 586), (7, 1, 825), (13, 1, 923), (8, 1, 1217), (21, 0, 1658), (9, 0, 1609), (28, 0, 1658), (31, 1, 1665), (6, 1, 587)]) (ids := [8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 21, 23, 24, 25, 27, 28, 30, 31, 22]) (cs := [1, 1, 1, 1, 1, 1, 1, 0, 2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11, 0, 1, 12, 20, 13, 14, 15, 0, 16, 17, 1, 18, 19]) (bs := [18, 1]) (W := 89388) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16255_1 : P.sumLeaves 26 16645184 64 = 89388 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 260081) rows (by decide) (by decide)).symm.trans contract16255_1

theorem c16255_2 : P.sumLeaves 26 16645248 343 = 21869472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 128) (len := 343) (W := 21869472) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem c16255_3 : P.sumLeaves 26 16645591 245 = 46222903 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 471) (len := 245) (W := 46222903) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem c16255_4 : P.sumLeaves 26 16645836 262 = 64331851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 716) (len := 262) (W := 64331851) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem c16255_5 : P.sumLeaves 26 16646098 46 = 84157686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16255) (lo := 978) (len := 46) (W := 84157686) check rows elimOK (by decide) (by decide) cover16255 (by decide)
  decide +kernel

theorem h16255 : P.leaf 36 16255 = 216755112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 83812), (64, 89388), (343, 21869472), (245, 46222903), (262, 64331851), (46, 84157686)]) (.cons c16255_0 (.cons c16255_1 (.cons c16255_2 (.cons c16255_3 (.cons c16255_4 (.cons c16255_5 (.nil))))))) (by decide) (by decide))

theorem cover16304 : P.CoversSplit 26 10 16304 0xc000c00000000000c000c0000000000000000000000000000000000000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (ps := [(21, [1658], [929])]) (by decide +kernel)

theorem c16304_0 : P.sumLeaves 26 16695296 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16304) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover16304 (by decide)
  decide +kernel

theorem contract16304_1 : P.leaf 32 260878 = 12600 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 260878) (ss := [(7, 1, 468), (2, 1, 475), (8, 1, 486), (29, 1, 538), (31, 1, 489), (33, 1, 538), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (10, 1, 458), (11, 1, 459), (12, 1, 460), (18, 1, 517), (21, 1, 929), (15, 1, 916), (30, 1, 972)]) (ids := [7, 17, 18, 23, 12, 14, 15, 22, 24, 26, 30, 20, 21, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7, 8, 1, 3, 4, 1, 13, 14, 9, 5, 10, 15, 11, 1, 1, 1, 12, 1]) (bs := [4, 4, 3, 3]) (W := 12600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16304_1 : P.sumLeaves 26 16696192 64 = 12600 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 260878) rows (by decide) (by decide)).symm.trans contract16304_1

theorem contract16304_2 : P.leaf 32 260879 = 14400 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 260879) (ss := [(7, 1, 468), (2, 1, 475), (8, 1, 486), (29, 1, 538), (31, 1, 489), (33, 1, 538), (13, 1, 923), (6, 1, 412), (3, 1, 409), (4, 1, 410), (5, 1, 411), (10, 1, 458), (11, 1, 459), (12, 1, 460), (18, 1, 517), (21, 1, 929), (15, 1, 916), (30, 1, 972)]) (ids := [7, 17, 18, 23, 12, 14, 15, 22, 20, 21, 24, 25, 26, 30]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7, 8, 1, 3, 4, 1, 10, 11, 9, 5, 12, 13, 14, 1, 1, 1, 15, 1]) (bs := [4, 4, 6]) (W := 14400) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16304_2 : P.sumLeaves 26 16696256 64 = 14400 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 260879) rows (by decide) (by decide)).symm.trans contract16304_2

theorem h16304 : P.leaf 36 16304 = 27000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 12600), (64, 14400)]) (.cons c16304_0 (.cons c16304_1 (.cons c16304_2 (.nil)))) (by decide) (by decide))

theorem cover16305 : P.CoversSplit 26 10 16305 0xc000c00000000000c000c0000000000000000000000000000000000000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (ps := [(21, [1658], [929])]) (by decide +kernel)

theorem c16305_0 : P.sumLeaves 26 16696320 1024 = 1614808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16305) (lo := 0) (len := 1024) (W := 1614808) check rows elimOK (by decide) (by decide) cover16305 (by decide)
  decide +kernel

theorem h16305 : P.leaf 36 16305 = 1614808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1614808)]) (.cons c16305_0 (.nil)) (by decide) (by decide))

theorem cover16306 : P.CoversSplit 26 10 16306 0xc000c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (ps := [(13, [923], [972])]) (by decide +kernel)

theorem c16306_0 : P.sumLeaves 26 16697344 1024 = 1251056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16306) (lo := 0) (len := 1024) (W := 1251056) check rows elimOK (by decide) (by decide) cover16306 (by decide)
  decide +kernel

theorem h16306 : P.leaf 36 16306 = 1251056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1251056)]) (.cons c16306_0 (.nil)) (by decide) (by decide))

theorem cover16307 : P.CoversSplit 26 10 16307 0xc000c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 538, 930, 972, 979, 1315, 1658, 1665]) (ps := [(13, [923], [972])]) (by decide +kernel)

theorem c16307_0 : P.sumLeaves 26 16698368 1024 = 5725552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16307) (lo := 0) (len := 1024) (W := 5725552) check rows elimOK (by decide) (by decide) cover16307 (by decide)
  decide +kernel

theorem h16307 : P.leaf 36 16307 = 5725552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5725552)]) (.cons c16307_0 (.nil)) (by decide) (by decide))

theorem cover16310 : P.CoversSplit 26 10 16310 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c16310_0 : P.sumLeaves 26 16701440 1024 = 8893248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16310) (lo := 0) (len := 1024) (W := 8893248) check rows elimOK (by decide) (by decide) cover16310 (by decide)
  decide +kernel

theorem h16310 : P.leaf 36 16310 = 8893248 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8893248)]) (.cons c16310_0 (.nil)) (by decide) (by decide))

theorem cover16311 : P.CoversSplit 26 10 16311 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c16311_0 : P.sumLeaves 26 16702464 1024 = 39549324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16311) (lo := 0) (len := 1024) (W := 39549324) check rows elimOK (by decide) (by decide) cover16311 (by decide)
  decide +kernel

theorem h16311 : P.leaf 36 16311 = 39549324 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39549324)]) (.cons c16311_0 (.nil)) (by decide) (by decide))

theorem cover16312 : P.CoversSplit 26 10 16312 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000300031003000300030003000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16312_0 : P.sumLeaves 26 16703488 1024 = 820476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16312) (lo := 0) (len := 1024) (W := 820476) check rows elimOK (by decide) (by decide) cover16312 (by decide)
  decide +kernel

theorem h16312 : P.leaf 36 16312 = 820476 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 820476)]) (.cons c16312_0 (.nil)) (by decide) (by decide))

theorem cover16313 : P.CoversSplit 26 10 16313 0xf0f0f0f500000030f0f0f0f00000003000300031000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000300031003000300030003000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16313_0 : P.sumLeaves 26 16704512 1024 = 25417970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16313) (lo := 0) (len := 1024) (W := 25417970) check rows elimOK (by decide) (by decide) cover16313 (by decide)
  decide +kernel

theorem h16313 : P.leaf 36 16313 = 25417970 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25417970)]) (.cons c16313_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(16212, 720), (16213, 720), (16214, 720), (16215, 720), (16216, 720), (16217, 720), (16218, 720), (16219, 720), (16220, 720), (16221, 720), (16222, 720), (16223, 720), (16240, 360), (16241, 360), (16242, 720), (16243, 720), (16246, 360), (16247, 360), (16248, 360), (16249, 360), (16250, 720), (16251, 720), (16254, 360), (16255, 360), (16304, 360), (16305, 360), (16306, 720), (16307, 720), (16310, 360), (16311, 360), (16312, 360), (16313, 360)]

theorem segOK : checkSeg 20 perms 16212 16314 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16212 16314 18000 214335584640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 214335584640)
    (SegSum.cons (w := 720) h16212 (SegSum.cons (w := 720) h16213 (SegSum.cons (w := 720) h16214 (SegSum.cons (w := 720) h16215 (SegSum.cons (w := 720) h16216 (SegSum.cons (w := 720) h16217 (SegSum.cons (w := 720) h16218 (SegSum.cons (w := 720) h16219 (SegSum.cons (w := 720) h16220 (SegSum.cons (w := 720) h16221 (SegSum.cons (w := 720) h16222 (SegSum.cons (w := 720) h16223 (SegSum.cons (w := 360) h16240 (SegSum.cons (w := 360) h16241 (SegSum.cons (w := 720) h16242 (SegSum.cons (w := 720) h16243 (SegSum.cons (w := 360) h16246 (SegSum.cons (w := 360) h16247 (SegSum.cons (w := 360) h16248 (SegSum.cons (w := 360) h16249 (SegSum.cons (w := 720) h16250 (SegSum.cons (w := 720) h16251 (SegSum.cons (w := 360) h16254 (SegSum.cons (w := 360) h16255 (SegSum.cons (w := 360) h16304 (SegSum.cons (w := 360) h16305 (SegSum.cons (w := 720) h16306 (SegSum.cons (w := 720) h16307 (SegSum.cons (w := 360) h16310 (SegSum.cons (w := 360) h16311 (SegSum.cons (w := 360) h16312 (SegSum.cons (w := 360) h16313 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S32
