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

namespace RACert.S6N0.C0.S27

open RACert RACert.Problem

theorem cover14065 : P.CoversSplit 26 10 14065 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14065_0 : P.sumLeaves 26 14402560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14065) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14065 (by decide)
  decide +kernel

theorem h14065 : P.leaf 36 14065 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14065_0 (.nil)) (by decide) (by decide))

theorem cover14066 : P.CoversSplit 26 10 14066 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14066_0 : P.sumLeaves 26 14403584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14066) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14066 (by decide)
  decide +kernel

theorem h14066 : P.leaf 36 14066 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14066_0 (.nil)) (by decide) (by decide))

theorem cover14067 : P.CoversSplit 26 10 14067 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14067_0 : P.sumLeaves 26 14404608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14067) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14067 (by decide)
  decide +kernel

theorem h14067 : P.leaf 36 14067 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14067_0 (.nil)) (by decide) (by decide))

theorem cover14068 : P.CoversSplit 26 10 14068 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14068_0 : P.sumLeaves 26 14405632 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14068) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14068 (by decide)
  decide +kernel

theorem h14068 : P.leaf 36 14068 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14068_0 (.nil)) (by decide) (by decide))

theorem cover14069 : P.CoversSplit 26 10 14069 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c14069_0 : P.sumLeaves 26 14406656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14069) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14069 (by decide)
  decide +kernel

theorem h14069 : P.leaf 36 14069 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14069_0 (.nil)) (by decide) (by decide))

theorem cover14070 : P.CoversSplit 26 10 14070 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14070_0 : P.sumLeaves 26 14407680 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14070) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14070 (by decide)
  decide +kernel

theorem h14070 : P.leaf 36 14070 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14070_0 (.nil)) (by decide) (by decide))

theorem cover14071 : P.CoversSplit 26 10 14071 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14071_0 : P.sumLeaves 26 14408704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14071) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14071 (by decide)
  decide +kernel

theorem h14071 : P.leaf 36 14071 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14071_0 (.nil)) (by decide) (by decide))

theorem cover14072 : P.CoversSplit 26 10 14072 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14072_0 : P.sumLeaves 26 14409728 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14072) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14072 (by decide)
  decide +kernel

theorem h14072 : P.leaf 36 14072 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14072_0 (.nil)) (by decide) (by decide))

theorem cover14073 : P.CoversSplit 26 10 14073 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14073_0 : P.sumLeaves 26 14410752 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14073) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14073 (by decide)
  decide +kernel

theorem h14073 : P.leaf 36 14073 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14073_0 (.nil)) (by decide) (by decide))

theorem cover14074 : P.CoversSplit 26 10 14074 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14074_0 : P.sumLeaves 26 14411776 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14074) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14074 (by decide)
  decide +kernel

theorem h14074 : P.leaf 36 14074 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14074_0 (.nil)) (by decide) (by decide))

theorem cover14075 : P.CoversSplit 26 10 14075 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14075_0 : P.sumLeaves 26 14412800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14075) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14075 (by decide)
  decide +kernel

theorem h14075 : P.leaf 36 14075 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14075_0 (.nil)) (by decide) (by decide))

theorem cover14076 : P.CoversSplit 26 10 14076 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14076_0 : P.sumLeaves 26 14413824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14076) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14076 (by decide)
  decide +kernel

theorem h14076 : P.leaf 36 14076 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14076_0 (.nil)) (by decide) (by decide))

theorem cover14077 : P.CoversSplit 26 10 14077 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14077_0 : P.sumLeaves 26 14414848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14077) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14077 (by decide)
  decide +kernel

theorem h14077 : P.leaf 36 14077 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14077_0 (.nil)) (by decide) (by decide))

theorem cover14078 : P.CoversSplit 26 10 14078 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14078_0 : P.sumLeaves 26 14415872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14078) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14078 (by decide)
  decide +kernel

theorem h14078 : P.leaf 36 14078 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14078_0 (.nil)) (by decide) (by decide))

theorem cover14079 : P.CoversSplit 26 10 14079 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c14079_0 : P.sumLeaves 26 14416896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14079) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14079 (by decide)
  decide +kernel

theorem h14079 : P.leaf 36 14079 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14079_0 (.nil)) (by decide) (by decide))

theorem cover14112 : P.CoversSplit 26 10 14112 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14112_0 : P.sumLeaves 26 14450688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14112) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14112 (by decide)
  decide +kernel

theorem h14112 : P.leaf 36 14112 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14112_0 (.nil)) (by decide) (by decide))

theorem cover14113 : P.CoversSplit 26 10 14113 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14113_0 : P.sumLeaves 26 14451712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14113) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14113 (by decide)
  decide +kernel

theorem h14113 : P.leaf 36 14113 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14113_0 (.nil)) (by decide) (by decide))

theorem cover14115 : P.CoversSplit 26 10 14115 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14115_0 : P.sumLeaves 26 14453760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14115) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14115 (by decide)
  decide +kernel

theorem h14115 : P.leaf 36 14115 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14115_0 (.nil)) (by decide) (by decide))

theorem cover14117 : P.CoversSplit 26 10 14117 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14117_0 : P.sumLeaves 26 14455808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14117) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14117 (by decide)
  decide +kernel

theorem h14117 : P.leaf 36 14117 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14117_0 (.nil)) (by decide) (by decide))

theorem cover14119 : P.CoversSplit 26 10 14119 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14119_0 : P.sumLeaves 26 14457856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14119) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14119 (by decide)
  decide +kernel

theorem h14119 : P.leaf 36 14119 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14119_0 (.nil)) (by decide) (by decide))

theorem cover14127 : P.CoversSplit 26 10 14127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14127_0 : P.sumLeaves 26 14466048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14127) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14127 (by decide)
  decide +kernel

theorem h14127 : P.leaf 36 14127 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14127_0 (.nil)) (by decide) (by decide))

theorem h14128 : P.leaf 36 14128 = 256 := by
  exact leaf_contract_factors (k := 36) (b := 8) (H := 14128) (ss := [(2, 1, 467), (7, 1, 468), (9, 1, 480), (8, 1, 486), (12, 1, 825), (5, 1, 411), (4, 1, 410), (3, 1, 409), (6, 1, 412), (10, 1, 458), (11, 1, 459), (13, 1, 461), (18, 1, 517), (20, 1, 572), (37, 17, 874), (17, 1, 880), (29, 1, 538), (31, 1, 489), (33, 1, 538), (36, 1, 923), (28, 1, 579), (30, 1, 481), (34, 1, 579), (14, 1, 859), (32, 1, 873), (21, 1, 929), (15, 1, 916), (35, 1, 930)]) (ids := [14, 17, 20, 21, 22, 23, 24, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [0, 8]) (W := 256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h14129 : P.leaf 36 14129 = 16576 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 14129) (ss := [(7, 1, 474), (2, 1, 475), (9, 1, 480), (12, 1, 825), (13, 1, 825), (6, 1, 412), (17, 1, 874), (36, 1, 923), (28, 1, 579), (30, 1, 481), (34, 1, 579), (32, 1, 873), (21, 1, 929), (20, 1, 572), (18, 1, 1217)]) (ids := [1, 2, 3, 6, 8, 9, 12, 13, 14, 17, 20, 21, 22, 25, 27, 29, 31, 33, 35, 23, 24]) (cs := [1, 2, 3, 4, 1, 1, 5, 1, 6, 7, 1, 1, 8, 9, 10, 1, 1, 11, 1, 1, 12, 13, 14, 21, 22, 15, 1, 16, 1, 17, 1, 18, 1, 19, 1, 20]) (bs := [19, 2]) (W := 16576) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover14131 : P.CoversSplit 26 10 14131 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c14131_0 : P.sumLeaves 26 14470144 1024 = 191744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14131) (lo := 0) (len := 1024) (W := 191744) check rows elimOK (by decide) (by decide) cover14131 (by decide)
  decide +kernel

theorem h14131 : P.leaf 36 14131 = 191744 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 191744)]) (.cons c14131_0 (.nil)) (by decide) (by decide))

theorem h14132 : P.leaf 36 14132 = 8608 := by
  exact leaf_contract_factors (k := 36) (b := 20) (H := 14132) (ss := [(7, 1, 468), (2, 1, 475), (8, 1, 486), (12, 1, 825), (10, 1, 458), (13, 1, 461), (14, 1, 859), (17, 1, 859), (18, 1, 517), (37, 1, 874), (29, 1, 489), (31, 1, 489), (33, 1, 538), (36, 1, 923), (35, 1, 930), (34, 1, 1658)]) (ids := [1, 2, 3, 4, 7, 9, 13, 14, 17, 18, 19, 20, 23, 24, 26, 28, 30, 21, 22, 25]) (cs := [1, 2, 3, 4, 5, 1, 1, 6, 1, 7, 1, 1, 1, 8, 9, 1, 1, 10, 11, 12, 13, 19, 20, 14, 15, 21, 16, 1, 17, 1, 18, 1, 1, 1, 1, 1]) (bs := [17, 3]) (W := 8608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover14133 : P.CoversSplit 26 10 14133 0xcc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 929, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c14133_0 : P.sumLeaves 26 14472192 1024 = 221312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14133) (lo := 0) (len := 1024) (W := 221312) check rows elimOK (by decide) (by decide) cover14133 (by decide)
  decide +kernel

theorem h14133 : P.leaf 36 14133 = 221312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 221312)]) (.cons c14133_0 (.nil)) (by decide) (by decide))

theorem cover14134 : P.CoversSplit 26 10 14134 0xcc00040000000000000000000000000000000000000000000000000000000000440000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c14134_0 : P.sumLeaves 26 14473216 1024 = 219200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14134) (lo := 0) (len := 1024) (W := 219200) check rows elimOK (by decide) (by decide) cover14134 (by decide)
  decide +kernel

theorem h14134 : P.leaf 36 14134 = 219200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 219200)]) (.cons c14134_0 (.nil)) (by decide) (by decide))

theorem cover14135 : P.CoversSplit 26 10 14135 0xcc00040000000000000000000000000000000000000000000000000000000000440000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c14135_0 : P.sumLeaves 26 14474240 1024 = 1619328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14135) (lo := 0) (len := 1024) (W := 1619328) check rows elimOK (by decide) (by decide) cover14135 (by decide)
  decide +kernel

theorem h14135 : P.leaf 36 14135 = 1619328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1619328)]) (.cons c14135_0 (.nil)) (by decide) (by decide))

theorem cover14140 : P.CoversSplit 26 10 14140 0xffff050000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 929, 972, 979, 1265, 1273, 1322, 1658]) (by decide +kernel)

noncomputable def f14140 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (14479360 + i)

theorem c14140_0 : rowSum f14140 0 1024 = 337616 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14140) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14140 (by decide)
  decide +kernel

theorem sum14140 : rowSum f14140 0 1024 = 337616 :=
  c14140_0

theorem h14140 : P.leaf 36 14140 = 337616 :=
  leaf_weighted (k := 26) (d := 10) (H := 14140) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 14140) (by decide) (by decide +kernel)) sum14140

theorem cover14141 : P.CoversSplit 26 10 14141 0xffff050000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033330000003300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 579, 929, 930, 972, 979, 1265, 1273, 1322, 1658]) (ps := [(17, [908], [1322])]) (by decide +kernel)

theorem c14141_0 : P.sumLeaves 26 14480384 1024 = 1625248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14141) (lo := 0) (len := 1024) (W := 1625248) check rows elimOK (by decide) (by decide) cover14141 (by decide)
  decide +kernel

theorem h14141 : P.leaf 36 14141 = 1625248 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1625248)]) (.cons c14141_0 (.nil)) (by decide) (by decide))

theorem cover14143 : P.CoversSplit 26 10 14143 0xffff050000000000000000000000000000300000000000000000000000000000555500000000000005050000000000000010000000000000000000000000000033330100003300000000000000000000000000000000000000000000000000001111000000110000010100000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1265, 1273, 1322, 1658]) (by decide +kernel)

noncomputable def f14143 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (14482432 + i)

theorem c14143_0 : rowSum f14143 0 1024 = 8069388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 14143) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover14143 (by decide)
  decide +kernel

theorem sum14143 : rowSum f14143 0 1024 = 8069388 :=
  c14143_0

theorem h14143 : P.leaf 36 14143 = 8069388 :=
  leaf_weighted (k := 26) (d := 10) (H := 14143) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 14143) (by decide) (by decide +kernel)) sum14143

theorem cover14176 : P.CoversSplit 26 10 14176 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14176_0 : P.sumLeaves 26 14516224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14176) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14176 (by decide)
  decide +kernel

theorem h14176 : P.leaf 36 14176 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14176_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14065, 360), (14066, 720), (14067, 720), (14068, 720), (14069, 720), (14070, 720), (14071, 720), (14072, 720), (14073, 720), (14074, 720), (14075, 720), (14076, 720), (14077, 720), (14078, 720), (14079, 720), (14112, 180), (14113, 720), (14115, 360), (14117, 720), (14119, 720), (14127, 180), (14128, 360), (14129, 720), (14131, 360), (14132, 720), (14133, 720), (14134, 720), (14135, 720), (14140, 360), (14141, 720), (14143, 360), (14176, 720)]

theorem segOK : checkSeg 20 perms 14065 14177 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14065 14177 19800 5767037280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5767037280)
    (SegSum.cons (w := 360) h14065 (SegSum.cons (w := 720) h14066 (SegSum.cons (w := 720) h14067 (SegSum.cons (w := 720) h14068 (SegSum.cons (w := 720) h14069 (SegSum.cons (w := 720) h14070 (SegSum.cons (w := 720) h14071 (SegSum.cons (w := 720) h14072 (SegSum.cons (w := 720) h14073 (SegSum.cons (w := 720) h14074 (SegSum.cons (w := 720) h14075 (SegSum.cons (w := 720) h14076 (SegSum.cons (w := 720) h14077 (SegSum.cons (w := 720) h14078 (SegSum.cons (w := 720) h14079 (SegSum.cons (w := 180) h14112 (SegSum.cons (w := 720) h14113 (SegSum.cons (w := 360) h14115 (SegSum.cons (w := 720) h14117 (SegSum.cons (w := 720) h14119 (SegSum.cons (w := 180) h14127 (SegSum.cons (w := 360) h14128 (SegSum.cons (w := 720) h14129 (SegSum.cons (w := 360) h14131 (SegSum.cons (w := 720) h14132 (SegSum.cons (w := 720) h14133 (SegSum.cons (w := 720) h14134 (SegSum.cons (w := 720) h14135 (SegSum.cons (w := 360) h14140 (SegSum.cons (w := 720) h14141 (SegSum.cons (w := 360) h14143 (SegSum.cons (w := 720) h14176 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S27
