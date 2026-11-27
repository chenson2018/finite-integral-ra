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

namespace RACert.S6N0.C0.S31

open RACert RACert.Problem

theorem cover15853 : P.CoversSplit 26 10 15853 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15853_0 : P.sumLeaves 26 16233472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15853) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15853 (by decide)
  decide +kernel

theorem h15853 : P.leaf 36 15853 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15853_0 (.nil)) (by decide) (by decide))

theorem cover15854 : P.CoversSplit 26 10 15854 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15854_0 : P.sumLeaves 26 16234496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15854) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15854 (by decide)
  decide +kernel

theorem h15854 : P.leaf 36 15854 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15854_0 (.nil)) (by decide) (by decide))

theorem cover15855 : P.CoversSplit 26 10 15855 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15855_0 : P.sumLeaves 26 16235520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15855) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15855 (by decide)
  decide +kernel

theorem h15855 : P.leaf 36 15855 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15855_0 (.nil)) (by decide) (by decide))

theorem cover15859 : P.CoversSplit 26 10 15859 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15859_0 : P.sumLeaves 26 16239616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15859) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15859 (by decide)
  decide +kernel

theorem h15859 : P.leaf 36 15859 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15859_0 (.nil)) (by decide) (by decide))

theorem cover15860 : P.CoversSplit 26 10 15860 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15860_0 : P.sumLeaves 26 16240640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15860) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15860 (by decide)
  decide +kernel

theorem h15860 : P.leaf 36 15860 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15860_0 (.nil)) (by decide) (by decide))

theorem cover15861 : P.CoversSplit 26 10 15861 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15861_0 : P.sumLeaves 26 16241664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15861) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15861 (by decide)
  decide +kernel

theorem h15861 : P.leaf 36 15861 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15861_0 (.nil)) (by decide) (by decide))

theorem cover15862 : P.CoversSplit 26 10 15862 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15862_0 : P.sumLeaves 26 16242688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15862) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15862 (by decide)
  decide +kernel

theorem h15862 : P.leaf 36 15862 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15862_0 (.nil)) (by decide) (by decide))

theorem cover15863 : P.CoversSplit 26 10 15863 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15863_0 : P.sumLeaves 26 16243712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15863) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15863 (by decide)
  decide +kernel

theorem h15863 : P.leaf 36 15863 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15863_0 (.nil)) (by decide) (by decide))

theorem cover15864 : P.CoversSplit 26 10 15864 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15864_0 : P.sumLeaves 26 16244736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15864) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15864 (by decide)
  decide +kernel

theorem h15864 : P.leaf 36 15864 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15864_0 (.nil)) (by decide) (by decide))

theorem cover15865 : P.CoversSplit 26 10 15865 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15865_0 : P.sumLeaves 26 16245760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15865) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15865 (by decide)
  decide +kernel

theorem h15865 : P.leaf 36 15865 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15865_0 (.nil)) (by decide) (by decide))

theorem cover15866 : P.CoversSplit 26 10 15866 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15866_0 : P.sumLeaves 26 16246784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15866) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15866 (by decide)
  decide +kernel

theorem h15866 : P.leaf 36 15866 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15866_0 (.nil)) (by decide) (by decide))

theorem cover15867 : P.CoversSplit 26 10 15867 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15867_0 : P.sumLeaves 26 16247808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15867) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15867 (by decide)
  decide +kernel

theorem h15867 : P.leaf 36 15867 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15867_0 (.nil)) (by decide) (by decide))

theorem cover15868 : P.CoversSplit 26 10 15868 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15868_0 : P.sumLeaves 26 16248832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15868) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15868 (by decide)
  decide +kernel

theorem h15868 : P.leaf 36 15868 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15868_0 (.nil)) (by decide) (by decide))

theorem cover15869 : P.CoversSplit 26 10 15869 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15869_0 : P.sumLeaves 26 16249856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15869) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15869 (by decide)
  decide +kernel

theorem h15869 : P.leaf 36 15869 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15869_0 (.nil)) (by decide) (by decide))

theorem cover15870 : P.CoversSplit 26 10 15870 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15870_0 : P.sumLeaves 26 16250880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15870) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15870 (by decide)
  decide +kernel

theorem h15870 : P.leaf 36 15870 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15870_0 (.nil)) (by decide) (by decide))

theorem cover15871 : P.CoversSplit 26 10 15871 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15871_0 : P.sumLeaves 26 16251904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15871) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem h15871 : P.leaf 36 15871 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15871_0 (.nil)) (by decide) (by decide))

theorem cover16176 : P.CoversSplit 26 10 16176 0x8000800000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16176_0 : P.sumLeaves 26 16564224 1024 = 1792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16176) (lo := 0) (len := 1024) (W := 1792) check rows elimOK (by decide) (by decide) cover16176 (by decide)
  decide +kernel

theorem h16176 : P.leaf 36 16176 = 1792 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1792)]) (.cons c16176_0 (.nil)) (by decide) (by decide))

theorem cover16177 : P.CoversSplit 26 10 16177 0x8000800000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16177_0 : P.sumLeaves 26 16565248 1024 = 98624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16177) (lo := 0) (len := 1024) (W := 98624) check rows elimOK (by decide) (by decide) cover16177 (by decide)
  decide +kernel

theorem h16177 : P.leaf 36 16177 = 98624 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 98624)]) (.cons c16177_0 (.nil)) (by decide) (by decide))

theorem cover16178 : P.CoversSplit 26 10 16178 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16178_0 : P.sumLeaves 26 16566272 1024 = 132428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16178) (lo := 0) (len := 1024) (W := 132428) check rows elimOK (by decide) (by decide) cover16178 (by decide)
  decide +kernel

theorem h16178 : P.leaf 36 16178 = 132428 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 132428)]) (.cons c16178_0 (.nil)) (by decide) (by decide))

theorem cover16179 : P.CoversSplit 26 10 16179 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c16179_0 : P.sumLeaves 26 16567296 1024 = 929536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16179) (lo := 0) (len := 1024) (W := 929536) check rows elimOK (by decide) (by decide) cover16179 (by decide)
  decide +kernel

theorem h16179 : P.leaf 36 16179 = 929536 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 929536)]) (.cons c16179_0 (.nil)) (by decide) (by decide))

theorem cover16182 : P.CoversSplit 26 10 16182 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c16182_0 : P.sumLeaves 26 16570368 1024 = 1886080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16182) (lo := 0) (len := 1024) (W := 1886080) check rows elimOK (by decide) (by decide) cover16182 (by decide)
  decide +kernel

theorem h16182 : P.leaf 36 16182 = 1886080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1886080)]) (.cons c16182_0 (.nil)) (by decide) (by decide))

theorem cover16183 : P.CoversSplit 26 10 16183 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c16183_0 : P.sumLeaves 26 16571392 1024 = 8822848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16183) (lo := 0) (len := 1024) (W := 8822848) check rows elimOK (by decide) (by decide) cover16183 (by decide)
  decide +kernel

theorem h16183 : P.leaf 36 16183 = 8822848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8822848)]) (.cons c16183_0 (.nil)) (by decide) (by decide))

theorem cover16184 : P.CoversSplit 26 10 16184 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000050500000001000005050000000100000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 579, 874, 930, 972, 1273, 1322, 1665]) (ps := [(21, [867], [929])]) (by decide +kernel)

theorem c16184_0 : P.sumLeaves 26 16572416 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16184) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover16184 (by decide)
  decide +kernel

theorem contract16184_1 : P.leaf 32 258951 = 2256 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 258951) (ss := [(7, 1, 474), (2, 1, 482), (28, 1, 579), (4, 1, 580), (3, 1, 409), (11, 1, 459), (13, 1, 923), (12, 1, 460), (21, 1, 929), (9, 1, 572), (20, 1, 572), (15, 1, 916), (30, 1, 972), (29, 0, 1322), (31, 0, 1322), (27, 1, 489)]) (ids := [3, 4, 6, 8, 12, 14, 15, 16, 17, 20, 21, 22, 30, 31, 23, 24]) (cs := [1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 1, 1, 6, 1, 7, 8, 9, 10, 1, 1, 11, 12, 13, 16, 17, 1, 1, 0, 1, 0, 14, 15]) (bs := [14, 2]) (W := 2256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16184_1 : P.sumLeaves 26 16572864 64 = 2256 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 258951) rows (by decide) (by decide)).symm.trans contract16184_1

theorem c16184_2 : P.sumLeaves 26 16572928 512 = 43074 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16184) (lo := 512) (len := 512) (W := 43074) check rows elimOK (by decide) (by decide) cover16184 (by decide)
  decide +kernel

theorem h16184 : P.leaf 36 16184 = 45330 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 2256), (512, 43074)]) (.cons c16184_0 (.cons c16184_1 (.cons c16184_2 (.nil)))) (by decide) (by decide))

theorem cover16185 : P.CoversSplit 26 10 16185 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000050500000001000005050000000100000001000000010000000000000000000200020002000200000000000000000000000000000000000000000000000000000001000000010000000100000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 930, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem c16185_0 : P.sumLeaves 26 16573440 448 = 1040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16185) (lo := 0) (len := 448) (W := 1040) check rows elimOK (by decide) (by decide) cover16185 (by decide)
  decide +kernel

theorem contract16185_1 : P.leaf 32 258967 = 30368 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 258967) (ss := [(7, 1, 474), (2, 1, 482), (28, 1, 579), (4, 1, 580), (13, 1, 923), (21, 1, 929), (9, 1, 572), (20, 1, 572), (15, 1, 916), (30, 1, 972), (29, 0, 1322), (31, 0, 1322)]) (ids := [1, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 25, 30, 31, 23, 24]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 6, 7, 8, 1, 9, 1, 10, 11, 12, 13, 1, 1, 14, 15, 16, 20, 21, 17, 1, 0, 1, 0, 18, 19]) (bs := [18, 2]) (W := 30368) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16185_1 : P.sumLeaves 26 16573888 64 = 30368 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 258967) rows (by decide) (by decide)).symm.trans contract16185_1

theorem c16185_2 : P.sumLeaves 26 16573952 512 = 1135112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16185) (lo := 512) (len := 512) (W := 1135112) check rows elimOK (by decide) (by decide) cover16185 (by decide)
  decide +kernel

theorem h16185 : P.leaf 36 16185 = 1166520 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 1040), (64, 30368), (512, 1135112)]) (.cons c16185_0 (.cons c16185_1 (.cons c16185_2 (.nil)))) (by decide) (by decide))

theorem cover16186 : P.CoversSplit 26 10 16186 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 874, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16186_0 : P.sumLeaves 26 16574464 1024 = 2329284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16186) (lo := 0) (len := 1024) (W := 2329284) check rows elimOK (by decide) (by decide) cover16186 (by decide)
  decide +kernel

theorem h16186 : P.leaf 36 16186 = 2329284 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2329284)]) (.cons c16186_0 (.nil)) (by decide) (by decide))

theorem cover16187 : P.CoversSplit 26 10 16187 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16187_0 : P.sumLeaves 26 16575488 1024 = 8269264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16187) (lo := 0) (len := 1024) (W := 8269264) check rows elimOK (by decide) (by decide) cover16187 (by decide)
  decide +kernel

theorem h16187 : P.leaf 36 16187 = 8269264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8269264)]) (.cons c16187_0 (.nil)) (by decide) (by decide))

theorem cover16190 : P.CoversSplit 26 10 16190 0xfffffffa00000030000000000000000000330032000000300000000000000000555550500000001055555050000000100000000000000000000000000000000000330032003300300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 579, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (ps := [(21, [867], [1658])]) (by decide +kernel)

theorem c16190_0 : P.sumLeaves 26 16578560 1024 = 14821432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16190) (lo := 0) (len := 1024) (W := 14821432) check rows elimOK (by decide) (by decide) cover16190 (by decide)
  decide +kernel

theorem h16190 : P.leaf 36 16190 = 14821432 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14821432)]) (.cons c16190_0 (.nil)) (by decide) (by decide))

theorem cover16191 : P.CoversSplit 26 10 16191 0xfffffffa00000030000000000000000000330032000000300000000000000000555550500000001055555050000000100011001000000010000000000000000000330032003300300000000000000000000000000000000000000000000000000011001000110010001100100011001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16191_0 : P.sumLeaves 26 16579584 192 = 11648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16191) (lo := 0) (len := 192) (W := 11648) check rows elimOK (by decide) (by decide) cover16191 (by decide)
  decide +kernel

theorem contract16191_1 : P.leaf 32 259059 = 8000 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 259059) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (7, 1, 825), (13, 1, 923), (8, 1, 1217), (29, 0, 1322), (31, 0, 1322), (21, 0, 1658), (9, 0, 1609), (28, 0, 1658), (20, 1, 1665)]) (ids := [4, 8, 9, 10, 12, 13, 14, 15, 16, 17, 21, 23, 24, 25, 28, 30, 31, 22]) (cs := [1, 1, 1, 1, 2, 1, 1, 0, 3, 4, 5, 1, 6, 7, 8, 9, 10, 11, 1, 0, 1, 12, 19, 13, 14, 15, 0, 0, 16, 0, 17, 18]) (bs := [17, 1]) (W := 8000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c16191_1 : P.sumLeaves 26 16579776 64 = 8000 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 259059) rows (by decide) (by decide)).symm.trans contract16191_1

theorem c16191_2 : P.sumLeaves 26 16579840 768 = 49329228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16191) (lo := 256) (len := 768) (W := 49329228) check rows elimOK (by decide) (by decide) cover16191 (by decide)
  decide +kernel

theorem h16191 : P.leaf 36 16191 = 49348876 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 11648), (64, 8000), (768, 49329228)]) (.cons c16191_0 (.cons c16191_1 (.cons c16191_2 (.nil)))) (by decide) (by decide))

theorem cover16208 : P.CoversSplit 26 10 16208 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16208_0 : P.sumLeaves 26 16596992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16208) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16208 (by decide)
  decide +kernel

theorem h16208 : P.leaf 36 16208 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16208_0 (.nil)) (by decide) (by decide))

theorem cover16209 : P.CoversSplit 26 10 16209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16209_0 : P.sumLeaves 26 16598016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16209) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16209 (by decide)
  decide +kernel

theorem h16209 : P.leaf 36 16209 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16209_0 (.nil)) (by decide) (by decide))

theorem cover16210 : P.CoversSplit 26 10 16210 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16210_0 : P.sumLeaves 26 16599040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16210) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16210 (by decide)
  decide +kernel

theorem h16210 : P.leaf 36 16210 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16210_0 (.nil)) (by decide) (by decide))

theorem cover16211 : P.CoversSplit 26 10 16211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16211_0 : P.sumLeaves 26 16600064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16211) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16211 (by decide)
  decide +kernel

theorem h16211 : P.leaf 36 16211 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16211_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(15853, 720), (15854, 720), (15855, 720), (15859, 360), (15860, 720), (15861, 720), (15862, 720), (15863, 720), (15864, 720), (15865, 720), (15866, 720), (15867, 720), (15868, 720), (15869, 720), (15870, 720), (15871, 720), (16176, 360), (16177, 360), (16178, 720), (16179, 720), (16182, 360), (16183, 360), (16184, 360), (16185, 360), (16186, 720), (16187, 720), (16190, 360), (16191, 360), (16208, 720), (16209, 720), (16210, 720), (16211, 720)]

theorem segOK : checkSeg 20 perms 15853 16212 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 15853 16212 19800 35824509360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 35824509360)
    (SegSum.cons (w := 720) h15853 (SegSum.cons (w := 720) h15854 (SegSum.cons (w := 720) h15855 (SegSum.cons (w := 360) h15859 (SegSum.cons (w := 720) h15860 (SegSum.cons (w := 720) h15861 (SegSum.cons (w := 720) h15862 (SegSum.cons (w := 720) h15863 (SegSum.cons (w := 720) h15864 (SegSum.cons (w := 720) h15865 (SegSum.cons (w := 720) h15866 (SegSum.cons (w := 720) h15867 (SegSum.cons (w := 720) h15868 (SegSum.cons (w := 720) h15869 (SegSum.cons (w := 720) h15870 (SegSum.cons (w := 720) h15871 (SegSum.cons (w := 360) h16176 (SegSum.cons (w := 360) h16177 (SegSum.cons (w := 720) h16178 (SegSum.cons (w := 720) h16179 (SegSum.cons (w := 360) h16182 (SegSum.cons (w := 360) h16183 (SegSum.cons (w := 360) h16184 (SegSum.cons (w := 360) h16185 (SegSum.cons (w := 720) h16186 (SegSum.cons (w := 720) h16187 (SegSum.cons (w := 360) h16190 (SegSum.cons (w := 360) h16191 (SegSum.cons (w := 720) h16208 (SegSum.cons (w := 720) h16209 (SegSum.cons (w := 720) h16210 (SegSum.cons (w := 720) h16211 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S31
