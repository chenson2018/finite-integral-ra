/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S69

open RACert RACert.Problem

theorem cover21734 : P.CoversSplit 24 10 21734 0xf0f00000f0f000000000000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 522, 573, 858, 860, 865, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21734_0 : P.sumLeaves 24 22255616 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21734) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover21734 (by decide)
  decide +kernel

theorem contract21734_1 : P.leaf 30 347751 = 0 := by
  exact leaf_contract_zero (ss := [(10, 1, 508), (18, 1, 536), (27, 1, 573), (14, 0, 867), (12, 1, 825), (6, 1, 458), (15, 1, 909), (29, 1, 916), (8, 0, 923), (28, 1, 468), (5, 1, 475), (4, 1, 426), (2, 1, 412), (21, 1, 482), (20, 1, 488), (30, 1, 524)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21734_1 : P.sumLeaves 24 22256064 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347751) rows (by decide) (by decide)).symm.trans contract21734_1

theorem c21734_2 : P.sumLeaves 24 22256128 512 = 373256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21734) (lo := 512) (len := 512) (W := 373256) check rows elimOK (by decide) (by decide) cover21734 (by decide)
  decide +kernel

theorem h21734 : P.leaf 34 21734 = 373256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 0), (512, 373256)]) (.cons c21734_0 (.cons c21734_1 (.cons c21734_2 (.nil)))) (by decide) (by decide))

theorem cover21735 : P.CoversSplit 24 10 21735 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 515, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21735_0 : P.sumLeaves 24 22256640 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21735) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover21735 (by decide)
  decide +kernel

theorem contract21735_1 : P.leaf 30 347767 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 536), (27, 1, 573), (14, 0, 867), (15, 1, 909), (29, 1, 916), (8, 0, 923), (5, 1, 475), (4, 1, 426), (30, 1, 524), (21, 0, 580), (20, 1, 586), (28, 1, 858)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21735_1 : P.sumLeaves 24 22257088 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347767) rows (by decide) (by decide)).symm.trans contract21735_1

theorem c21735_2 : P.sumLeaves 24 22257152 512 = 2962711 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21735) (lo := 512) (len := 512) (W := 2962711) check rows elimOK (by decide) (by decide) cover21735 (by decide)
  decide +kernel

theorem h21735 : P.leaf 34 21735 = 2962711 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 0), (512, 2962711)]) (.cons c21735_0 (.cons c21735_1 (.cons c21735_2 (.nil)))) (by decide) (by decide))

theorem cover21736 : P.CoversSplit 24 10 21736 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c21736_0 : P.sumLeaves 24 22257664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21736) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21736 (by decide)
  decide +kernel

theorem h21736 : P.leaf 34 21736 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21736_0 (.nil)) (by decide) (by decide))

theorem cover21737 : P.CoversSplit 24 10 21737 0xf0f00000e0e00000f0f00000e0e00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c0c000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [472, 473, 515, 522, 573, 858, 860, 916, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21737_0 : P.sumLeaves 24 22258688 320 = 48 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21737) (lo := 0) (len := 320) (W := 48) check rows elimOK (by decide) (by decide) cover21737 (by decide)
  decide +kernel

theorem contract21737_1 : P.leaf 30 347797 = 160 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 347797) (ss := [(30, 1, 472), (14, 0, 487), (4, 1, 508), (18, 1, 524), (27, 1, 573), (8, 0, 874), (5, 1, 426), (2, 1, 410), (11, 1, 475), (6, 1, 460), (12, 1, 460), (20, 1, 482), (21, 0, 488), (29, 15, 558), (7, 1, 628), (10, 1, 811), (13, 1, 971), (31, 1, 1210), (28, 1, 858), (16, 1, 1314)]) (ids := [7, 13, 15, 17, 21, 1, 20, 22, 23, 24]) (cs := [1, 7, 1, 1, 1, 1, 0, 2, 1, 1, 1, 1, 0, 3, 1, 4, 1, 5, 1, 0, 8, 6, 9, 10, 11, 1, 1, 3, 1, 1]) (bs := [5, 5]) (W := 160) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21737_1 : P.sumLeaves 24 22259008 64 = 160 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347797) rows (by decide) (by decide)).symm.trans contract21737_1

theorem c21737_2 : P.sumLeaves 24 22259072 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21737) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover21737 (by decide)
  decide +kernel

theorem contract21737_3 : P.leaf 30 347799 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 472), (14, 0, 487), (8, 1, 488), (18, 1, 475), (15, 1, 488), (4, 1, 508), (27, 1, 573), (29, 1, 916), (2, 1, 410), (28, 1, 858), (21, 0, 923), (20, 1, 929), (12, 1, 951), (6, 1, 460), (10, 1, 811), (11, 1, 818)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21737_3 : P.sumLeaves 24 22259136 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347799) rows (by decide) (by decide)).symm.trans contract21737_3

theorem c21737_4 : P.sumLeaves 24 22259200 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21737) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover21737 (by decide)
  decide +kernel

theorem contract21737_5 : P.leaf 30 347804 = 22120 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 347804) (ss := [(30, 1, 472), (14, 1, 487), (4, 1, 508), (18, 11, 879), (29, 15, 909), (31, 1, 1210), (28, 1, 858), (11, 1, 1264), (12, 1, 803), (21, 17, 1266), (20, 1, 1272)]) (ids := [0, 1, 3, 4, 5, 6, 7, 8, 11, 13, 14, 15, 17, 20, 21, 23, 24, 25, 22]) (cs := [2, 3, 1, 4, 5, 6, 7, 8, 9, 1, 1, 10, 1, 11, 12, 13, 1, 14, 1, 13, 15, 16, 20, 17, 18, 19, 1, 11, 1, 1]) (bs := [18, 1]) (W := 22120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21737_5 : P.sumLeaves 24 22259456 64 = 22120 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347804) rows (by decide) (by decide)).symm.trans contract21737_5

theorem c21737_6 : P.sumLeaves 24 22259520 192 = 467178 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21737) (lo := 832) (len := 192) (W := 467178) check rows elimOK (by decide) (by decide) cover21737 (by decide)
  decide +kernel

theorem h21737 : P.leaf 34 21737 = 489506 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 48), (64, 160), (64, 0), (64, 0), (256, 0), (64, 22120), (192, 467178)]) (.cons c21737_0 (.cons c21737_1 (.cons c21737_2 (.cons c21737_3 (.cons c21737_4 (.cons c21737_5 (.cons c21737_6 (.nil)))))))) (by decide) (by decide))

theorem cover21738 : P.CoversSplit 24 10 21738 0xf0f00000f0f000000000000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 515, 522, 573, 858, 860, 865, 916, 1202, 1210, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21738_0 : P.sumLeaves 24 22259712 448 = 256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21738) (lo := 0) (len := 448) (W := 256) check rows elimOK (by decide) (by decide) cover21738 (by decide)
  decide +kernel

theorem contract21738_1 : P.leaf 30 347815 = 0 := by
  exact leaf_contract_zero (ss := [(10, 1, 508), (18, 1, 536), (27, 1, 573), (12, 1, 803), (14, 0, 867), (6, 1, 460), (15, 1, 486), (11, 1, 818), (29, 1, 916), (8, 0, 923), (20, 1, 482), (21, 0, 488), (28, 1, 509), (30, 1, 524)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21738_1 : P.sumLeaves 24 22260160 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347815) rows (by decide) (by decide)).symm.trans contract21738_1

theorem c21738_2 : P.sumLeaves 24 22260224 512 = 704020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21738) (lo := 512) (len := 512) (W := 704020) check rows elimOK (by decide) (by decide) cover21738 (by decide)
  decide +kernel

theorem h21738 : P.leaf 34 21738 = 704276 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 256), (64, 0), (512, 704020)]) (.cons c21738_0 (.cons c21738_1 (.cons c21738_2 (.nil)))) (by decide) (by decide))

theorem cover21739 : P.CoversSplit 24 10 21739 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [472, 515, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21739_0 : P.sumLeaves 24 22260736 448 = 256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21739) (lo := 0) (len := 448) (W := 256) check rows elimOK (by decide) (by decide) cover21739 (by decide)
  decide +kernel

theorem contract21739_1 : P.leaf 30 347831 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 536), (27, 1, 573), (14, 0, 867), (12, 1, 487), (8, 1, 488), (6, 1, 460), (15, 1, 488), (10, 1, 811), (11, 1, 818), (29, 1, 916)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21739_1 : P.sumLeaves 24 22261184 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347831) rows (by decide) (by decide)).symm.trans contract21739_1

theorem c21739_2 : P.sumLeaves 24 22261248 512 = 2898818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21739) (lo := 512) (len := 512) (W := 2898818) check rows elimOK (by decide) (by decide) cover21739 (by decide)
  decide +kernel

theorem h21739 : P.leaf 34 21739 = 2899074 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 256), (64, 0), (512, 2898818)]) (.cons c21739_0 (.cons c21739_1 (.cons c21739_2 (.nil)))) (by decide) (by decide))

theorem cover21740 : P.CoversSplit 24 10 21740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem c21740_0 : P.sumLeaves 24 22261760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21740) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21740 (by decide)
  decide +kernel

theorem h21740 : P.leaf 34 21740 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21740_0 (.nil)) (by decide) (by decide))

theorem cover21741 : P.CoversSplit 24 10 21741 0xf0f00000e0ea0000f0f00000e0ea0000f0f000000000aaaaf0f000000000aa880000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000880000300000000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 858, 860, 865, 916, 1210, 1259, 1601]) (ps := [(8, [1217], [573]), (17, [1259], [1251])]) (by decide +kernel)

theorem c21741_0 : P.sumLeaves 24 22262784 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21741) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover21741 (by decide)
  decide +kernel

theorem contract21741_1 : P.leaf 30 347861 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 508), (18, 1, 487), (27, 1, 573), (14, 0, 867), (11, 1, 879), (12, 1, 818), (29, 15, 909), (15, 1, 916), (21, 0, 923), (8, 1, 874), (20, 1, 929)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21741_1 : P.sumLeaves 24 22263104 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347861) rows (by decide) (by decide)).symm.trans contract21741_1

theorem c21741_2 : P.sumLeaves 24 22263168 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21741) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover21741 (by decide)
  decide +kernel

theorem contract21741_3 : P.leaf 30 347863 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 508), (18, 1, 487), (27, 1, 573), (14, 0, 867), (15, 1, 909), (29, 1, 916), (21, 0, 923), (20, 1, 929), (8, 1, 972), (30, 1, 1266), (28, 1, 858)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21741_3 : P.sumLeaves 24 22263232 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347863) rows (by decide) (by decide)).symm.trans contract21741_3

theorem c21741_4 : P.sumLeaves 24 22263296 512 = 1686540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21741) (lo := 512) (len := 512) (W := 1686540) check rows elimOK (by decide) (by decide) cover21741 (by decide)
  decide +kernel

theorem h21741 : P.leaf 34 21741 = 1686540 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (64, 0), (64, 0), (512, 1686540)]) (.cons c21741_0 (.cons c21741_1 (.cons c21741_2 (.cons c21741_3 (.cons c21741_4 (.nil)))))) (by decide) (by decide))

theorem cover21742 : P.CoversSplit 24 10 21742 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21742_0 : P.sumLeaves 24 22263808 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21742) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover21742 (by decide)
  decide +kernel

theorem contract21742_1 : P.leaf 30 347879 = 0 := by
  exact leaf_contract_zero (ss := [(10, 1, 508), (18, 1, 536), (27, 1, 573), (14, 0, 867), (15, 1, 909), (29, 1, 916), (8, 0, 923), (30, 1, 524), (21, 0, 580), (20, 1, 482), (28, 1, 858)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21742_1 : P.sumLeaves 24 22264256 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347879) rows (by decide) (by decide)).symm.trans contract21742_1

theorem c21742_2 : P.sumLeaves 24 22264320 512 = 3013200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21742) (lo := 512) (len := 512) (W := 3013200) check rows elimOK (by decide) (by decide) cover21742 (by decide)
  decide +kernel

theorem h21742 : P.leaf 34 21742 = 3013200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 0), (512, 3013200)]) (.cons c21742_0 (.cons c21742_1 (.cons c21742_2 (.nil)))) (by decide) (by decide))

theorem cover21743 : P.CoversSplit 24 10 21743 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21743_0 : P.sumLeaves 24 22264832 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21743) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover21743 (by decide)
  decide +kernel

theorem contract21743_1 : P.leaf 30 347895 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 536), (27, 1, 573), (14, 0, 867), (15, 1, 909), (29, 1, 916), (8, 0, 923), (30, 1, 524), (21, 0, 580), (20, 1, 586), (28, 1, 858)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21743_1 : P.sumLeaves 24 22265280 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347895) rows (by decide) (by decide)).symm.trans contract21743_1

theorem c21743_2 : P.sumLeaves 24 22265344 512 = 5594138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21743) (lo := 512) (len := 512) (W := 5594138) check rows elimOK (by decide) (by decide) cover21743 (by decide)
  decide +kernel

theorem h21743 : P.leaf 34 21743 = 5594138 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 0), (512, 5594138)]) (.cons c21743_0 (.cons c21743_1 (.cons c21743_2 (.nil)))) (by decide) (by decide))

theorem cover21750 : P.CoversSplit 24 10 21750 0xf0f00000f0f00000f0f00000f0f00000f0f0000050500000f0f0000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21750_0 : P.sumLeaves 24 22272000 1024 = 2574462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21750) (lo := 0) (len := 1024) (W := 2574462) check rows elimOK (by decide) (by decide) cover21750 (by decide)
  decide +kernel

theorem h21750 : P.leaf 34 21750 = 2574462 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2574462)]) (.cons c21750_0 (.nil)) (by decide) (by decide))

theorem cover21751 : P.CoversSplit 24 10 21751 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21751_0 : P.sumLeaves 24 22273024 924 = 10323385 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21751) (lo := 0) (len := 924) (W := 10323385) check rows elimOK (by decide) (by decide) cover21751 (by decide)
  decide +kernel

theorem c21751_1 : P.sumLeaves 24 22273948 100 = 23474097 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21751) (lo := 924) (len := 100) (W := 23474097) check rows elimOK (by decide) (by decide) cover21751 (by decide)
  decide +kernel

theorem h21751 : P.leaf 34 21751 = 33797482 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 10323385), (100, 23474097)]) (.cons c21751_0 (.cons c21751_1 (.nil))) (by decide) (by decide))

theorem cover21753 : P.CoversSplit 24 10 21753 0xfffffffff0f00000fffffffff0f00000fffffffff0f00000fffffffff0f000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cccccccc8080000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [1217], [487]), (15, [909], [916])]) (by decide +kernel)

theorem c21753_0 : P.sumLeaves 24 22275072 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21753) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover21753 (by decide)
  decide +kernel

theorem contract21753_1 : P.leaf 30 348052 = 192 := by
  exact leaf_contract_factors (k := 30) (b := 8) (H := 348052) (ss := [(14, 0, 487), (8, 0, 874), (5, 1, 433), (18, 11, 475), (20, 1, 482), (21, 0, 488), (29, 15, 558), (12, 1, 608), (31, 1, 1217), (15, 0, 1259), (2, 1, 411), (7, 1, 474), (6, 1, 460), (23, 1, 803), (10, 1, 811), (28, 1, 860), (16, 1, 872), (13, 1, 971), (17, 0, 1259), (11, 1, 908), (27, 0, 1259), (9, 0, 573)]) (ids := [17, 23, 1, 2, 20, 22, 24, 28]) (cs := [1, 4, 5, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 2, 1, 0, 6, 1, 7, 3, 8, 0, 1, 0, 9, 1]) (bs := [2, 6]) (W := 192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21753_1 : P.sumLeaves 24 22275328 64 = 192 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 348052) rows (by decide) (by decide)).symm.trans contract21753_1

theorem c21753_2 : P.sumLeaves 24 22275392 128 = 1552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21753) (lo := 320) (len := 128) (W := 1552) check rows elimOK (by decide) (by decide) cover21753 (by decide)
  decide +kernel

theorem contract21753_3 : P.leaf 30 348055 = 0 := by
  exact leaf_contract_zero (ss := [(14, 0, 487), (8, 1, 488), (18, 1, 475), (15, 1, 488), (27, 1, 573), (29, 1, 916), (21, 0, 923), (20, 1, 929), (12, 1, 951), (6, 1, 460), (10, 1, 811), (11, 1, 818)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21753_3 : P.sumLeaves 24 22275520 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 348055) rows (by decide) (by decide)).symm.trans contract21753_3

theorem c21753_4 : P.sumLeaves 24 22275584 424 = 873736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21753) (lo := 512) (len := 424) (W := 873736) check rows elimOK (by decide) (by decide) cover21753 (by decide)
  decide +kernel

theorem c21753_5 : P.sumLeaves 24 22276008 88 = 2933220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21753) (lo := 936) (len := 88) (W := 2933220) check rows elimOK (by decide) (by decide) cover21753 (by decide)
  decide +kernel

theorem h21753 : P.leaf 34 21753 = 3808700 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 192), (128, 1552), (64, 0), (424, 873736), (88, 2933220)]) (.cons c21753_0 (.cons c21753_1 (.cons c21753_2 (.cons c21753_3 (.cons c21753_4 (.cons c21753_5 (.nil))))))) (by decide) (by decide))

theorem cover21755 : P.CoversSplit 24 10 21755 0xfffffffff0f00000fffffffff0f00000fffffffff0f00000fffffffff0f000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000cc00cc008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [1217], [867]), (15, [909], [916])]) (by decide +kernel)

theorem c21755_0 : P.sumLeaves 24 22277120 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21755) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover21755 (by decide)
  decide +kernel

theorem contract21755_1 : P.leaf 30 348085 = 1024 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 348085) (ss := [(27, 1, 573), (14, 0, 867), (12, 1, 487), (8, 0, 874), (5, 1, 433), (20, 1, 482), (21, 0, 488), (18, 1, 879), (7, 1, 628), (6, 1, 460), (10, 1, 811), (11, 1, 818), (15, 1, 909), (9, 1, 678), (29, 1, 916), (13, 1, 971), (31, 1, 1217), (16, 1, 1314), (17, 1, 1364), (19, 1, 1707)]) (ids := [0, 1, 2, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 4, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 5, 6, 7, 8, 9, 1, 10, 1, 11, 1]) (bs := [0, 10]) (W := 1024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21755_1 : P.sumLeaves 24 22277440 64 = 1024 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 348085) rows (by decide) (by decide)).symm.trans contract21755_1

theorem c21755_2 : P.sumLeaves 24 22277504 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21755) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover21755 (by decide)
  decide +kernel

theorem contract21755_3 : P.leaf 30 348087 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (14, 0, 867), (12, 1, 487), (6, 1, 460), (15, 1, 488), (10, 1, 811), (11, 1, 818), (29, 1, 916)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21755_3 : P.sumLeaves 24 22277568 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 348087) rows (by decide) (by decide)).symm.trans contract21755_3

theorem c21755_4 : P.sumLeaves 24 22277632 424 = 4417598 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21755) (lo := 512) (len := 424) (W := 4417598) check rows elimOK (by decide) (by decide) cover21755 (by decide)
  decide +kernel

theorem c21755_5 : P.sumLeaves 24 22278056 88 = 9876764 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21755) (lo := 936) (len := 88) (W := 9876764) check rows elimOK (by decide) (by decide) cover21755 (by decide)
  decide +kernel

theorem h21755 : P.leaf 34 21755 = 14295386 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 1024), (64, 0), (64, 0), (424, 4417598), (88, 9876764)]) (.cons c21755_0 (.cons c21755_1 (.cons c21755_2 (.cons c21755_3 (.cons c21755_4 (.cons c21755_5 (.nil))))))) (by decide) (by decide))

theorem cover21756 : P.CoversSplit 24 10 21756 0xf0f00000f0f00000f0f00000f0f00000f000000050000000f000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 909, 1202, 1210, 1601]) (by decide +kernel)

theorem c21756_0 : P.sumLeaves 24 22278144 1024 = 4308730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21756) (lo := 0) (len := 1024) (W := 4308730) check rows elimOK (by decide) (by decide) cover21756 (by decide)
  decide +kernel

theorem h21756 : P.leaf 34 21756 = 4308730 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4308730)]) (.cons c21756_0 (.nil)) (by decide) (by decide))

theorem cover21757 : P.CoversSplit 24 10 21757 0xfffffffffaf00000fffffffffaf00000ff00ff00fa000000ff00ff00fa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 860, 865, 867, 909, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21757_0 : P.sumLeaves 24 22279168 992 = 12864763 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21757) (lo := 0) (len := 992) (W := 12864763) check rows elimOK (by decide) (by decide) cover21757 (by decide)
  decide +kernel

theorem c21757_1 : P.sumLeaves 24 22280160 32 = 6374504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21757) (lo := 992) (len := 32) (W := 6374504) check rows elimOK (by decide) (by decide) cover21757 (by decide)
  decide +kernel

theorem h21757 : P.leaf 34 21757 = 19239267 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(992, 12864763), (32, 6374504)]) (.cons c21757_0 (.cons c21757_1 (.nil))) (by decide) (by decide))

theorem cover21758 : P.CoversSplit 24 10 21758 0xf0f00000f0f00000f0f00000f0f00000f0f0000050500000f0f0000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21758_0 : P.sumLeaves 24 22280192 1024 = 14561436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21758) (lo := 0) (len := 1024) (W := 14561436) check rows elimOK (by decide) (by decide) cover21758 (by decide)
  decide +kernel

theorem h21758 : P.leaf 34 21758 = 14561436 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14561436)]) (.cons c21758_0 (.nil)) (by decide) (by decide))

theorem cover21759 : P.CoversSplit 24 10 21759 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21759_0 : P.sumLeaves 24 22281216 924 = 24714445 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21759) (lo := 0) (len := 924) (W := 24714445) check rows elimOK (by decide) (by decide) cover21759 (by decide)
  decide +kernel

theorem c21759_1 : P.sumLeaves 24 22282140 100 = 51760076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21759) (lo := 924) (len := 100) (W := 51760076) check rows elimOK (by decide) (by decide) cover21759 (by decide)
  decide +kernel

theorem h21759 : P.leaf 34 21759 = 76474521 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 24714445), (100, 51760076)]) (.cons c21759_0 (.cons c21759_1 (.nil))) (by decide) (by decide))

theorem cover21796 : P.CoversSplit 24 10 21796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem c21796_0 : P.sumLeaves 24 22319104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21796) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21796 (by decide)
  decide +kernel

theorem h21796 : P.leaf 34 21796 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21796_0 (.nil)) (by decide) (by decide))

theorem cover21797 : P.CoversSplit 24 10 21797 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 860, 865, 916, 1202, 1601]) (by decide +kernel)

theorem c21797_0 : P.sumLeaves 24 22320128 1024 = 89207 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21797) (lo := 0) (len := 1024) (W := 89207) check rows elimOK (by decide) (by decide) cover21797 (by decide)
  decide +kernel

theorem h21797 : P.leaf 34 21797 = 89207 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 89207)]) (.cons c21797_0 (.nil)) (by decide) (by decide))

theorem cover21798 : P.CoversSplit 24 10 21798 0x8080000080800000000000000000000080800000000000000000000000000000808000008080000000000000000000008080000000000000000000000000000080800000808000000000000000000000808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 860, 865, 1259, 1601]) (ps := [(3, [508], [522])]) (by decide +kernel)

theorem c21798_0 : P.sumLeaves 24 22321152 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21798) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover21798 (by decide)
  decide +kernel

theorem contract21798_1 : P.leaf 30 348775 = 8624 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 348775) (ss := [(10, 1, 466), (8, 1, 468), (3, 1, 508), (27, 1, 522), (26, 1, 529), (6, 1, 458), (9, 1, 510), (28, 1, 858), (30, 1, 515), (4, 1, 417), (14, 0, 867), (12, 1, 825), (15, 1, 874), (18, 1, 879)]) (ids := [0, 3, 5, 9, 11, 14, 15, 17, 18, 19, 20, 27, 29, 21, 22, 23]) (cs := [2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 6, 0, 1, 7, 8, 1, 9, 10, 11, 12, 15, 16, 17, 1, 1, 1, 13, 1, 14]) (bs := [13, 3]) (W := 8624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21798_1 : P.sumLeaves 24 22321600 64 = 8624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 348775) rows (by decide) (by decide)).symm.trans contract21798_1

theorem c21798_2 : P.sumLeaves 24 22321664 512 = 53392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21798) (lo := 512) (len := 512) (W := 53392) check rows elimOK (by decide) (by decide) cover21798 (by decide)
  decide +kernel

theorem h21798 : P.leaf 34 21798 = 62016 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 8624), (512, 53392)]) (.cons c21798_0 (.cons c21798_1 (.cons c21798_2 (.nil)))) (by decide) (by decide))

theorem cover21799 : P.CoversSplit 24 10 21799 0x8080000080800000000000000000000080800000000004040000000000000000808000008080000000000000000000008080000000000404000000000000000080800000808000000000000000000000808000000000040400000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 1259, 1601]) (by decide +kernel)

theorem c21799_0 : P.sumLeaves 24 22322176 1024 = 1082042 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21799) (lo := 0) (len := 1024) (W := 1082042) check rows elimOK (by decide) (by decide) cover21799 (by decide)
  decide +kernel

theorem h21799 : P.leaf 34 21799 = 1082042 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1082042)]) (.cons c21799_0 (.nil)) (by decide) (by decide))

theorem cover21804 : P.CoversSplit 24 10 21804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c21804_0 : P.sumLeaves 24 22327296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21804) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21804 (by decide)
  decide +kernel

theorem h21804 : P.leaf 34 21804 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21804_0 (.nil)) (by decide) (by decide))

theorem cover21805 : P.CoversSplit 24 10 21805 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 860, 865, 916, 1202, 1601]) (by decide +kernel)

theorem c21805_0 : P.sumLeaves 24 22328320 1024 = 304976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21805) (lo := 0) (len := 1024) (W := 304976) check rows elimOK (by decide) (by decide) cover21805 (by decide)
  decide +kernel

theorem h21805 : P.leaf 34 21805 = 304976 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 304976)]) (.cons c21805_0 (.nil)) (by decide) (by decide))

theorem cover21806 : P.CoversSplit 24 10 21806 0x8080000080800000000000000000000080800000000000000000000000000000808000008080000000000000000000008080000000000000000000000000000080800000808000000000000000000000808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 860, 865, 1259, 1601]) (ps := [(3, [508], [522])]) (by decide +kernel)

theorem c21806_0 : P.sumLeaves 24 22329344 1024 = 265228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21806) (lo := 0) (len := 1024) (W := 265228) check rows elimOK (by decide) (by decide) cover21806 (by decide)
  decide +kernel

theorem h21806 : P.leaf 34 21806 = 265228 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 265228)]) (.cons c21806_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(21734, 48), (21735, 48), (21736, 12), (21737, 24), (21738, 24), (21739, 48), (21740, 48), (21741, 48), (21742, 48), (21743, 48), (21750, 48), (21751, 48), (21753, 12), (21755, 24), (21756, 48), (21757, 48), (21758, 48), (21759, 48), (21796, 24), (21797, 48), (21798, 48), (21799, 48), (21804, 48), (21805, 48), (21806, 48)]

theorem segOK : checkSeg 16 perms 21734 21807 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21734 21807 1032 8543282160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 8543282160)
    (SegSum.cons (w := 48) h21734 (SegSum.cons (w := 48) h21735 (SegSum.cons (w := 12) h21736 (SegSum.cons (w := 24) h21737 (SegSum.cons (w := 24) h21738 (SegSum.cons (w := 48) h21739 (SegSum.cons (w := 48) h21740 (SegSum.cons (w := 48) h21741 (SegSum.cons (w := 48) h21742 (SegSum.cons (w := 48) h21743 (SegSum.cons (w := 48) h21750 (SegSum.cons (w := 48) h21751 (SegSum.cons (w := 12) h21753 (SegSum.cons (w := 24) h21755 (SegSum.cons (w := 48) h21756 (SegSum.cons (w := 48) h21757 (SegSum.cons (w := 48) h21758 (SegSum.cons (w := 48) h21759 (SegSum.cons (w := 24) h21796 (SegSum.cons (w := 48) h21797 (SegSum.cons (w := 48) h21798 (SegSum.cons (w := 48) h21799 (SegSum.cons (w := 48) h21804 (SegSum.cons (w := 48) h21805 (SegSum.cons (w := 48) h21806 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S69
