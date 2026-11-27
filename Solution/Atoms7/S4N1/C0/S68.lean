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

namespace RACert.S4N1.C0.S68

open RACert RACert.Problem

theorem cover21668 : P.CoversSplit 24 10 21668 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c21668_0 : P.sumLeaves 24 22188032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21668) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21668 (by decide)
  decide +kernel

theorem h21668 : P.leaf 34 21668 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21668_0 (.nil)) (by decide) (by decide))

theorem cover21669 : P.CoversSplit 24 10 21669 0xa0a00000a0aa0000a0a00000a0aa0000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000a02000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 473, 515, 517, 522, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573])]) (by decide +kernel)

theorem c21669_0 : P.sumLeaves 24 22189056 768 = 160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21669) (lo := 0) (len := 768) (W := 160) check rows elimOK (by decide) (by decide) cover21669 (by decide)
  decide +kernel

theorem contract21669_1 : P.leaf 30 346716 = 4800 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 346716) (ss := [(30, 1, 466), (8, 1, 475), (31, 1, 468), (11, 4, 508), (26, 1, 515), (18, 4, 536), (27, 9, 566), (28, 1, 858), (14, 1, 867), (4, 1, 487), (5, 1, 404), (16, 1, 531), (9, 1, 559), (6, 1, 459), (29, 15, 909), (21, 17, 1266), (20, 1, 1272)]) (ids := [0, 1, 8, 10, 11, 13, 15, 20, 21, 5, 17, 22, 23]) (cs := [2, 3, 1, 1, 1, 11, 1, 1, 4, 1, 5, 6, 1, 7, 1, 8, 1, 12, 1, 8, 9, 10, 13, 14, 1, 1, 1, 7, 1, 1]) (bs := [9, 4]) (W := 4800) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21669_1 : P.sumLeaves 24 22189824 64 = 4800 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346716) rows (by decide) (by decide)).symm.trans contract21669_1

theorem contract21669_2 : P.leaf 30 346717 = 6848 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 346717) (ss := [(30, 1, 466), (8, 1, 475), (31, 1, 468), (11, 4, 508), (26, 1, 515), (18, 4, 536), (27, 9, 566), (28, 1, 858), (14, 1, 867), (4, 1, 487), (5, 1, 404), (16, 1, 531), (9, 1, 559), (6, 1, 459), (29, 15, 909), (17, 1, 1266)]) (ids := [0, 1, 5, 8, 10, 11, 13, 17, 18, 21, 19, 20, 22, 23]) (cs := [2, 3, 1, 1, 1, 4, 1, 1, 5, 1, 6, 7, 1, 8, 1, 1, 1, 9, 10, 12, 13, 11, 14, 15, 1, 1, 1, 8, 1, 1]) (bs := [10, 4]) (W := 6848) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21669_2 : P.sumLeaves 24 22189888 64 = 6848 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346717) rows (by decide) (by decide)).symm.trans contract21669_2

theorem c21669_3 : P.sumLeaves 24 22189952 128 = 90256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21669) (lo := 896) (len := 128) (W := 90256) check rows elimOK (by decide) (by decide) cover21669 (by decide)
  decide +kernel

theorem h21669 : P.leaf 34 21669 = 102064 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 160), (64, 4800), (64, 6848), (128, 90256)]) (.cons c21669_0 (.cons c21669_1 (.cons c21669_2 (.cons c21669_3 (.nil))))) (by decide) (by decide))

theorem cover21670 : P.CoversSplit 24 10 21670 0xa0a00000a0a00000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 515, 517, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [468], [524]), (9, [510], [566])]) (by decide +kernel)

theorem c21670_0 : P.sumLeaves 24 22190080 1024 = 56128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21670) (lo := 0) (len := 1024) (W := 56128) check rows elimOK (by decide) (by decide) cover21670 (by decide)
  decide +kernel

theorem h21670 : P.leaf 34 21670 = 56128 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 56128)]) (.cons c21670_0 (.nil)) (by decide) (by decide))

theorem cover21671 : P.CoversSplit 24 10 21671 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000a02000000000050100200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573])]) (by decide +kernel)

theorem c21671_0 : P.sumLeaves 24 22191104 320 = 24 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21671) (lo := 0) (len := 320) (W := 24) check rows elimOK (by decide) (by decide) cover21671 (by decide)
  decide +kernel

theorem contract21671_1 : P.leaf 30 346741 = 284 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 346741) (ss := [(8, 0, 524), (5, 1, 468), (14, 0, 531), (21, 0, 482), (20, 1, 433), (18, 1, 536), (4, 1, 426), (2, 1, 412), (3, 1, 419), (27, 9, 566), (7, 1, 628), (29, 15, 909), (13, 1, 971), (16, 1, 1314)]) (ids := [4, 7, 8, 9, 10, 13, 15, 17, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [1, 1, 1, 1, 2, 1, 0, 3, 4, 5, 6, 1, 0, 7, 1, 8, 1, 9, 1, 0, 10, 11, 12, 17, 13, 3, 14, 7, 15, 16]) (bs := [15, 1]) (W := 284) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21671_1 : P.sumLeaves 24 22191424 64 = 284 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346741) rows (by decide) (by decide)).symm.trans contract21671_1

theorem c21671_2 : P.sumLeaves 24 22191488 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21671) (lo := 384) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover21671 (by decide)
  decide +kernel

theorem contract21671_3 : P.leaf 30 346748 = 18240 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 346748) (ss := [(30, 1, 466), (8, 1, 524), (18, 1, 536), (27, 9, 566), (14, 1, 867), (16, 1, 531), (29, 15, 909), (31, 1, 1210), (26, 1, 515), (28, 1, 858), (21, 17, 1266), (20, 1, 1272)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 14, 1, 15, 1, 14, 16, 17, 18, 19, 1, 8, 1, 13, 1, 1]) (bs := [16, 2]) (W := 18240) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21671_3 : P.sumLeaves 24 22191872 64 = 18240 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346748) rows (by decide) (by decide)).symm.trans contract21671_3

theorem c21671_4 : P.sumLeaves 24 22191936 192 = 354802 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21671) (lo := 832) (len := 192) (W := 354802) check rows elimOK (by decide) (by decide) cover21671 (by decide)
  decide +kernel

theorem h21671 : P.leaf 34 21671 = 373350 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 24), (64, 284), (384, 0), (64, 18240), (192, 354802)]) (.cons c21671_0 (.cons c21671_1 (.cons c21671_2 (.cons c21671_3 (.cons c21671_4 (.nil)))))) (by decide) (by decide))

theorem cover21676 : P.CoversSplit 24 10 21676 0xa0a00000b0ba0000a0a00000b0ba0000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573])]) (by decide +kernel)

noncomputable def f21676 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22196224 + i)

theorem c21676_0 : rowSum f21676 0 1024 = 362276 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21676) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21676 (by decide)
  decide +kernel

theorem sum21676 : rowSum f21676 0 1024 = 362276 :=
  c21676_0

theorem h21676 : P.leaf 34 21676 = 362276 :=
  leaf_weighted (k := 24) (d := 10) (H := 21676) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 21676) (by decide) (by decide +kernel)) sum21676

theorem cover21677 : P.CoversSplit 24 10 21677 0xa0a00000b0ba0000a0a00000b0ba0000a0a0000000000505a0a0000000000504000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000040100200000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573]), (17, [1259], [1251])]) (by decide +kernel)

noncomputable def f21677 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22197248 + i)

theorem c21677_0 : rowSum f21677 0 1024 = 334744 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21677) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21677 (by decide)
  decide +kernel

theorem sum21677 : rowSum f21677 0 1024 = 334744 :=
  c21677_0

theorem h21677 : P.leaf 34 21677 = 334744 :=
  leaf_weighted (k := 24) (d := 10) (H := 21677) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 21677) (by decide) (by decide +kernel)) sum21677

theorem cover21678 : P.CoversSplit 24 10 21678 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573])]) (by decide +kernel)

noncomputable def f21678 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22198272 + i)

theorem c21678_0 : rowSum f21678 0 1024 = 377740 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21678) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21678 (by decide)
  decide +kernel

theorem sum21678 : rowSum f21678 0 1024 = 377740 :=
  c21678_0

theorem h21678 : P.leaf 34 21678 = 377740 :=
  leaf_weighted (k := 24) (d := 10) (H := 21678) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 21678) (by decide) (by decide +kernel)) sum21678

theorem cover21679 : P.CoversSplit 24 10 21679 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000504000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000040100200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 858, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [565], [524]), (9, [566], [573]), (17, [1259], [1251])]) (by decide +kernel)

noncomputable def f21679 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22199296 + i)

theorem c21679_0 : rowSum f21679 0 1024 = 640420 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21679) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21679 (by decide)
  decide +kernel

theorem sum21679 : rowSum f21679 0 1024 = 640420 :=
  c21679_0

theorem h21679 : P.leaf 34 21679 = 640420 :=
  leaf_weighted (k := 24) (d := 10) (H := 21679) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 21679) (by decide) (by decide +kernel)) sum21679

theorem cover21685 : P.CoversSplit 24 10 21685 0xffffffffaaa00000ffffffffaaa00000f500f50000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 573, 858, 860, 865, 867, 909, 1202, 1210, 1251, 1601]) (by decide +kernel)

theorem c21685_0 : P.sumLeaves 24 22205440 768 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21685) (lo := 0) (len := 768) (W := 0) check rows elimOK (by decide) (by decide) cover21685 (by decide)
  decide +kernel

theorem contract21685_1 : P.leaf 30 346972 = 32832 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 346972) (ss := [(8, 1, 475), (31, 1, 468), (16, 1, 531), (9, 1, 559), (14, 1, 874), (18, 1, 487), (28, 1, 860), (11, 1, 879), (29, 1, 909), (30, 1, 1251), (17, 1, 1266)]) (ids := [0, 1, 2, 3, 4, 5, 8, 10, 11, 13, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 1, 8, 1, 9, 10, 1, 11, 1, 1, 1, 12, 13, 14, 15, 16, 19, 20, 17, 18, 1, 1, 1, 1]) (bs := [17, 2]) (W := 32832) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21685_1 : P.sumLeaves 24 22206208 64 = 32832 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346972) rows (by decide) (by decide)).symm.trans contract21685_1

theorem contract21685_2 : P.leaf 30 346973 = 65792 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 346973) (ss := [(8, 1, 475), (31, 1, 468), (16, 1, 531), (9, 1, 559), (14, 1, 874), (18, 1, 487), (28, 1, 860), (11, 1, 879), (29, 1, 909), (17, 1, 1266)]) (ids := [0, 1, 2, 3, 4, 5, 8, 10, 11, 13, 17, 18, 19, 20, 21, 24, 25, 28, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 1, 8, 1, 9, 10, 1, 11, 1, 1, 1, 12, 13, 14, 15, 16, 20, 21, 17, 18, 1, 1, 19, 1]) (bs := [18, 2]) (W := 65792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21685_2 : P.sumLeaves 24 22206272 64 = 65792 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346973) rows (by decide) (by decide)).symm.trans contract21685_2

theorem c21685_3 : P.sumLeaves 24 22206336 128 = 955122 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21685) (lo := 896) (len := 128) (W := 955122) check rows elimOK (by decide) (by decide) cover21685 (by decide)
  decide +kernel

theorem h21685 : P.leaf 34 21685 = 1053746 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 0), (64, 32832), (64, 65792), (128, 955122)]) (.cons c21685_0 (.cons c21685_1 (.cons c21685_2 (.cons c21685_3 (.nil))))) (by decide) (by decide))

theorem cover21686 : P.CoversSplit 24 10 21686 0xf0f00000a0a00000f0f00000a0a00000f000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 860, 865, 867, 909, 1210, 1601]) (by decide +kernel)

theorem c21686_0 : P.sumLeaves 24 22206464 768 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21686) (lo := 0) (len := 768) (W := 0) check rows elimOK (by decide) (by decide) cover21686 (by decide)
  decide +kernel

theorem contract21686_1 : P.leaf 30 346988 = 17408 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 346988) (ss := [(2, 1, 466), (5, 1, 404), (8, 1, 468), (9, 1, 510), (16, 1, 531), (18, 1, 879), (29, 1, 909), (30, 1, 1251), (28, 1, 858), (31, 1, 1217), (17, 1, 1266)]) (ids := [1, 2, 4, 5, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20, 21, 23, 24, 25, 22]) (cs := [1, 2, 3, 1, 4, 5, 1, 1, 6, 7, 8, 9, 10, 11, 1, 1, 1, 12, 13, 14, 15, 16, 20, 17, 18, 19, 1, 1, 1, 1]) (bs := [18, 1]) (W := 17408) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21686_1 : P.sumLeaves 24 22207232 64 = 17408 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 346988) rows (by decide) (by decide)).symm.trans contract21686_1

theorem c21686_2 : P.sumLeaves 24 22207296 192 = 372768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21686) (lo := 832) (len := 192) (W := 372768) check rows elimOK (by decide) (by decide) cover21686 (by decide)
  decide +kernel

theorem h21686 : P.leaf 34 21686 = 390176 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 0), (64, 17408), (192, 372768)]) (.cons c21686_0 (.cons c21686_1 (.cons c21686_2 (.nil)))) (by decide) (by decide))

theorem cover21687 : P.CoversSplit 24 10 21687 0xffffffffaaaa0000ffffffffaaaa0000f500f50000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 860, 865, 867, 909, 1202, 1210, 1251, 1601]) (by decide +kernel)

theorem c21687_0 : P.sumLeaves 24 22207488 1022 = 5001830 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21687) (lo := 0) (len := 1022) (W := 5001830) check rows elimOK (by decide) (by decide) cover21687 (by decide)
  decide +kernel

theorem c21687_1 : P.sumLeaves 24 22208510 2 = 353792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21687) (lo := 1022) (len := 2) (W := 353792) check rows elimOK (by decide) (by decide) cover21687 (by decide)
  decide +kernel

theorem h21687 : P.leaf 34 21687 = 5355622 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1022, 5001830), (2, 353792)]) (.cons c21687_0 (.cons c21687_1 (.nil))) (by decide) (by decide))

theorem cover21689 : P.CoversSplit 24 10 21689 0xfffffffff0f00000fffffffff0f00000f0f0f0f000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000c0ffc0ffc8f0000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 573, 858, 860, 865, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(8, [580], [573]), (14, [487], [860]), (15, [558, 909], [860, 916])]) (by decide +kernel)

theorem c21689_0 : P.sumLeaves 24 22209536 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21689) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover21689 (by decide)
  decide +kernel

theorem contract21689_1 : P.leaf 30 347028 = 60 := by
  exact leaf_contract_factors (k := 30) (b := 7) (H := 347028) (ss := [(14, 0, 487), (31, 12, 486), (8, 0, 874), (18, 11, 475), (21, 0, 488), (5, 1, 524), (20, 1, 433), (29, 15, 558), (12, 1, 608), (30, 1, 1251), (15, 0, 1259), (2, 1, 411), (7, 1, 474), (6, 1, 460), (23, 1, 803), (10, 1, 852), (16, 1, 872), (13, 1, 971), (17, 0, 1259), (11, 1, 908), (4, 1, 426), (27, 0, 1259), (9, 0, 573)]) (ids := [1, 22, 24, 26, 17, 23, 20]) (cs := [1, 2, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 6, 1, 0, 8, 1, 3, 7, 4, 0, 5, 0, 1, 1]) (bs := [4, 2, 1]) (W := 60) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21689_1 : P.sumLeaves 24 22209792 64 = 60 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347028) rows (by decide) (by decide)).symm.trans contract21689_1

theorem c21689_2 : P.sumLeaves 24 22209856 128 = 1676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21689) (lo := 320) (len := 128) (W := 1676) check rows elimOK (by decide) (by decide) cover21689 (by decide)
  decide +kernel

theorem contract21689_3 : P.leaf 30 347031 = 0 := by
  exact leaf_contract_zero (ss := [(14, 0, 487), (12, 1, 486), (8, 1, 488), (6, 1, 460), (18, 1, 475), (15, 1, 488), (27, 1, 573), (10, 1, 811), (11, 1, 818), (29, 1, 916), (21, 0, 923), (20, 1, 929)]) (q := 972) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21689_3 : P.sumLeaves 24 22209984 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347031) rows (by decide) (by decide)).symm.trans contract21689_3

theorem c21689_4 : P.sumLeaves 24 22210048 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21689) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover21689 (by decide)
  decide +kernel

theorem contract21689_5 : P.leaf 30 347036 = 39456 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 347036) (ss := [(14, 1, 487), (31, 1, 486), (8, 1, 531), (18, 1, 475), (16, 1, 531), (15, 1, 558), (28, 1, 860), (11, 1, 879), (12, 1, 803), (29, 1, 909), (30, 1, 1251), (17, 1, 1266)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 18, 19, 20, 24, 25, 21, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 10, 1, 1, 1, 1, 1, 11, 12, 13, 14, 17, 18, 19, 15, 16, 1, 1, 1, 1]) (bs := [15, 3]) (W := 39456) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21689_5 : P.sumLeaves 24 22210304 64 = 39456 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347036) rows (by decide) (by decide)).symm.trans contract21689_5

theorem contract21689_6 : P.leaf 30 347037 = 80768 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 347037) (ss := [(14, 1, 487), (31, 1, 486), (8, 1, 531), (18, 1, 475), (16, 1, 531), (15, 1, 558), (28, 1, 860), (11, 1, 879), (12, 1, 803), (29, 1, 909), (17, 1, 1266)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 18, 19, 20, 24, 25, 28, 21, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 10, 1, 1, 1, 1, 1, 11, 12, 13, 14, 18, 19, 20, 15, 16, 1, 1, 17, 1]) (bs := [16, 3]) (W := 80768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21689_6 : P.sumLeaves 24 22210368 64 = 80768 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347037) rows (by decide) (by decide)).symm.trans contract21689_6

theorem c21689_7 : P.sumLeaves 24 22210432 128 = 1523824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21689) (lo := 896) (len := 128) (W := 1523824) check rows elimOK (by decide) (by decide) cover21689 (by decide)
  decide +kernel

theorem h21689 : P.leaf 34 21689 = 1645784 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 60), (128, 1676), (64, 0), (256, 0), (64, 39456), (64, 80768), (128, 1523824)]) (.cons c21689_0 (.cons c21689_1 (.cons c21689_2 (.cons c21689_3 (.cons c21689_4 (.cons c21689_5 (.cons c21689_6 (.cons c21689_7 (.nil))))))))) (by decide) (by decide))

theorem cover21691 : P.CoversSplit 24 10 21691 0xfffffffff0f00000fffffffff0f00000f0f0f0f000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000c0ffc0ffc8f8000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 865, 916, 1202, 1210, 1217, 1251, 1259, 1601]) (ps := [(5, [517], [566]), (8, [580], [573]), (14, [867], [860]), (15, [909], [860, 916])]) (by decide +kernel)

theorem c21691_0 : P.sumLeaves 24 22211584 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21691) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover21691 (by decide)
  decide +kernel

theorem contract21691_1 : P.leaf 30 347060 = 120 := by
  exact leaf_contract_factors (k := 30) (b := 8) (H := 347060) (ss := [(14, 0, 867), (12, 1, 486), (8, 0, 874), (20, 1, 482), (21, 0, 488), (5, 1, 524), (18, 1, 879), (7, 1, 628), (6, 1, 460), (11, 1, 818), (10, 1, 811), (29, 15, 909), (13, 1, 971), (30, 1, 1251), (31, 1, 1251), (15, 0, 1259), (2, 1, 411), (23, 1, 803), (16, 1, 872), (17, 0, 1259), (27, 0, 1259), (9, 0, 573)]) (ids := [1, 22, 24, 26, 17, 23, 2, 20]) (cs := [1, 2, 8, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 6, 1, 0, 9, 1, 3, 7, 4, 0, 5, 0, 1, 1]) (bs := [4, 2, 2]) (W := 120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21691_1 : P.sumLeaves 24 22211840 64 = 120 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347060) rows (by decide) (by decide)).symm.trans contract21691_1

theorem contract21691_2 : P.leaf 30 347061 = 2176 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 347061) (ss := [(14, 0, 867), (12, 1, 486), (8, 0, 874), (20, 1, 482), (21, 0, 488), (5, 1, 524), (18, 1, 879), (7, 1, 628), (6, 1, 460), (11, 1, 818), (10, 1, 811), (29, 15, 909), (13, 1, 971), (16, 1, 1314)]) (ids := [0, 1, 2, 7, 13, 15, 17, 20, 21, 22, 24, 25, 26, 28, 29, 23]) (cs := [2, 3, 4, 1, 1, 1, 0, 5, 1, 1, 1, 1, 0, 6, 1, 7, 1, 8, 1, 0, 9, 10, 11, 17, 12, 13, 14, 6, 15, 16]) (bs := [15, 1]) (W := 2176) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21691_2 : P.sumLeaves 24 22211904 64 = 2176 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347061) rows (by decide) (by decide)).symm.trans contract21691_2

theorem c21691_3 : P.sumLeaves 24 22211968 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21691) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover21691 (by decide)
  decide +kernel

theorem contract21691_4 : P.leaf 30 347063 = 0 := by
  exact leaf_contract_zero (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (14, 0, 867), (12, 1, 486), (6, 1, 460), (15, 1, 488), (10, 1, 811), (11, 1, 818), (29, 1, 916)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21691_4 : P.sumLeaves 24 22212032 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347063) rows (by decide) (by decide)).symm.trans contract21691_4

theorem c21691_5 : P.sumLeaves 24 22212096 504 = 4455746 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21691) (lo := 512) (len := 504) (W := 4455746) check rows elimOK (by decide) (by decide) cover21691 (by decide)
  decide +kernel

theorem c21691_6 : P.sumLeaves 24 22212600 8 = 878336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21691) (lo := 1016) (len := 8) (W := 878336) check rows elimOK (by decide) (by decide) cover21691 (by decide)
  decide +kernel

theorem h21691 : P.leaf 34 21691 = 5336378 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 120), (64, 2176), (64, 0), (64, 0), (504, 4455746), (8, 878336)]) (.cons c21691_0 (.cons c21691_1 (.cons c21691_2 (.cons c21691_3 (.cons c21691_4 (.cons c21691_5 (.cons c21691_6 (.nil)))))))) (by decide) (by decide))

theorem cover21692 : P.CoversSplit 24 10 21692 0xf0000000f00a0000f0000000f00a0000f000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21692_0 : P.sumLeaves 24 22212608 1024 = 1158980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21692) (lo := 0) (len := 1024) (W := 1158980) check rows elimOK (by decide) (by decide) cover21692 (by decide)
  decide +kernel

theorem h21692 : P.leaf 34 21692 = 1158980 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1158980)]) (.cons c21692_0 (.nil)) (by decide) (by decide))

theorem cover21693 : P.CoversSplit 24 10 21693 0xfffffffffaf00000fffffffffaf00000f500f50000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 573, 858, 860, 865, 867, 909, 1202, 1210, 1217, 1251, 1601]) (by decide +kernel)

theorem c21693_0 : P.sumLeaves 24 22213632 768 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21693) (lo := 0) (len := 768) (W := 0) check rows elimOK (by decide) (by decide) cover21693 (by decide)
  decide +kernel

theorem contract21693_1 : P.leaf 30 347100 = 103056 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 347100) (ss := [(8, 1, 531), (16, 1, 531), (14, 1, 874), (18, 11, 879), (29, 1, 909), (30, 1, 1251), (31, 1, 1217), (28, 1, 860), (11, 1, 1264), (17, 1, 1266)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 13, 17, 18, 19, 20, 21, 24, 25, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 10, 11, 1, 12, 1, 1, 1, 13, 14, 15, 16, 17, 20, 21, 18, 19, 1, 1, 1, 1]) (bs := [18, 2]) (W := 103056) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21693_1 : P.sumLeaves 24 22214400 64 = 103056 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347100) rows (by decide) (by decide)).symm.trans contract21693_1

theorem c21693_2 : P.sumLeaves 24 22214464 192 = 7681450 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21693) (lo := 832) (len := 192) (W := 7681450) check rows elimOK (by decide) (by decide) cover21693 (by decide)
  decide +kernel

theorem h21693 : P.leaf 34 21693 = 7784506 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 0), (64, 103056), (192, 7681450)]) (.cons c21693_0 (.cons c21693_1 (.cons c21693_2 (.nil)))) (by decide) (by decide))

theorem cover21694 : P.CoversSplit 24 10 21694 0xf0f00000f0f00000f0f00000f0f00000f000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 860, 865, 867, 909, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21694_0 : P.sumLeaves 24 22214656 1024 = 4159348 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21694) (lo := 0) (len := 1024) (W := 4159348) check rows elimOK (by decide) (by decide) cover21694 (by decide)
  decide +kernel

theorem h21694 : P.leaf 34 21694 = 4159348 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4159348)]) (.cons c21694_0 (.nil)) (by decide) (by decide))

theorem cover21695 : P.CoversSplit 24 10 21695 0xfffffffffafa0000fffffffffafa0000f500f50000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 860, 865, 867, 909, 1202, 1210, 1217, 1251, 1601]) (by decide +kernel)

theorem c21695_0 : P.sumLeaves 24 22215680 1014 = 20150934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21695) (lo := 0) (len := 1014) (W := 20150934) check rows elimOK (by decide) (by decide) cover21695 (by decide)
  decide +kernel

theorem c21695_1 : P.sumLeaves 24 22216694 10 = 4031936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21695) (lo := 1014) (len := 10) (W := 4031936) check rows elimOK (by decide) (by decide) cover21695 (by decide)
  decide +kernel

theorem h21695 : P.leaf 34 21695 = 24182870 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1014, 20150934), (10, 4031936)]) (.cons c21695_0 (.cons c21695_1 (.nil))) (by decide) (by decide))

theorem cover21700 : P.CoversSplit 24 10 21700 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c21700_0 : P.sumLeaves 24 22220800 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21700) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21700 (by decide)
  decide +kernel

theorem h21700 : P.leaf 34 21700 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21700_0 (.nil)) (by decide) (by decide))

theorem cover21701 : P.CoversSplit 24 10 21701 0xf0f00000e0e00000f0f00000e0e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 536, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21701_0 : P.sumLeaves 24 22221824 960 = 16991 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21701) (lo := 0) (len := 960) (W := 16991) check rows elimOK (by decide) (by decide) cover21701 (by decide)
  decide +kernel

theorem contract21701_1 : P.leaf 30 347231 = 34680 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 347231) (ss := [(30, 1, 466), (11, 1, 472), (8, 1, 475), (4, 1, 508), (3, 1, 417), (18, 1, 487), (17, 1, 565), (14, 1, 867), (9, 1, 559), (15, 1, 909)]) (ids := [0, 3, 4, 5, 8, 10, 11, 14, 17, 18, 20, 21, 22, 24, 25, 26, 27, 29, 19, 23]) (cs := [2, 1, 1, 3, 4, 5, 1, 1, 6, 1, 7, 8, 1, 1, 9, 1, 1, 10, 11, 20, 12, 13, 14, 21, 15, 16, 17, 18, 1, 19]) (bs := [18, 2]) (W := 34680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21701_1 : P.sumLeaves 24 22222784 64 = 34680 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347231) rows (by decide) (by decide)).symm.trans contract21701_1

theorem h21701 : P.leaf 34 21701 = 51671 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 16991), (64, 34680)]) (.cons c21701_0 (.cons c21701_1 (.nil))) (by decide) (by decide))

theorem cover21702 : P.CoversSplit 24 10 21702 0xa0a00000a0a000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 536, 858, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21702_0 : P.sumLeaves 24 22222848 1024 = 50976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21702) (lo := 0) (len := 1024) (W := 50976) check rows elimOK (by decide) (by decide) cover21702 (by decide)
  decide +kernel

theorem h21702 : P.leaf 34 21702 = 50976 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 50976)]) (.cons c21702_0 (.nil)) (by decide) (by decide))

theorem cover21703 : P.CoversSplit 24 10 21703 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 536, 573, 858, 860, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c21703_0 : P.sumLeaves 24 22223872 768 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21703) (lo := 0) (len := 768) (W := 0) check rows elimOK (by decide) (by decide) cover21703 (by decide)
  decide +kernel

theorem contract21703_1 : P.leaf 30 347260 = 36636 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 347260) (ss := [(30, 1, 466), (7, 1, 523), (18, 1, 524), (8, 1, 565), (14, 1, 867), (11, 1, 879), (15, 1, 909), (31, 1, 1210), (28, 1, 858), (21, 17, 1266), (20, 1, 1272)]) (ids := [0, 1, 2, 3, 4, 7, 8, 10, 11, 14, 15, 17, 20, 21, 23, 24, 25, 27, 22]) (cs := [2, 3, 4, 5, 6, 1, 1, 7, 8, 1, 9, 10, 1, 1, 11, 12, 1, 13, 1, 12, 14, 15, 20, 16, 17, 18, 1, 19, 1, 1]) (bs := [18, 1]) (W := 36636) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21703_1 : P.sumLeaves 24 22224640 64 = 36636 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 347260) rows (by decide) (by decide)).symm.trans contract21703_1

theorem c21703_2 : P.sumLeaves 24 22224704 192 = 1165912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21703) (lo := 832) (len := 192) (W := 1165912) check rows elimOK (by decide) (by decide) cover21703 (by decide)
  decide +kernel

theorem h21703 : P.leaf 34 21703 = 1202548 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 0), (64, 36636), (192, 1165912)]) (.cons c21703_0 (.cons c21703_1 (.cons c21703_2 (.nil)))) (by decide) (by decide))

theorem cover21708 : P.CoversSplit 24 10 21708 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c21708_0 : P.sumLeaves 24 22228992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21708) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21708 (by decide)
  decide +kernel

theorem h21708 : P.leaf 34 21708 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21708_0 (.nil)) (by decide) (by decide))

theorem cover21709 : P.CoversSplit 24 10 21709 0xf0f00000e0e00000f0f00000e0e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(11, [472], [858])]) (by decide +kernel)

theorem c21709_0 : P.sumLeaves 24 22230016 1024 = 271294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21709) (lo := 0) (len := 1024) (W := 271294) check rows elimOK (by decide) (by decide) cover21709 (by decide)
  decide +kernel

theorem h21709 : P.leaf 34 21709 = 271294 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 271294)]) (.cons c21709_0 (.nil)) (by decide) (by decide))

theorem cover21710 : P.CoversSplit 24 10 21710 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 858, 865, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21710_0 : P.sumLeaves 24 22231040 1024 = 297894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21710) (lo := 0) (len := 1024) (W := 297894) check rows elimOK (by decide) (by decide) cover21710 (by decide)
  decide +kernel

theorem h21710 : P.leaf 34 21710 = 297894 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 297894)]) (.cons c21710_0 (.nil)) (by decide) (by decide))

theorem cover21711 : P.CoversSplit 24 10 21711 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 858, 860, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c21711_0 : P.sumLeaves 24 22232064 1024 = 2390268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21711) (lo := 0) (len := 1024) (W := 2390268) check rows elimOK (by decide) (by decide) cover21711 (by decide)
  decide +kernel

theorem h21711 : P.leaf 34 21711 = 2390268 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2390268)]) (.cons c21711_0 (.nil)) (by decide) (by decide))

theorem cover21718 : P.CoversSplit 24 10 21718 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21718_0 : P.sumLeaves 24 22239232 1024 = 655933 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21718) (lo := 0) (len := 1024) (W := 655933) check rows elimOK (by decide) (by decide) cover21718 (by decide)
  decide +kernel

theorem h21718 : P.leaf 34 21718 = 655933 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 655933)]) (.cons c21718_0 (.nil)) (by decide) (by decide))

theorem cover21719 : P.CoversSplit 24 10 21719 0xfffffffff0f00000fffffffff0f00000ffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 867, 916, 1202, 1210, 1217, 1259, 1601]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c21719_0 : P.sumLeaves 24 22240256 1008 = 9832558 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21719) (lo := 0) (len := 1008) (W := 9832558) check rows elimOK (by decide) (by decide) cover21719 (by decide)
  decide +kernel

theorem c21719_1 : P.sumLeaves 24 22241264 16 = 3603628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21719) (lo := 1008) (len := 16) (W := 3603628) check rows elimOK (by decide) (by decide) cover21719 (by decide)
  decide +kernel

theorem h21719 : P.leaf 34 21719 = 13436186 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1008, 9832558), (16, 3603628)]) (.cons c21719_0 (.cons c21719_1 (.nil))) (by decide) (by decide))

theorem cover21724 : P.CoversSplit 24 10 21724 0xa0000000f0000000a0000000f0000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 508, 516, 536, 573, 858, 867, 1202, 1210, 1601]) (by decide +kernel)

theorem c21724_0 : P.sumLeaves 24 22245376 1024 = 901268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21724) (lo := 0) (len := 1024) (W := 901268) check rows elimOK (by decide) (by decide) cover21724 (by decide)
  decide +kernel

theorem h21724 : P.leaf 34 21724 = 901268 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 901268)]) (.cons c21724_0 (.nil)) (by decide) (by decide))

theorem cover21725 : P.CoversSplit 24 10 21725 0xfffffffff0f00000fffffffff0f00000ff00000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 860, 865, 867, 909, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21725_0 : P.sumLeaves 24 22246400 1024 = 7837230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21725) (lo := 0) (len := 1024) (W := 7837230) check rows elimOK (by decide) (by decide) cover21725 (by decide)
  decide +kernel

theorem h21725 : P.leaf 34 21725 = 7837230 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7837230)]) (.cons c21725_0 (.nil)) (by decide) (by decide))

theorem cover21726 : P.CoversSplit 24 10 21726 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21726_0 : P.sumLeaves 24 22247424 1024 = 2739236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21726) (lo := 0) (len := 1024) (W := 2739236) check rows elimOK (by decide) (by decide) cover21726 (by decide)
  decide +kernel

theorem h21726 : P.leaf 34 21726 = 2739236 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2739236)]) (.cons c21726_0 (.nil)) (by decide) (by decide))

theorem cover21727 : P.CoversSplit 24 10 21727 0xfffffffff0f00000fffffffff0f00000ffff00000000a0a0ffff00000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 867, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c21727_0 : P.sumLeaves 24 22248448 1000 = 17342216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21727) (lo := 0) (len := 1000) (W := 17342216) check rows elimOK (by decide) (by decide) cover21727 (by decide)
  decide +kernel

theorem c21727_1 : P.sumLeaves 24 22249448 24 = 9042576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21727) (lo := 1000) (len := 24) (W := 9042576) check rows elimOK (by decide) (by decide) cover21727 (by decide)
  decide +kernel

theorem h21727 : P.leaf 34 21727 = 26384792 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1000, 17342216), (24, 9042576)]) (.cons c21727_0 (.cons c21727_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(21668, 24), (21669, 48), (21670, 48), (21671, 48), (21676, 24), (21677, 24), (21678, 24), (21679, 24), (21685, 48), (21686, 24), (21687, 48), (21689, 24), (21691, 48), (21692, 48), (21693, 48), (21694, 48), (21695, 48), (21700, 16), (21701, 16), (21702, 48), (21703, 48), (21708, 48), (21709, 48), (21710, 48), (21711, 48), (21718, 48), (21719, 48), (21724, 48), (21725, 48), (21726, 48), (21727, 48)]

theorem segOK : checkSeg 16 perms 21668 21734 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21668 21734 1256 5165923712 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5165923712)
    (SegSum.cons (w := 24) h21668 (SegSum.cons (w := 48) h21669 (SegSum.cons (w := 48) h21670 (SegSum.cons (w := 48) h21671 (SegSum.cons (w := 24) h21676 (SegSum.cons (w := 24) h21677 (SegSum.cons (w := 24) h21678 (SegSum.cons (w := 24) h21679 (SegSum.cons (w := 48) h21685 (SegSum.cons (w := 24) h21686 (SegSum.cons (w := 48) h21687 (SegSum.cons (w := 24) h21689 (SegSum.cons (w := 48) h21691 (SegSum.cons (w := 48) h21692 (SegSum.cons (w := 48) h21693 (SegSum.cons (w := 48) h21694 (SegSum.cons (w := 48) h21695 (SegSum.cons (w := 16) h21700 (SegSum.cons (w := 16) h21701 (SegSum.cons (w := 48) h21702 (SegSum.cons (w := 48) h21703 (SegSum.cons (w := 48) h21708 (SegSum.cons (w := 48) h21709 (SegSum.cons (w := 48) h21710 (SegSum.cons (w := 48) h21711 (SegSum.cons (w := 48) h21718 (SegSum.cons (w := 48) h21719 (SegSum.cons (w := 48) h21724 (SegSum.cons (w := 48) h21725 (SegSum.cons (w := 48) h21726 (SegSum.cons (w := 48) h21727 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S68
