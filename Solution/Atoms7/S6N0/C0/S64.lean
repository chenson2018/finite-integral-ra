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

namespace RACert.S6N0.C0.S64

open RACert RACert.Problem

theorem cover90025 : P.CoversSplit 26 10 90025 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 536, 923, 972, 1272]) (by decide +kernel)

noncomputable def f90025 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92185600 + i)

theorem c90025_0 : rowSum f90025 0 1024 = 50552484 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90025) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90025 (by decide)
  decide +kernel

theorem sum90025 : rowSum f90025 0 1024 = 50552484 :=
  c90025_0

theorem h90025 : P.leaf 36 90025 = 50552484 :=
  leaf_weighted (k := 26) (d := 10) (H := 90025) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90025) (by decide) (by decide +kernel)) sum90025

theorem cover90026 : P.CoversSplit 26 10 90026 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1272, 1322, 1658, 1665]) (by decide +kernel)

theorem c90026_0 : P.sumLeaves 26 92186624 1024 = 11111183 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90026) (lo := 0) (len := 1024) (W := 11111183) check rows elimOK (by decide) (by decide) cover90026 (by decide)
  decide +kernel

theorem h90026 : P.leaf 36 90026 = 11111183 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11111183)]) (.cons c90026_0 (.nil)) (by decide) (by decide))

theorem cover90027 : P.CoversSplit 26 10 90027 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1272, 1322, 1658, 1665]) (by decide +kernel)

theorem c90027_0 : P.sumLeaves 26 92187648 1024 = 93269754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90027) (lo := 0) (len := 1024) (W := 93269754) check rows elimOK (by decide) (by decide) cover90027 (by decide)
  decide +kernel

theorem h90027 : P.leaf 36 90027 = 93269754 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 93269754)]) (.cons c90027_0 (.nil)) (by decide) (by decide))

theorem cover90029 : P.CoversSplit 26 10 90029 0xffffffff00000000fffffffa00000000ffffffff00000000fafafafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [536, 922, 923, 972, 1272, 1658]) (by decide +kernel)

theorem c90029_0 : P.sumLeaves 26 92189696 1002 = 121363814 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90029) (lo := 0) (len := 1002) (W := 121363814) check rows elimOK (by decide) (by decide) cover90029 (by decide)
  decide +kernel

theorem c90029_1 : P.sumLeaves 26 92190698 22 = 62065100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90029) (lo := 1002) (len := 22) (W := 62065100) check rows elimOK (by decide) (by decide) cover90029 (by decide)
  decide +kernel

theorem h90029 : P.leaf 36 90029 = 183428914 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 121363814), (22, 62065100)]) (.cons c90029_0 (.cons c90029_1 (.nil))) (by decide) (by decide))

theorem cover90031 : P.CoversSplit 26 10 90031 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1272, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90031_0 : P.sumLeaves 26 92191744 954 = 167805964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90031) (lo := 0) (len := 954) (W := 167805964) check rows elimOK (by decide) (by decide) cover90031 (by decide)
  decide +kernel

theorem c90031_1 : P.sumLeaves 26 92192698 70 = 138112438 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90031) (lo := 954) (len := 70) (W := 138112438) check rows elimOK (by decide) (by decide) cover90031 (by decide)
  decide +kernel

theorem h90031 : P.leaf 36 90031 = 305918402 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(954, 167805964), (70, 138112438)]) (.cons c90031_0 (.cons c90031_1 (.nil))) (by decide) (by decide))

theorem cover90036 : P.CoversSplit 26 10 90036 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 874, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c90036_0 : P.sumLeaves 26 92196864 1024 = 9365408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90036) (lo := 0) (len := 1024) (W := 9365408) check rows elimOK (by decide) (by decide) cover90036 (by decide)
  decide +kernel

theorem h90036 : P.leaf 36 90036 = 9365408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9365408)]) (.cons c90036_0 (.nil)) (by decide) (by decide))

theorem cover90037 : P.CoversSplit 26 10 90037 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c90037_0 : P.sumLeaves 26 92197888 1024 = 82993914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90037) (lo := 0) (len := 1024) (W := 82993914) check rows elimOK (by decide) (by decide) cover90037 (by decide)
  decide +kernel

theorem h90037 : P.leaf 36 90037 = 82993914 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 82993914)]) (.cons c90037_0 (.nil)) (by decide) (by decide))

theorem cover90038 : P.CoversSplit 26 10 90038 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 874, 922, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c90038_0 : P.sumLeaves 26 92198912 1024 = 35363640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90038) (lo := 0) (len := 1024) (W := 35363640) check rows elimOK (by decide) (by decide) cover90038 (by decide)
  decide +kernel

theorem h90038 : P.leaf 36 90038 = 35363640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 35363640)]) (.cons c90038_0 (.nil)) (by decide) (by decide))

theorem cover90039 : P.CoversSplit 26 10 90039 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c90039_0 : P.sumLeaves 26 92199936 1024 = 137029062 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90039) (lo := 0) (len := 1024) (W := 137029062) check rows elimOK (by decide) (by decide) cover90039 (by decide)
  decide +kernel

theorem h90039 : P.leaf 36 90039 = 137029062 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 137029062)]) (.cons c90039_0 (.nil)) (by decide) (by decide))

theorem cover90042 : P.CoversSplit 26 10 90042 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90042 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92203008 + i)

theorem c90042_0 : rowSum f90042 0 1024 = 37658492 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90042) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90042 (by decide)
  decide +kernel

theorem sum90042 : rowSum f90042 0 1024 = 37658492 :=
  c90042_0

theorem h90042 : P.leaf 36 90042 = 37658492 :=
  leaf_weighted (k := 26) (d := 10) (H := 90042) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90042) (by decide) (by decide +kernel)) sum90042

theorem cover90043 : P.CoversSplit 26 10 90043 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90043 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92204032 + i)

theorem c90043_0 : rowSum f90043 0 1024 = 169648438 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90043) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90043 (by decide)
  decide +kernel

theorem sum90043 : rowSum f90043 0 1024 = 169648438 :=
  c90043_0

theorem h90043 : P.leaf 36 90043 = 169648438 :=
  leaf_weighted (k := 26) (d := 10) (H := 90043) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90043) (by decide) (by decide +kernel)) sum90043

theorem cover90044 : P.CoversSplit 26 10 90044 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90044_0 : P.sumLeaves 26 92205056 809 = 39637682 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90044) (lo := 0) (len := 809) (W := 39637682) check rows elimOK (by decide) (by decide) cover90044 (by decide)
  decide +kernel

theorem c90044_1 : P.sumLeaves 26 92205865 197 = 84731264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90044) (lo := 809) (len := 197) (W := 84731264) check rows elimOK (by decide) (by decide) cover90044 (by decide)
  decide +kernel

theorem c90044_2 : P.sumLeaves 26 92206062 18 = 36415060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90044) (lo := 1006) (len := 18) (W := 36415060) check rows elimOK (by decide) (by decide) cover90044 (by decide)
  decide +kernel

theorem h90044 : P.leaf 36 90044 = 160784006 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(809, 39637682), (197, 84731264), (18, 36415060)]) (.cons c90044_0 (.cons c90044_1 (.cons c90044_2 (.nil)))) (by decide) (by decide))

theorem cover90045 : P.CoversSplit 26 10 90045 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90045_0 : P.sumLeaves 26 92206080 809 = 114128540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90045) (lo := 0) (len := 809) (W := 114128540) check rows elimOK (by decide) (by decide) cover90045 (by decide)
  decide +kernel

theorem c90045_1 : P.sumLeaves 26 92206889 197 = 262232190 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90045) (lo := 809) (len := 197) (W := 262232190) check rows elimOK (by decide) (by decide) cover90045 (by decide)
  decide +kernel

theorem c90045_2 : P.sumLeaves 26 92207086 18 = 100568210 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90045) (lo := 1006) (len := 18) (W := 100568210) check rows elimOK (by decide) (by decide) cover90045 (by decide)
  decide +kernel

theorem h90045 : P.leaf 36 90045 = 476928940 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(809, 114128540), (197, 262232190), (18, 100568210)]) (.cons c90045_0 (.cons c90045_1 (.cons c90045_2 (.nil)))) (by decide) (by decide))

theorem cover90046 : P.CoversSplit 26 10 90046 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90046_0 : P.sumLeaves 26 92207104 760 = 71947974 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90046) (lo := 0) (len := 760) (W := 71947974) check rows elimOK (by decide) (by decide) cover90046 (by decide)
  decide +kernel

theorem c90046_1 : P.sumLeaves 26 92207864 232 = 148129202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90046) (lo := 760) (len := 232) (W := 148129202) check rows elimOK (by decide) (by decide) cover90046 (by decide)
  decide +kernel

theorem c90046_2 : P.sumLeaves 26 92208096 32 = 86142024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90046) (lo := 992) (len := 32) (W := 86142024) check rows elimOK (by decide) (by decide) cover90046 (by decide)
  decide +kernel

theorem h90046 : P.leaf 36 90046 = 306219200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 71947974), (232, 148129202), (32, 86142024)]) (.cons c90046_0 (.cons c90046_1 (.cons c90046_2 (.nil)))) (by decide) (by decide))

theorem cover90047 : P.CoversSplit 26 10 90047 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000330030000000000032003000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem contract90047_0 : P.leaf 32 1440752 = 38976 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1440752) (ss := [(22, 1, 433), (2, 1, 488), (3, 1, 531), (4, 1, 586), (7, 1, 825), (8, 1, 1217), (18, 1, 1266), (29, 0, 1322), (31, 0, 1322), (33, 1, 538), (6, 1, 636), (16, 1, 1273), (17, 0, 1322), (9, 1, 1609)]) (ids := [3, 8, 9, 10, 11, 12, 13, 17, 18, 19, 21, 23, 24, 25, 26, 28, 30, 22]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 1, 0, 1, 9, 10, 11, 1, 12, 19, 13, 14, 15, 16, 0, 17, 0, 18, 1]) (bs := [17, 1]) (W := 38976) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c90047_0 : P.sumLeaves 26 92208128 64 = 38976 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1440752) rows (by decide) (by decide)).symm.trans contract90047_0

theorem contract90047_1 : P.leaf 32 1440753 = 50400 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1440753) (ss := [(22, 1, 433), (2, 1, 488), (3, 1, 531), (4, 1, 580), (5, 1, 629), (7, 1, 825), (8, 1, 1217), (18, 1, 1266), (29, 0, 1322), (31, 0, 1322), (33, 1, 538), (6, 1, 636), (16, 1, 1273), (17, 0, 1322), (9, 1, 1609)]) (ids := [8, 11, 21, 9, 13, 17, 19, 24, 26, 28, 30, 12, 25, 10, 18, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 15, 3, 13, 6, 1, 0, 1, 7, 16, 8, 1, 4, 17, 18, 9, 14, 10, 0, 11, 0, 12, 1]) (bs := [3, 8, 2, 4]) (W := 50400) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c90047_1 : P.sumLeaves 26 92208192 64 = 50400 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1440753) rows (by decide) (by decide)).symm.trans contract90047_1

theorem c90047_2 : P.sumLeaves 26 92208256 632 = 163001444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90047) (lo := 128) (len := 632) (W := 163001444) check rows elimOK (by decide) (by decide) cover90047 (by decide)
  decide +kernel

theorem c90047_3 : P.sumLeaves 26 92208888 232 = 385229760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90047) (lo := 760) (len := 232) (W := 385229760) check rows elimOK (by decide) (by decide) cover90047 (by decide)
  decide +kernel

theorem c90047_4 : P.sumLeaves 26 92209120 32 = 212331060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90047) (lo := 992) (len := 32) (W := 212331060) check rows elimOK (by decide) (by decide) cover90047 (by decide)
  decide +kernel

theorem h90047 : P.leaf 36 90047 = 760651640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 38976), (64, 50400), (632, 163001444), (232, 385229760), (32, 212331060)]) (.cons c90047_0 (.cons c90047_1 (.cons c90047_2 (.cons c90047_3 (.cons c90047_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90025, 360), (90026, 360), (90027, 720), (90029, 360), (90031, 360), (90036, 720), (90037, 720), (90038, 720), (90039, 720), (90042, 360), (90043, 360), (90044, 720), (90045, 720), (90046, 720), (90047, 720)]

theorem segOK : checkSeg 20 perms 90025 90052 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90025 90052 8640 1758070454760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1758070454760)
    (SegSum.cons (w := 360) h90025 (SegSum.cons (w := 360) h90026 (SegSum.cons (w := 720) h90027 (SegSum.cons (w := 360) h90029 (SegSum.cons (w := 360) h90031 (SegSum.cons (w := 720) h90036 (SegSum.cons (w := 720) h90037 (SegSum.cons (w := 720) h90038 (SegSum.cons (w := 720) h90039 (SegSum.cons (w := 360) h90042 (SegSum.cons (w := 360) h90043 (SegSum.cons (w := 720) h90044 (SegSum.cons (w := 720) h90045 (SegSum.cons (w := 720) h90046 (SegSum.cons (w := 720) h90047 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S64
