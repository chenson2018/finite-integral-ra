/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S70

open RACert RACert.Problem

theorem cover90024 : P.CoversSplit 26 10 90024 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 558, 566, 874, 923, 972, 1272]) (by decide +kernel)

theorem c90024_0 : P.sumLeaves 26 92184576 1024 = 7582166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90024) (lo := 0) (len := 1024) (W := 7582166) check rows elimOK (by decide) (by decide) cover90024 (by decide)
  decide +kernel

theorem h90024 : P.leaf 36 90024 = 7582166 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7582166)]) (.cons c90024_0 (.nil)) (by decide) (by decide))

theorem cover90025 : P.CoversSplit 26 10 90025 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 536, 923, 972, 1272]) (by decide +kernel)

theorem c90025_0 : P.sumLeaves 26 92185600 1024 = 50552484 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90025) (lo := 0) (len := 1024) (W := 50552484) check rows elimOK (by decide) (by decide) cover90025 (by decide)
  decide +kernel

theorem h90025 : P.leaf 36 90025 = 50552484 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 50552484)]) (.cons c90025_0 (.nil)) (by decide) (by decide))

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

theorem c90042_0 : P.sumLeaves 26 92203008 1024 = 37658492 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90042) (lo := 0) (len := 1024) (W := 37658492) check rows elimOK (by decide) (by decide) cover90042 (by decide)
  decide +kernel

theorem h90042 : P.leaf 36 90042 = 37658492 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 37658492)]) (.cons c90042_0 (.nil)) (by decide) (by decide))

theorem cover90043 : P.CoversSplit 26 10 90043 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c90043_0 : P.sumLeaves 26 92204032 1024 = 169648438 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90043) (lo := 0) (len := 1024) (W := 169648438) check rows elimOK (by decide) (by decide) cover90043 (by decide)
  decide +kernel

theorem h90043 : P.leaf 36 90043 = 169648438 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 169648438)]) (.cons c90043_0 (.nil)) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(90024, 72), (90025, 360), (90026, 360), (90027, 720), (90029, 360), (90031, 360), (90036, 720), (90037, 720), (90038, 720), (90039, 720), (90042, 360), (90043, 360), (90044, 720), (90045, 720), (90046, 720)]

theorem segOK : checkSeg 20 perms 90024 90047 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90024 90047 7992 1210947189912 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1210947189912)
    (SegSum.cons (w := 72) h90024 (SegSum.cons (w := 360) h90025 (SegSum.cons (w := 360) h90026 (SegSum.cons (w := 720) h90027 (SegSum.cons (w := 360) h90029 (SegSum.cons (w := 360) h90031 (SegSum.cons (w := 720) h90036 (SegSum.cons (w := 720) h90037 (SegSum.cons (w := 720) h90038 (SegSum.cons (w := 720) h90039 (SegSum.cons (w := 360) h90042 (SegSum.cons (w := 360) h90043 (SegSum.cons (w := 720) h90044 (SegSum.cons (w := 720) h90045 (SegSum.cons (w := 720) h90046 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S70
