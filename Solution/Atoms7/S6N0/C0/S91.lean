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

namespace RACert.S6N0.C0.S91

open RACert RACert.Problem

theorem cover120807 : P.CoversSplit 26 10 120807 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120807_0 : P.sumLeaves 26 123706368 171 = 44355102 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 0) (len := 171) (W := 44355102) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_1 : P.sumLeaves 26 123706539 140 = 71740345 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 171) (len := 140) (W := 71740345) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_2 : P.sumLeaves 26 123706679 127 = 137032903 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 311) (len := 127) (W := 137032903) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_3 : P.sumLeaves 26 123706806 126 = 214459353 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 438) (len := 126) (W := 214459353) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_4 : P.sumLeaves 26 123706932 125 = 149406360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 564) (len := 125) (W := 149406360) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_5 : P.sumLeaves 26 123707057 133 = 228929509 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 689) (len := 133) (W := 228929509) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_6 : P.sumLeaves 26 123707190 112 = 211739632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 822) (len := 112) (W := 211739632) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_7 : P.sumLeaves 26 123707302 90 = 313153350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120807) (lo := 934) (len := 90) (W := 313153350) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem h120807 : P.leaf 36 120807 = 1370816554 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 44355102), (140, 71740345), (127, 137032903), (126, 214459353), (125, 149406360), (133, 228929509), (112, 211739632), (90, 313153350)]) (.cons c120807_0 (.cons c120807_1 (.cons c120807_2 (.cons c120807_3 (.cons c120807_4 (.cons c120807_5 (.cons c120807_6 (.cons c120807_7 (.nil))))))))) (by decide) (by decide))

theorem cover120811 : P.CoversSplit 26 10 120811 0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000505000005050f0f00000f0f000000000505000004040f0f00000f0f000000000000000000000f0f00000c00000000000000000000000f0f00000f0f000000000505000005050f0f00000c00000000000505000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 922, 1273, 1322]) (by decide +kernel)

theorem c120811_0 : P.sumLeaves 26 123710464 725 = 167306438 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120811) (lo := 0) (len := 725) (W := 167306438) check rows elimOK (by decide) (by decide) cover120811 (by decide)
  decide +kernel

theorem c120811_1 : P.sumLeaves 26 123711189 299 = 292381730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120811) (lo := 725) (len := 299) (W := 292381730) check rows elimOK (by decide) (by decide) cover120811 (by decide)
  decide +kernel

theorem h120811 : P.leaf 36 120811 = 459688168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(725, 167306438), (299, 292381730)]) (.cons c120811_0 (.cons c120811_1 (.nil))) (by decide) (by decide))

theorem cover120812 : P.CoversSplit 26 10 120812 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaf0f0fafaf0f0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120812_0 : P.sumLeaves 26 123711488 188 = 11461396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 0) (len := 188) (W := 11461396) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_1 : P.sumLeaves 26 123711676 163 = 15961506 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 188) (len := 163) (W := 15961506) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_2 : P.sumLeaves 26 123711839 102 = 24208607 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 351) (len := 102) (W := 24208607) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_3 : P.sumLeaves 26 123711941 142 = 43471889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 453) (len := 142) (W := 43471889) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_4 : P.sumLeaves 26 123712083 128 = 54443417 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 595) (len := 128) (W := 54443417) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_5 : P.sumLeaves 26 123712211 138 = 103237003 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 723) (len := 138) (W := 103237003) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_6 : P.sumLeaves 26 123712349 102 = 87874850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 861) (len := 102) (W := 87874850) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_7 : P.sumLeaves 26 123712451 61 = 144777610 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120812) (lo := 963) (len := 61) (W := 144777610) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem h120812 : P.leaf 36 120812 = 485436278 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(188, 11461396), (163, 15961506), (102, 24208607), (142, 43471889), (128, 54443417), (138, 103237003), (102, 87874850), (61, 144777610)]) (.cons c120812_0 (.cons c120812_1 (.cons c120812_2 (.cons c120812_3 (.cons c120812_4 (.cons c120812_5 (.cons c120812_6 (.cons c120812_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120807, 360), (120811, 360), (120812, 180)]

theorem segOK : checkSeg 20 perms 120807 120813 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120807 120813 900 746360229960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 746360229960)
    (SegSum.cons (w := 360) h120807 (SegSum.cons (w := 360) h120811 (SegSum.cons (w := 180) h120812 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S91
