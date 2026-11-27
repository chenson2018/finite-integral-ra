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

namespace RACert.S6N0.C0.S82

open RACert RACert.Problem

theorem cover120807 : P.CoversSplit 26 10 120807 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120807 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123706368 + i)

theorem c120807_0 : rowSum f120807 0 250 = 86167025 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_1 : rowSum f120807 250 190 = 240285673 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_2 : rowSum f120807 440 192 = 286228741 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_3 : rowSum f120807 632 228 = 329079597 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem c120807_4 : rowSum f120807 860 164 = 429055518 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120807) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120807 (by decide)
  decide +kernel

theorem sum120807 : rowSum f120807 0 1024 = 1370816554 :=
  rowSum_append (F := f120807) (lo := 0) (n := 250) (m := 774) (A := 86167025) (B := 1284649529) c120807_0 (rowSum_append (F := f120807) (lo := 250) (n := 190) (m := 584) (A := 240285673) (B := 1044363856) c120807_1 (rowSum_append (F := f120807) (lo := 440) (n := 192) (m := 392) (A := 286228741) (B := 758135115) c120807_2 (rowSum_append (F := f120807) (lo := 632) (n := 228) (m := 164) (A := 329079597) (B := 429055518) c120807_3 (c120807_4))))

theorem h120807 : P.leaf 36 120807 = 1370816554 :=
  leaf_weighted (k := 26) (d := 10) (H := 120807) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120807) (by decide) (by decide +kernel)) sum120807

theorem cover120811 : P.CoversSplit 26 10 120811 0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000505000005050f0f00000f0f000000000505000004040f0f00000f0f000000000000000000000f0f00000c00000000000000000000000f0f00000f0f000000000505000005050f0f00000c00000000000505000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 922, 1273, 1322]) (by decide +kernel)

noncomputable def f120811 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123710464 + i)

theorem c120811_0 : rowSum f120811 0 1013 = 383671360 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120811) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120811 (by decide)
  decide +kernel

theorem c120811_1 : rowSum f120811 1013 11 = 76016808 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120811) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120811 (by decide)
  decide +kernel

theorem sum120811 : rowSum f120811 0 1024 = 459688168 :=
  rowSum_append (F := f120811) (lo := 0) (n := 1013) (m := 11) (A := 383671360) (B := 76016808) c120811_0 (c120811_1)

theorem h120811 : P.leaf 36 120811 = 459688168 :=
  leaf_weighted (k := 26) (d := 10) (H := 120811) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120811) (by decide) (by decide +kernel)) sum120811

theorem cover120812 : P.CoversSplit 26 10 120812 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaf0f0fafaf0f0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120812 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123711488 + i)

theorem c120812_0 : rowSum f120812 0 283 = 20856546 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120812) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_1 : rowSum f120812 283 214 = 45292301 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120812) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_2 : rowSum f120812 497 190 = 83682162 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120812) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_3 : rowSum f120812 687 192 = 135037829 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120812) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem c120812_4 : rowSum f120812 879 145 = 200567440 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120812) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120812 (by decide)
  decide +kernel

theorem sum120812 : rowSum f120812 0 1024 = 485436278 :=
  rowSum_append (F := f120812) (lo := 0) (n := 283) (m := 741) (A := 20856546) (B := 464579732) c120812_0 (rowSum_append (F := f120812) (lo := 283) (n := 214) (m := 527) (A := 45292301) (B := 419287431) c120812_1 (rowSum_append (F := f120812) (lo := 497) (n := 190) (m := 337) (A := 83682162) (B := 335605269) c120812_2 (rowSum_append (F := f120812) (lo := 687) (n := 192) (m := 145) (A := 135037829) (B := 200567440) c120812_3 (c120812_4))))

theorem h120812 : P.leaf 36 120812 = 485436278 :=
  leaf_weighted (k := 26) (d := 10) (H := 120812) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120812) (by decide) (by decide +kernel)) sum120812

theorem cover120813 : P.CoversSplit 26 10 120813 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaf0f0fafaf0f0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120813_0 : P.sumLeaves 26 123712512 188 = 50005934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 0) (len := 188) (W := 50005934) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_1 : P.sumLeaves 26 123712700 163 = 69597616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 188) (len := 163) (W := 69597616) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_2 : P.sumLeaves 26 123712863 102 = 85918452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 351) (len := 102) (W := 85918452) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_3 : P.sumLeaves 26 123712965 142 = 135053323 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 453) (len := 142) (W := 135053323) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_4 : P.sumLeaves 26 123713107 128 = 148668036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 595) (len := 128) (W := 148668036) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_5 : P.sumLeaves 26 123713235 138 = 223710009 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 723) (len := 138) (W := 223710009) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_6 : P.sumLeaves 26 123713373 102 = 200101850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 861) (len := 102) (W := 200101850) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem c120813_7 : P.sumLeaves 26 123713475 61 = 249641065 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120813) (lo := 963) (len := 61) (W := 249641065) check rows elimOK (by decide) (by decide) cover120813 (by decide)
  decide +kernel

theorem h120813 : P.leaf 36 120813 = 1162696285 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(188, 50005934), (163, 69597616), (102, 85918452), (142, 135053323), (128, 148668036), (138, 223710009), (102, 200101850), (61, 249641065)]) (.cons c120813_0 (.cons c120813_1 (.cons c120813_2 (.cons c120813_3 (.cons c120813_4 (.cons c120813_5 (.cons c120813_6 (.cons c120813_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120807, 360), (120811, 360), (120812, 180), (120813, 720)]

theorem segOK : checkSeg 20 perms 120807 120815 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120807 120815 1620 1583501555160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1583501555160)
    (SegSum.cons (w := 360) h120807 (SegSum.cons (w := 360) h120811 (SegSum.cons (w := 180) h120812 (SegSum.cons (w := 720) h120813 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S82
