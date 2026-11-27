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

namespace RACert.S6N0.C0.S83

open RACert RACert.Problem

theorem cover120815 : P.CoversSplit 26 10 120815 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120815 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123714560 + i)

theorem c120815_0 : rowSum f120815 0 250 = 324428969 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120815) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_1 : rowSum f120815 250 190 = 452982067 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120815) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_2 : rowSum f120815 440 192 = 605491655 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120815) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_3 : rowSum f120815 632 228 = 645841851 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120815) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem c120815_4 : rowSum f120815 860 164 = 743350849 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120815) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120815 (by decide)
  decide +kernel

theorem sum120815 : rowSum f120815 0 1024 = 2772095391 :=
  rowSum_append (F := f120815) (lo := 0) (n := 250) (m := 774) (A := 324428969) (B := 2447666422) c120815_0 (rowSum_append (F := f120815) (lo := 250) (n := 190) (m := 584) (A := 452982067) (B := 1994684355) c120815_1 (rowSum_append (F := f120815) (lo := 440) (n := 192) (m := 392) (A := 605491655) (B := 1389192700) c120815_2 (rowSum_append (F := f120815) (lo := 632) (n := 228) (m := 164) (A := 645841851) (B := 743350849) c120815_3 (c120815_4))))

theorem h120815 : P.leaf 36 120815 = 2772095391 :=
  leaf_weighted (k := 26) (d := 10) (H := 120815) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120815) (by decide) (by decide +kernel)) sum120815

theorem cover120819 : P.CoversSplit 26 10 120819 0xf0f00000f0f000000000000000000000f0f00000f0c000000000000000000000f0f00000f0f000000000505000005050f0f00000f0c000000000505000004040f0f00000f0f000000000000000000000f0f00000c0c000000000000000000000f0f00000f0f000000000505000005050f0f00000c0c000000000505000004040 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 873, 922, 1322]) (by decide +kernel)

noncomputable def f120819 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123718656 + i)

theorem c120819_0 : rowSum f120819 0 1012 = 167365116 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120819) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120819 (by decide)
  decide +kernel

theorem c120819_1 : rowSum f120819 1012 12 = 32247264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120819) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120819 (by decide)
  decide +kernel

theorem sum120819 : rowSum f120819 0 1024 = 199612380 :=
  rowSum_append (F := f120819) (lo := 0) (n := 1012) (m := 12) (A := 167365116) (B := 32247264) c120819_0 (c120819_1)

theorem h120819 : P.leaf 36 120819 = 199612380 :=
  leaf_weighted (k := 26) (d := 10) (H := 120819) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120819) (by decide) (by decide +kernel)) sum120819

theorem cover120820 : P.CoversSplit 26 10 120820 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0ffccffccffccfac8ffccffccffccfac8ffccffccccccc8c8fac8fac8c8c8c8c8ffccfac8ffccfac8fac8f0c0fac8f0c0ffccfac8ccccc8c8fac8f0c0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120820 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123719680 + i)

theorem c120820_0 : rowSum f120820 0 297 = 10231424 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120820) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_1 : rowSum f120820 297 254 = 54888976 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120820) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_2 : rowSum f120820 551 216 = 47108688 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120820) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_3 : rowSum f120820 767 172 = 45526960 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120820) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem c120820_4 : rowSum f120820 939 85 = 34040422 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120820) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120820 (by decide)
  decide +kernel

theorem sum120820 : rowSum f120820 0 1024 = 191796470 :=
  rowSum_append (F := f120820) (lo := 0) (n := 297) (m := 727) (A := 10231424) (B := 181565046) c120820_0 (rowSum_append (F := f120820) (lo := 297) (n := 254) (m := 473) (A := 54888976) (B := 126676070) c120820_1 (rowSum_append (F := f120820) (lo := 551) (n := 216) (m := 257) (A := 47108688) (B := 79567382) c120820_2 (rowSum_append (F := f120820) (lo := 767) (n := 172) (m := 85) (A := 45526960) (B := 34040422) c120820_3 (c120820_4))))

theorem h120820 : P.leaf 36 120820 = 191796470 :=
  leaf_weighted (k := 26) (d := 10) (H := 120820) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120820) (by decide) (by decide +kernel)) sum120820

theorem cover120821 : P.CoversSplit 26 10 120821 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0ffffffffffccfac8ffffffffffccfac8ffffffffccccc8c8fafafafac8c8c8c8fffffafaffccfac8fafaf0f0fac8f0c0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120821_0 : P.sumLeaves 26 123720704 179 = 27141249 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 0) (len := 179) (W := 27141249) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_1 : P.sumLeaves 26 123720883 144 = 55486171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 179) (len := 144) (W := 55486171) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_2 : P.sumLeaves 26 123721027 122 = 118366768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 323) (len := 122) (W := 118366768) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_3 : P.sumLeaves 26 123721149 151 = 160922617 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 445) (len := 151) (W := 160922617) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_4 : P.sumLeaves 26 123721300 128 = 167542045 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 596) (len := 128) (W := 167542045) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_5 : P.sumLeaves 26 123721428 138 = 220635506 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 724) (len := 138) (W := 220635506) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_6 : P.sumLeaves 26 123721566 102 = 233944689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 862) (len := 102) (W := 233944689) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem c120821_7 : P.sumLeaves 26 123721668 60 = 234305566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120821) (lo := 964) (len := 60) (W := 234305566) check rows elimOK (by decide) (by decide) cover120821 (by decide)
  decide +kernel

theorem h120821 : P.leaf 36 120821 = 1218344611 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(179, 27141249), (144, 55486171), (122, 118366768), (151, 160922617), (128, 167542045), (138, 220635506), (102, 233944689), (60, 234305566)]) (.cons c120821_0 (.cons c120821_1 (.cons c120821_2 (.cons c120821_3 (.cons c120821_4 (.cons c120821_5 (.cons c120821_6 (.cons c120821_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120815, 360), (120819, 360), (120820, 360), (120821, 720)]

theorem segOK : checkSeg 20 perms 120815 120823 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120815 120823 1800 2016069646680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2016069646680)
    (SegSum.cons (w := 360) h120815 (SegSum.cons (w := 360) h120819 (SegSum.cons (w := 360) h120820 (SegSum.cons (w := 720) h120821 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S83
