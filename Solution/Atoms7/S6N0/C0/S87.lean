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

namespace RACert.S6N0.C0.S87

open RACert RACert.Problem

theorem cover122841 : P.CoversSplit 26 10 122841 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaf0f0fafaf0f0fffffafafffffa00fafaf0f0c8c8c000fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaf0f0fafaf0f0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122841_0 : P.sumLeaves 26 125789184 188 = 26665912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 0) (len := 188) (W := 26665912) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_1 : P.sumLeaves 26 125789372 163 = 40622880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 188) (len := 163) (W := 40622880) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_2 : P.sumLeaves 26 125789535 102 = 98013012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 351) (len := 102) (W := 98013012) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_3 : P.sumLeaves 26 125789637 144 = 135856634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 453) (len := 144) (W := 135856634) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_4 : P.sumLeaves 26 125789781 128 = 150004569 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 597) (len := 128) (W := 150004569) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_5 : P.sumLeaves 26 125789909 141 = 206189414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 725) (len := 141) (W := 206189414) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_6 : P.sumLeaves 26 125790050 103 = 210262162 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 866) (len := 103) (W := 210262162) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem c122841_7 : P.sumLeaves 26 125790153 55 = 233275952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122841) (lo := 969) (len := 55) (W := 233275952) check rows elimOK (by decide) (by decide) cover122841 (by decide)
  decide +kernel

theorem h122841 : P.leaf 36 122841 = 1100890535 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(188, 26665912), (163, 40622880), (102, 98013012), (144, 135856634), (128, 150004569), (141, 206189414), (103, 210262162), (55, 233275952)]) (.cons c122841_0 (.cons c122841_1 (.cons c122841_2 (.cons c122841_3 (.cons c122841_4 (.cons c122841_5 (.cons c122841_6 (.cons c122841_7 (.nil))))))))) (by decide) (by decide))

theorem cover122843 : P.CoversSplit 26 10 122843 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafafffffa00fafafafac8c8c800fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122843 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125791232 + i)

theorem c122843_0 : rowSum f122843 0 292 = 220481980 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122843) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_1 : rowSum f122843 292 242 = 485228236 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122843) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_2 : rowSum f122843 534 245 = 659173415 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122843) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_3 : rowSum f122843 779 177 = 611949889 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122843) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_4 : rowSum f122843 956 68 = 233708634 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122843) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem sum122843 : rowSum f122843 0 1024 = 2210542154 :=
  rowSum_append (F := f122843) (lo := 0) (n := 292) (m := 732) (A := 220481980) (B := 1990060174) c122843_0 (rowSum_append (F := f122843) (lo := 292) (n := 242) (m := 490) (A := 485228236) (B := 1504831938) c122843_1 (rowSum_append (F := f122843) (lo := 534) (n := 245) (m := 245) (A := 659173415) (B := 845658523) c122843_2 (rowSum_append (F := f122843) (lo := 779) (n := 177) (m := 68) (A := 611949889) (B := 233708634) c122843_3 (c122843_4))))

theorem h122843 : P.leaf 36 122843 = 2210542154 :=
  leaf_weighted (k := 26) (d := 10) (H := 122843) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 122843) (by decide) (by decide +kernel)) sum122843

theorem cover122844 : P.CoversSplit 26 10 122844 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaa0a0fafaa0a0fffffafafffffa00fafaa0a0c8c88000fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaa0a0fafaa0a0fffffafacc00c800fafaa0a0c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122844 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125792256 + i)

theorem c122844_0 : rowSum f122844 0 309 = 47821408 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_1 : rowSum f122844 309 258 = 182546393 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_2 : rowSum f122844 567 258 = 352690674 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_3 : rowSum f122844 825 199 = 473492624 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem sum122844 : rowSum f122844 0 1024 = 1056551099 :=
  rowSum_append (F := f122844) (lo := 0) (n := 309) (m := 715) (A := 47821408) (B := 1008729691) c122844_0 (rowSum_append (F := f122844) (lo := 309) (n := 258) (m := 457) (A := 182546393) (B := 826183298) c122844_1 (rowSum_append (F := f122844) (lo := 567) (n := 258) (m := 199) (A := 352690674) (B := 473492624) c122844_2 (c122844_3)))

theorem h122844 : P.leaf 36 122844 = 1056551099 :=
  leaf_weighted (k := 26) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 122844) (by decide) (by decide +kernel)) sum122844

def seg : List (ℕ × ℕ) := [(122841, 360), (122843, 360), (122844, 360)]

theorem segOK : checkSeg 20 perms 122841 122845 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122841 122845 1080 1572474163680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1572474163680)
    (SegSum.cons (w := 360) h122841 (SegSum.cons (w := 360) h122843 (SegSum.cons (w := 360) h122844 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S87
