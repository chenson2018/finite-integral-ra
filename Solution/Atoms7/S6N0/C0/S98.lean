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

namespace RACert.S6N0.C0.S98

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

theorem c122843_0 : P.sumLeaves 26 125791232 171 = 92796542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 0) (len := 171) (W := 92796542) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_1 : P.sumLeaves 26 125791403 140 = 137281922 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 171) (len := 140) (W := 137281922) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_2 : P.sumLeaves 26 125791543 127 = 192021021 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 311) (len := 127) (W := 192021021) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_3 : P.sumLeaves 26 125791670 129 = 316689991 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 438) (len := 129) (W := 316689991) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_4 : P.sumLeaves 26 125791799 126 = 243615532 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 567) (len := 126) (W := 243615532) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_5 : P.sumLeaves 26 125791925 137 = 452975669 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 693) (len := 137) (W := 452975669) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_6 : P.sumLeaves 26 125792062 110 = 264890132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 830) (len := 110) (W := 264890132) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem c122843_7 : P.sumLeaves 26 125792172 84 = 510271345 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122843) (lo := 940) (len := 84) (W := 510271345) check rows elimOK (by decide) (by decide) cover122843 (by decide)
  decide +kernel

theorem h122843 : P.leaf 36 122843 = 2210542154 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 92796542), (140, 137281922), (127, 192021021), (129, 316689991), (126, 243615532), (137, 452975669), (110, 264890132), (84, 510271345)]) (.cons c122843_0 (.cons c122843_1 (.cons c122843_2 (.cons c122843_3 (.cons c122843_4 (.cons c122843_5 (.cons c122843_6 (.cons c122843_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122841, 360), (122843, 360)]

theorem segOK : checkSeg 20 perms 122841 122844 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122841 122844 720 1192115768040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1192115768040)
    (SegSum.cons (w := 360) h122841 (SegSum.cons (w := 360) h122843 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S98
