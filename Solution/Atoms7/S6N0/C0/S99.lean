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

namespace RACert.S6N0.C0.S99

open RACert RACert.Problem

theorem cover122844 : P.CoversSplit 26 10 122844 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaa0a0fafaa0a0fffffafafffffa00fafaa0a0c8c88000fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaa0a0fafaa0a0fffffafacc00c800fafaa0a0c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122844_0 : P.sumLeaves 26 125792256 205 = 21053760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 0) (len := 205) (W := 21053760) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_1 : P.sumLeaves 26 125792461 159 = 37774760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 205) (len := 159) (W := 37774760) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_2 : P.sumLeaves 26 125792620 104 = 71518884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 364) (len := 104) (W := 71518884) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_3 : P.sumLeaves 26 125792724 151 = 123624816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 468) (len := 151) (W := 123624816) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_4 : P.sumLeaves 26 125792875 136 = 193094257 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 619) (len := 136) (W := 193094257) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_5 : P.sumLeaves 26 125793011 137 = 203384511 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 755) (len := 137) (W := 203384511) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_6 : P.sumLeaves 26 125793148 104 = 209372405 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 892) (len := 104) (W := 209372405) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_7 : P.sumLeaves 26 125793252 28 = 196727706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122844) (lo := 996) (len := 28) (W := 196727706) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem h122844 : P.leaf 36 122844 = 1056551099 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(205, 21053760), (159, 37774760), (104, 71518884), (151, 123624816), (136, 193094257), (137, 203384511), (104, 209372405), (28, 196727706)]) (.cons c122844_0 (.cons c122844_1 (.cons c122844_2 (.cons c122844_3 (.cons c122844_4 (.cons c122844_5 (.cons c122844_6 (.cons c122844_7 (.nil))))))))) (by decide) (by decide))

theorem cover122845 : P.CoversSplit 26 10 122845 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaf0f0fafaf0f0fffffafafffffa00fafaf0f0c8c8c000fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaf0f0fafaf0f0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122845_0 : P.sumLeaves 26 125793280 188 = 108898934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 0) (len := 188) (W := 108898934) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_1 : P.sumLeaves 26 125793468 163 = 148667960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 188) (len := 163) (W := 148667960) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_2 : P.sumLeaves 26 125793631 102 = 239438998 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 351) (len := 102) (W := 239438998) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_3 : P.sumLeaves 26 125793733 144 = 317779264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 453) (len := 144) (W := 317779264) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_4 : P.sumLeaves 26 125793877 128 = 348613977 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 597) (len := 128) (W := 348613977) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_5 : P.sumLeaves 26 125794005 141 = 435238542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 725) (len := 141) (W := 435238542) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_6 : P.sumLeaves 26 125794146 103 = 432207795 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 866) (len := 103) (W := 432207795) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem c122845_7 : P.sumLeaves 26 125794249 55 = 439389846 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122845) (lo := 969) (len := 55) (W := 439389846) check rows elimOK (by decide) (by decide) cover122845 (by decide)
  decide +kernel

theorem h122845 : P.leaf 36 122845 = 2470235316 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(188, 108898934), (163, 148667960), (102, 239438998), (144, 317779264), (128, 348613977), (141, 435238542), (103, 432207795), (55, 439389846)]) (.cons c122845_0 (.cons c122845_1 (.cons c122845_2 (.cons c122845_3 (.cons c122845_4 (.cons c122845_5 (.cons c122845_6 (.cons c122845_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122844, 360), (122845, 720)]

theorem segOK : checkSeg 20 perms 122844 122847 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122844 122847 1080 2158927823160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2158927823160)
    (SegSum.cons (w := 360) h122844 (SegSum.cons (w := 720) h122845 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S99
