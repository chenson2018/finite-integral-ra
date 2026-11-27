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

namespace RACert.S6N0.C0.S88

open RACert RACert.Problem

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

theorem cover122847 : P.CoversSplit 26 10 122847 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafafffffa00fafafafac8c8c800fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122847 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125795328 + i)

theorem c122847_0 : rowSum f122847 0 292 = 765738274 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_1 : rowSum f122847 292 242 = 1198908536 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_2 : rowSum f122847 534 245 = 1343286300 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_3 : rowSum f122847 779 177 = 1369383154 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_4 : rowSum f122847 956 68 = 343459744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem sum122847 : rowSum f122847 0 1024 = 5020776008 :=
  rowSum_append (F := f122847) (lo := 0) (n := 292) (m := 732) (A := 765738274) (B := 4255037734) c122847_0 (rowSum_append (F := f122847) (lo := 292) (n := 242) (m := 490) (A := 1198908536) (B := 3056129198) c122847_1 (rowSum_append (F := f122847) (lo := 534) (n := 245) (m := 245) (A := 1343286300) (B := 1712842898) c122847_2 (rowSum_append (F := f122847) (lo := 779) (n := 177) (m := 68) (A := 1369383154) (B := 343459744) c122847_3 (c122847_4))))

theorem h122847 : P.leaf 36 122847 = 5020776008 :=
  leaf_weighted (k := 26) (d := 10) (H := 122847) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 122847) (by decide) (by decide +kernel)) sum122847

theorem cover122866 : P.CoversSplit 26 10 122866 0xfffffffffffffafafafafafafafafafaffccffccffccfac8fac8fac8c8c8c8c8fffffafafffffafafafafafafafafafaffccfac8ffccfac8fac8fac8c8c8c8c8fffffffffffffafafafafafafafafafaffccffccccccc8c8fac8fac8c8c8c8c8fffffafafffffafafafafafafafafafaffccfac8ccccc8c8fac8fac8c8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1665]) (by decide +kernel)

theorem c122866_0 : P.sumLeaves 26 125814784 171 = 6735364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 0) (len := 171) (W := 6735364) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_1 : P.sumLeaves 26 125814955 140 = 19065402 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 171) (len := 140) (W := 19065402) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_2 : P.sumLeaves 26 125815095 142 = 91569285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 311) (len := 142) (W := 91569285) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_3 : P.sumLeaves 26 125815237 141 = 106947498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 453) (len := 141) (W := 106947498) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_4 : P.sumLeaves 26 125815378 129 = 84591955 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 594) (len := 129) (W := 84591955) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_5 : P.sumLeaves 26 125815507 149 = 120935164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 723) (len := 149) (W := 120935164) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_6 : P.sumLeaves 26 125815656 120 = 135780509 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 872) (len := 120) (W := 135780509) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_7 : P.sumLeaves 26 125815776 32 = 92044806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 992) (len := 32) (W := 92044806) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem h122866 : P.leaf 36 122866 = 657669983 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 6735364), (140, 19065402), (142, 91569285), (141, 106947498), (129, 84591955), (149, 120935164), (120, 135780509), (32, 92044806)]) (.cons c122866_0 (.cons c122866_1 (.cons c122866_2 (.cons c122866_3 (.cons c122866_4 (.cons c122866_5 (.cons c122866_6 (.cons c122866_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122845, 720), (122847, 360), (122866, 720)]

theorem segOK : checkSeg 20 perms 122845 122867 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122845 122867 1800 4059571178160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4059571178160)
    (SegSum.cons (w := 720) h122845 (SegSum.cons (w := 360) h122847 (SegSum.cons (w := 720) h122866 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S88
