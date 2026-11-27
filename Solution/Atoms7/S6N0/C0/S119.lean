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

namespace RACert.S6N0.C0.S119

open RACert RACert.Problem

theorem cover262140 : P.CoversSplit 26 10 262140 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f262140 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (268431360 + i)

theorem c262140_0 : rowSum f262140 0 210 = 86347552 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_1 : rowSum f262140 210 141 = 1038099560 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_2 : rowSum f262140 351 100 = 1797354172 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_3 : rowSum f262140 451 392 = 2335071948 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem c262140_4 : rowSum f262140 843 181 = 2855237840 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262140 (by decide)
  decide +kernel

theorem sum262140 : rowSum f262140 0 1024 = 8112111072 :=
  rowSum_append (F := f262140) (lo := 0) (n := 210) (m := 814) (A := 86347552) (B := 8025763520) c262140_0 (rowSum_append (F := f262140) (lo := 210) (n := 141) (m := 673) (A := 1038099560) (B := 6987663960) c262140_1 (rowSum_append (F := f262140) (lo := 351) (n := 100) (m := 573) (A := 1797354172) (B := 5190309788) c262140_2 (rowSum_append (F := f262140) (lo := 451) (n := 392) (m := 181) (A := 2335071948) (B := 2855237840) c262140_3 (c262140_4))))

theorem h262140 : P.leaf 36 262140 = 8112111072 :=
  leaf_weighted (k := 26) (d := 10) (H := 262140) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 262140) (by decide) (by decide +kernel)) sum262140

theorem cover262141 : P.CoversSplit 26 10 262141 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f262141 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (268432384 + i)

theorem c262141_0 : rowSum f262141 0 210 = 414612096 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262141) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_1 : rowSum f262141 210 141 = 1842242136 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262141) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_2 : rowSum f262141 351 100 = 2877589412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262141) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_3 : rowSum f262141 451 392 = 3309749852 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262141) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem c262141_4 : rowSum f262141 843 181 = 3797559484 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262141) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262141 (by decide)
  decide +kernel

theorem sum262141 : rowSum f262141 0 1024 = 12241752980 :=
  rowSum_append (F := f262141) (lo := 0) (n := 210) (m := 814) (A := 414612096) (B := 11827140884) c262141_0 (rowSum_append (F := f262141) (lo := 210) (n := 141) (m := 673) (A := 1842242136) (B := 9984898748) c262141_1 (rowSum_append (F := f262141) (lo := 351) (n := 100) (m := 573) (A := 2877589412) (B := 7107309336) c262141_2 (rowSum_append (F := f262141) (lo := 451) (n := 392) (m := 181) (A := 3309749852) (B := 3797559484) c262141_3 (c262141_4))))

theorem h262141 : P.leaf 36 262141 = 12241752980 :=
  leaf_weighted (k := 26) (d := 10) (H := 262141) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 262141) (by decide) (by decide +kernel)) sum262141

theorem cover262143 : P.CoversSplit 26 10 262143 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f262143 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (268434432 + i)

theorem c262143_0 : rowSum f262143 0 210 = 1755449104 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_1 : rowSum f262143 210 141 = 3045366626 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_2 : rowSum f262143 351 100 = 3850873072 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_3 : rowSum f262143 451 392 = 4550446524 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_4 : rowSum f262143 843 181 = 4902420132 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 262143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem sum262143 : rowSum f262143 0 1024 = 18104555458 :=
  rowSum_append (F := f262143) (lo := 0) (n := 210) (m := 814) (A := 1755449104) (B := 16349106354) c262143_0 (rowSum_append (F := f262143) (lo := 210) (n := 141) (m := 673) (A := 3045366626) (B := 13303739728) c262143_1 (rowSum_append (F := f262143) (lo := 351) (n := 100) (m := 573) (A := 3850873072) (B := 9452866656) c262143_2 (rowSum_append (F := f262143) (lo := 451) (n := 392) (m := 181) (A := 4550446524) (B := 4902420132) c262143_3 (c262143_4))))

theorem h262143 : P.leaf 36 262143 = 18104555458 :=
  leaf_weighted (k := 26) (d := 10) (H := 262143) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 262143) (by decide) (by decide +kernel)) sum262143

def seg : List (ℕ × ℕ) := [(262140, 45), (262141, 180), (262143, 90)]

theorem segOK : checkSeg 20 perms 262140 520157 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 262140 520157 315 4197970525860 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4197970525860)
    (SegSum.cons (w := 45) h262140 (SegSum.cons (w := 180) h262141 (SegSum.cons (w := 90) h262143 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S119
