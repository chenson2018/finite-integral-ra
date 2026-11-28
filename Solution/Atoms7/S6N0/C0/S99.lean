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

namespace RACert.S6N0.C0.S99

open RACert RACert.Problem

theorem cover851965 : P.CoversSplit 26 10 851965 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273]) (by decide +kernel)

noncomputable def f851965 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (872412160 + i)

theorem c851965_0 : rowSum f851965 0 210 = 1671131476 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851965) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851965 (by decide)
  decide +kernel

theorem c851965_1 : rowSum f851965 210 141 = 2101653716 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851965) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851965 (by decide)
  decide +kernel

theorem c851965_2 : rowSum f851965 351 104 = 2550768780 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851965) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851965 (by decide)
  decide +kernel

theorem c851965_3 : rowSum f851965 455 392 = 2745816342 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851965) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851965 (by decide)
  decide +kernel

theorem c851965_4 : rowSum f851965 847 177 = 2583853240 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851965) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851965 (by decide)
  decide +kernel

theorem sum851965 : rowSum f851965 0 1024 = 11653223554 :=
  rowSum_append (F := f851965) (lo := 0) (n := 210) (m := 814) (A := 1671131476) (B := 9982092078) c851965_0 (rowSum_append (F := f851965) (lo := 210) (n := 141) (m := 673) (A := 2101653716) (B := 7880438362) c851965_1 (rowSum_append (F := f851965) (lo := 351) (n := 104) (m := 569) (A := 2550768780) (B := 5329669582) c851965_2 (rowSum_append (F := f851965) (lo := 455) (n := 392) (m := 177) (A := 2745816342) (B := 2583853240) c851965_3 (c851965_4))))

theorem h851965 : P.leaf 36 851965 = 11653223554 :=
  leaf_weighted (k := 26) (d := 10) (H := 851965) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 851965) (by decide) (by decide +kernel)) sum851965

theorem h262135 : P.leaf 36 262135 = 11653223554 :=
  orient80 (v := 851965) (by decide) (by decide +kernel) h851965

theorem cover851955 : P.CoversSplit 26 10 851955 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489]) (by decide +kernel)

noncomputable def f851955 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (872401920 + i)

theorem c851955_0 : rowSum f851955 0 210 = 1220801054 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851955) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851955 (by decide)
  decide +kernel

theorem c851955_1 : rowSum f851955 210 141 = 1379383566 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851955) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851955 (by decide)
  decide +kernel

theorem c851955_2 : rowSum f851955 351 104 = 1756181692 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851955) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851955 (by decide)
  decide +kernel

theorem c851955_3 : rowSum f851955 455 392 = 1953056234 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851955) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851955 (by decide)
  decide +kernel

theorem c851955_4 : rowSum f851955 847 177 = 1802688526 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851955) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851955 (by decide)
  decide +kernel

theorem sum851955 : rowSum f851955 0 1024 = 8112111072 :=
  rowSum_append (F := f851955) (lo := 0) (n := 210) (m := 814) (A := 1220801054) (B := 6891310018) c851955_0 (rowSum_append (F := f851955) (lo := 210) (n := 141) (m := 673) (A := 1379383566) (B := 5511926452) c851955_1 (rowSum_append (F := f851955) (lo := 351) (n := 104) (m := 569) (A := 1756181692) (B := 3755744760) c851955_2 (rowSum_append (F := f851955) (lo := 455) (n := 392) (m := 177) (A := 1953056234) (B := 1802688526) c851955_3 (c851955_4))))

theorem h851955 : P.leaf 36 851955 = 8112111072 :=
  leaf_weighted (k := 26) (d := 10) (H := 851955) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 851955) (by decide) (by decide +kernel)) sum851955

theorem h262140 : P.leaf 36 262140 = 8112111072 :=
  orient80 (v := 851955) (by decide) (by decide +kernel) h851955

theorem cover851959 : P.CoversSplit 26 10 851959 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1265, 1273]) (by decide +kernel)

noncomputable def f851959 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (872406016 + i)

theorem c851959_0 : rowSum f851959 0 181 = 1930106832 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851959) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover851959 (by decide)
  decide +kernel

theorem c851959_1 : rowSum f851959 181 194 = 2263492454 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851959) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover851959 (by decide)
  decide +kernel

theorem c851959_2 : rowSum f851959 375 235 = 2612233126 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851959) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover851959 (by decide)
  decide +kernel

theorem c851959_3 : rowSum f851959 610 210 = 2675170448 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851959) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover851959 (by decide)
  decide +kernel

theorem c851959_4 : rowSum f851959 820 204 = 2760750120 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851959) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover851959 (by decide)
  decide +kernel

theorem sum851959 : rowSum f851959 0 1024 = 12241752980 :=
  rowSum_append (F := f851959) (lo := 0) (n := 181) (m := 843) (A := 1930106832) (B := 10311646148) c851959_0 (rowSum_append (F := f851959) (lo := 181) (n := 194) (m := 649) (A := 2263492454) (B := 8048153694) c851959_1 (rowSum_append (F := f851959) (lo := 375) (n := 235) (m := 414) (A := 2612233126) (B := 5435920568) c851959_2 (rowSum_append (F := f851959) (lo := 610) (n := 210) (m := 204) (A := 2675170448) (B := 2760750120) c851959_3 (c851959_4))))

theorem h851959 : P.leaf 36 851959 = 12241752980 :=
  leaf_weighted (k := 26) (d := 10) (H := 851959) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 851959) (by decide) (by decide +kernel)) sum851959

theorem h262141 : P.leaf 36 262141 = 12241752980 :=
  orient80 (v := 851959) (by decide) (by decide +kernel) h851959

theorem cover851967 : P.CoversSplit 26 10 851967 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273]) (by decide +kernel)

noncomputable def f851967 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (872414208 + i)

theorem c851967_0 : rowSum f851967 0 210 = 2859005558 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851967) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851967 (by decide)
  decide +kernel

theorem c851967_1 : rowSum f851967 210 141 = 3412100788 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851967) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851967 (by decide)
  decide +kernel

theorem c851967_2 : rowSum f851967 351 104 = 3921495200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851967) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851967 (by decide)
  decide +kernel

theorem c851967_3 : rowSum f851967 455 392 = 4208268124 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851967) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851967 (by decide)
  decide +kernel

theorem c851967_4 : rowSum f851967 847 177 = 3703685788 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 851967) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover851967 (by decide)
  decide +kernel

theorem sum851967 : rowSum f851967 0 1024 = 18104555458 :=
  rowSum_append (F := f851967) (lo := 0) (n := 210) (m := 814) (A := 2859005558) (B := 15245549900) c851967_0 (rowSum_append (F := f851967) (lo := 210) (n := 141) (m := 673) (A := 3412100788) (B := 11833449112) c851967_1 (rowSum_append (F := f851967) (lo := 351) (n := 104) (m := 569) (A := 3921495200) (B := 7911953912) c851967_2 (rowSum_append (F := f851967) (lo := 455) (n := 392) (m := 177) (A := 4208268124) (B := 3703685788) c851967_3 (c851967_4))))

theorem h851967 : P.leaf 36 851967 = 18104555458 :=
  leaf_weighted (k := 26) (d := 10) (H := 851967) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 851967) (by decide) (by decide +kernel)) sum851967

theorem h262143 : P.leaf 36 262143 = 18104555458 :=
  orient80 (v := 851967) (by decide) (by decide +kernel) h851967

def seg : List (ℕ × ℕ) := [(262135, 180), (262140, 45), (262141, 180), (262143, 90)]

theorem segOK : checkSeg 20 perms 262135 520157 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 262135 520157 495 6295550765580 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6295550765580)
    (SegSum.cons (w := 180) h262135 (SegSum.cons (w := 45) h262140 (SegSum.cons (w := 180) h262141 (SegSum.cons (w := 90) h262143 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S99
