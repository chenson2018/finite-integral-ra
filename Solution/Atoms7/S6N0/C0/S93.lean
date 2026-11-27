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

namespace RACert.S6N0.C0.S93

open RACert RACert.Problem

theorem cover131056 : P.CoversSplit 26 10 131056 0xfac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489]) (by decide +kernel)

noncomputable def f131056 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (134201344 + i)

theorem c131056_0 : rowSum f131056 0 303 = 4325824 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131056) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_1 : rowSum f131056 303 319 = 5422112 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131056) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_2 : rowSum f131056 622 335 = 6325448 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131056) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_3 : rowSum f131056 957 67 = 779824 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131056) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem sum131056 : rowSum f131056 0 1024 = 16853208 :=
  rowSum_append (F := f131056) (lo := 0) (n := 303) (m := 721) (A := 4325824) (B := 12527384) c131056_0 (rowSum_append (F := f131056) (lo := 303) (n := 319) (m := 402) (A := 5422112) (B := 7105272) c131056_1 (rowSum_append (F := f131056) (lo := 622) (n := 335) (m := 67) (A := 6325448) (B := 779824) c131056_2 (c131056_3)))

theorem h131056 : P.leaf 36 131056 = 16853208 :=
  leaf_weighted (k := 26) (d := 10) (H := 131056) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 131056) (by decide) (by decide +kernel)) sum131056

theorem cover131057 : P.CoversSplit 26 10 131057 0xfffffafaffccfac8fffffafaffccfac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fffffafaffccfac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1658]) (by decide +kernel)

noncomputable def f131057 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (134202368 + i)

theorem c131057_0 : rowSum f131057 0 240 = 21186692 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131057) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_1 : rowSum f131057 240 223 = 339981766 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131057) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_2 : rowSum f131057 463 228 = 448840468 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131057) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_3 : rowSum f131057 691 228 = 619996412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131057) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_4 : rowSum f131057 919 105 = 592714256 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131057) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem sum131057 : rowSum f131057 0 1024 = 2022719594 :=
  rowSum_append (F := f131057) (lo := 0) (n := 240) (m := 784) (A := 21186692) (B := 2001532902) c131057_0 (rowSum_append (F := f131057) (lo := 240) (n := 223) (m := 561) (A := 339981766) (B := 1661551136) c131057_1 (rowSum_append (F := f131057) (lo := 463) (n := 228) (m := 333) (A := 448840468) (B := 1212710668) c131057_2 (rowSum_append (F := f131057) (lo := 691) (n := 228) (m := 105) (A := 619996412) (B := 592714256) c131057_3 (c131057_4))))

theorem h131057 : P.leaf 36 131057 = 2022719594 :=
  leaf_weighted (k := 26) (d := 10) (H := 131057) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 131057) (by decide) (by decide +kernel)) sum131057

theorem cover131059 : P.CoversSplit 26 10 131059 0xfffffffffffffafafffffafafffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8fffffffffffffafafffffafafffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1658]) (by decide +kernel)

noncomputable def f131059 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (134204416 + i)

theorem c131059_0 : rowSum f131059 0 245 = 112667744 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131059) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_1 : rowSum f131059 245 193 = 606048594 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131059) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_2 : rowSum f131059 438 240 = 891742380 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131059) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_3 : rowSum f131059 678 211 = 1197942308 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131059) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_4 : rowSum f131059 889 135 = 815894572 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131059) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem sum131059 : rowSum f131059 0 1024 = 3624295598 :=
  rowSum_append (F := f131059) (lo := 0) (n := 245) (m := 779) (A := 112667744) (B := 3511627854) c131059_0 (rowSum_append (F := f131059) (lo := 245) (n := 193) (m := 586) (A := 606048594) (B := 2905579260) c131059_1 (rowSum_append (F := f131059) (lo := 438) (n := 240) (m := 346) (A := 891742380) (B := 2013836880) c131059_2 (rowSum_append (F := f131059) (lo := 678) (n := 211) (m := 135) (A := 1197942308) (B := 815894572) c131059_3 (c131059_4))))

theorem h131059 : P.leaf 36 131059 = 3624295598 :=
  leaf_weighted (k := 26) (d := 10) (H := 131059) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 131059) (by decide) (by decide +kernel)) sum131059

theorem cover131063 : P.CoversSplit 26 10 131063 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f131063 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (134208512 + i)

theorem c131063_0 : rowSum f131063 0 245 = 475318728 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131063) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_1 : rowSum f131063 245 190 = 1208389752 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131063) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_2 : rowSum f131063 435 202 = 1421175272 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131063) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_3 : rowSum f131063 637 243 = 1689657262 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131063) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_4 : rowSum f131063 880 144 = 1285790956 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131063) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem sum131063 : rowSum f131063 0 1024 = 6080331970 :=
  rowSum_append (F := f131063) (lo := 0) (n := 245) (m := 779) (A := 475318728) (B := 5605013242) c131063_0 (rowSum_append (F := f131063) (lo := 245) (n := 190) (m := 589) (A := 1208389752) (B := 4396623490) c131063_1 (rowSum_append (F := f131063) (lo := 435) (n := 202) (m := 387) (A := 1421175272) (B := 2975448218) c131063_2 (rowSum_append (F := f131063) (lo := 637) (n := 243) (m := 144) (A := 1689657262) (B := 1285790956) c131063_3 (c131063_4))))

theorem h131063 : P.leaf 36 131063 = 6080331970 :=
  leaf_weighted (k := 26) (d := 10) (H := 131063) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 131063) (by decide) (by decide +kernel)) sum131063

def seg : List (ℕ × ℕ) := [(131056, 60), (131057, 180), (131059, 180), (131063, 60)]

theorem segOK : checkSeg 20 perms 131056 131064 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131056 131064 480 1382293845240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1382293845240)
    (SegSum.cons (w := 60) h131056 (SegSum.cons (w := 180) h131057 (SegSum.cons (w := 180) h131059 (SegSum.cons (w := 60) h131063 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S93
