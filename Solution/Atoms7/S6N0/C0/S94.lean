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

namespace RACert.S6N0.C0.S94

open RACert RACert.Problem

theorem cover131064 : P.CoversSplit 26 10 131064 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fafafafafafafafafafafafafafafafafafafafafafafac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fafafafafafafafafafafafafafafafafafafafafac8fac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f131064 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (134209536 + i)

theorem c131064_0 : rowSum f131064 0 267 = 24183336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131064) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_1 : rowSum f131064 267 177 = 409672918 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131064) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_2 : rowSum f131064 444 253 = 602404262 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131064) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_3 : rowSum f131064 697 234 = 734432846 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131064) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_4 : rowSum f131064 931 93 = 556476904 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131064) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem sum131064 : rowSum f131064 0 1024 = 2327170266 :=
  rowSum_append (F := f131064) (lo := 0) (n := 267) (m := 757) (A := 24183336) (B := 2302986930) c131064_0 (rowSum_append (F := f131064) (lo := 267) (n := 177) (m := 580) (A := 409672918) (B := 1893314012) c131064_1 (rowSum_append (F := f131064) (lo := 444) (n := 253) (m := 327) (A := 602404262) (B := 1290909750) c131064_2 (rowSum_append (F := f131064) (lo := 697) (n := 234) (m := 93) (A := 734432846) (B := 556476904) c131064_3 (c131064_4))))

theorem h131064 : P.leaf 36 131064 = 2327170266 :=
  leaf_weighted (k := 26) (d := 10) (H := 131064) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 131064) (by decide) (by decide +kernel)) sum131064

theorem cover131065 : P.CoversSplit 26 10 131065 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f131065 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (134210560 + i)

theorem c131065_0 : rowSum f131065 0 219 = 88920304 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_1 : rowSum f131065 219 202 = 392254324 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_2 : rowSum f131065 421 194 = 859377536 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_3 : rowSum f131065 615 208 = 1227206550 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_4 : rowSum f131065 823 174 = 1279854964 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_5 : rowSum f131065 997 27 = 441560792 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem sum131065 : rowSum f131065 0 1024 = 4289174470 :=
  rowSum_append (F := f131065) (lo := 0) (n := 219) (m := 805) (A := 88920304) (B := 4200254166) c131065_0 (rowSum_append (F := f131065) (lo := 219) (n := 202) (m := 603) (A := 392254324) (B := 3807999842) c131065_1 (rowSum_append (F := f131065) (lo := 421) (n := 194) (m := 409) (A := 859377536) (B := 2948622306) c131065_2 (rowSum_append (F := f131065) (lo := 615) (n := 208) (m := 201) (A := 1227206550) (B := 1721415756) c131065_3 (rowSum_append (F := f131065) (lo := 823) (n := 174) (m := 27) (A := 1279854964) (B := 441560792) c131065_4 (c131065_5)))))

theorem h131065 : P.leaf 36 131065 = 4289174470 :=
  leaf_weighted (k := 26) (d := 10) (H := 131065) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 131065) (by decide) (by decide +kernel)) sum131065

theorem cover131067 : P.CoversSplit 26 10 131067 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f131067 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (134212608 + i)

theorem c131067_0 : rowSum f131067 0 245 = 476739152 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131067) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_1 : rowSum f131067 245 190 = 1016940032 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131067) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_2 : rowSum f131067 435 202 = 1705833976 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131067) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_3 : rowSum f131067 637 243 = 2218916490 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131067) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_4 : rowSum f131067 880 144 = 1725584284 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131067) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem sum131067 : rowSum f131067 0 1024 = 7144013934 :=
  rowSum_append (F := f131067) (lo := 0) (n := 245) (m := 779) (A := 476739152) (B := 6667274782) c131067_0 (rowSum_append (F := f131067) (lo := 245) (n := 190) (m := 589) (A := 1016940032) (B := 5650334750) c131067_1 (rowSum_append (F := f131067) (lo := 435) (n := 202) (m := 387) (A := 1705833976) (B := 3944500774) c131067_2 (rowSum_append (F := f131067) (lo := 637) (n := 243) (m := 144) (A := 2218916490) (B := 1725584284) c131067_3 (c131067_4))))

theorem h131067 : P.leaf 36 131067 = 7144013934 :=
  leaf_weighted (k := 26) (d := 10) (H := 131067) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 131067) (by decide) (by decide +kernel)) sum131067

theorem cover131071 : P.CoversSplit 26 10 131071 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f131071 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (134216704 + i)

theorem c131071_0 : rowSum f131071 0 245 = 1929572004 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131071) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_1 : rowSum f131071 245 190 = 2532284978 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131071) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_2 : rowSum f131071 435 202 = 3199359672 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131071) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_3 : rowSum f131071 637 243 = 3505581638 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131071) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_4 : rowSum f131071 880 144 = 2281357484 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 131071) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem sum131071 : rowSum f131071 0 1024 = 13448155776 :=
  rowSum_append (F := f131071) (lo := 0) (n := 245) (m := 779) (A := 1929572004) (B := 11518583772) c131071_0 (rowSum_append (F := f131071) (lo := 245) (n := 190) (m := 589) (A := 2532284978) (B := 8986298794) c131071_1 (rowSum_append (F := f131071) (lo := 435) (n := 202) (m := 387) (A := 3199359672) (B := 5786939122) c131071_2 (rowSum_append (F := f131071) (lo := 637) (n := 243) (m := 144) (A := 3505581638) (B := 2281357484) c131071_3 (c131071_4))))

theorem h131071 : P.leaf 36 131071 = 13448155776 :=
  leaf_weighted (k := 26) (d := 10) (H := 131071) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 131071) (by decide) (by decide +kernel)) sum131071

def seg : List (ℕ × ℕ) := [(131064, 60), (131065, 180), (131067, 180), (131071, 60)]

theorem segOK : checkSeg 20 perms 131064 227823 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131064 227823 480 3004493475240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3004493475240)
    (SegSum.cons (w := 60) h131064 (SegSum.cons (w := 180) h131065 (SegSum.cons (w := 180) h131067 (SegSum.cons (w := 60) h131071 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S94
