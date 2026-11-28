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

namespace RACert.S6N0.C0.S86

open RACert RACert.Problem

theorem cover383999 : P.CoversSplit 26 10 383999 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f383999 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (393214976 + i)

theorem c383999_0 : rowSum f383999 0 229 = 1321116750 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383999 (by decide)
  decide +kernel

theorem c383999_1 : rowSum f383999 229 158 = 1790146152 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383999 (by decide)
  decide +kernel

theorem c383999_2 : rowSum f383999 387 96 = 1956548602 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383999 (by decide)
  decide +kernel

theorem c383999_3 : rowSum f383999 483 395 = 2399956130 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383999 (by decide)
  decide +kernel

theorem c383999_4 : rowSum f383999 878 146 = 1640166754 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383999 (by decide)
  decide +kernel

theorem sum383999 : rowSum f383999 0 1024 = 9107934388 :=
  rowSum_append (F := f383999) (lo := 0) (n := 229) (m := 795) (A := 1321116750) (B := 7786817638) c383999_0 (rowSum_append (F := f383999) (lo := 229) (n := 158) (m := 637) (A := 1790146152) (B := 5996671486) c383999_1 (rowSum_append (F := f383999) (lo := 387) (n := 96) (m := 541) (A := 1956548602) (B := 4040122884) c383999_2 (rowSum_append (F := f383999) (lo := 483) (n := 395) (m := 146) (A := 2399956130) (B := 1640166754) c383999_3 (c383999_4))))

theorem h383999 : P.leaf 36 383999 = 9107934388 :=
  leaf_weighted (k := 26) (d := 10) (H := 383999) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 383999) (by decide) (by decide +kernel)) sum383999

theorem h241663 : P.leaf 36 241663 = 9107934388 :=
  orient6 (v := 383999) (by decide) (by decide +kernel) h383999

theorem cover242467 : P.CoversSplit 26 10 242467 0xfffffffffffffffffffffafafffff0f0ffffffffffccccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffccc8c8fafaa0a0fa008000ffffffffffccffccfffffafaffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242467 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248286208 + i)

theorem c242467_0 : rowSum f242467 0 443 = 59990548 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_1 : rowSum f242467 443 411 = 107579628 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem c242467_2 : rowSum f242467 854 170 = 86774280 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242467 (by decide)
  decide +kernel

theorem sum242467 : rowSum f242467 0 1024 = 254344456 :=
  rowSum_append (F := f242467) (lo := 0) (n := 443) (m := 581) (A := 59990548) (B := 194353908) c242467_0 (rowSum_append (F := f242467) (lo := 443) (n := 411) (m := 170) (A := 107579628) (B := 86774280) c242467_1 (c242467_2))

theorem h242467 : P.leaf 36 242467 = 254344456 :=
  leaf_weighted (k := 26) (d := 10) (H := 242467) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 242467) (by decide) (by decide +kernel)) sum242467

theorem cover242471 : P.CoversSplit 26 10 242471 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffffc8c8fafaa0a0fa008000ffffffffffccffccffffffffffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242471 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (248290304 + i)

theorem c242471_0 : rowSum f242471 0 559 = 126905787 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_1 : rowSum f242471 559 260 = 112871690 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem c242471_2 : rowSum f242471 819 205 = 156828885 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover242471 (by decide)
  decide +kernel

theorem sum242471 : rowSum f242471 0 1024 = 396606362 :=
  rowSum_append (F := f242471) (lo := 0) (n := 559) (m := 465) (A := 126905787) (B := 269700575) c242471_0 (rowSum_append (F := f242471) (lo := 559) (n := 260) (m := 205) (A := 112871690) (B := 156828885) c242471_1 (c242471_2))

theorem h242471 : P.leaf 36 242471 = 396606362 :=
  leaf_weighted (k := 26) (d := 10) (H := 242471) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 242471) (by decide) (by decide +kernel)) sum242471

theorem cover242479 : P.CoversSplit 26 10 242479 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafafafaa0a0fafaa0a0fffffafaffffc8c8fafaa0a0fa008000ffffffffffccffccffffffffffccf0c0ffccffcccc00cc00ffccaa88cc0080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242479 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248298496 + i)

theorem c242479_0 : rowSum f242479 0 439 = 161980866 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_1 : rowSum f242479 439 391 = 277411754 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem c242479_2 : rowSum f242479 830 194 = 241358162 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242479 (by decide)
  decide +kernel

theorem sum242479 : rowSum f242479 0 1024 = 680750782 :=
  rowSum_append (F := f242479) (lo := 0) (n := 439) (m := 585) (A := 161980866) (B := 518769916) c242479_0 (rowSum_append (F := f242479) (lo := 439) (n := 391) (m := 194) (A := 277411754) (B := 241358162) c242479_1 (c242479_2))

theorem h242479 : P.leaf 36 242479 = 680750782 :=
  leaf_weighted (k := 26) (d := 10) (H := 242479) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 242479) (by decide) (by decide +kernel)) sum242479

theorem cover378349 : P.CoversSplit 26 10 378349 0xfffffffffffffffffffffafafffffafaffffffffffccffccfafafafac8c8c8c8fffffffffffffffffafaf0f0fafaf0f0ffffffffffccffccfafaf0f0c8c8c0c0fffffffffffffffffffffafafffffafaffffffffcc00cc00fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [580, 629, 636, 873, 881, 922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f378349 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (387429376 + i)

theorem c378349_0 : rowSum f378349 0 414 = 119627826 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 378349) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover378349 (by decide)
  decide +kernel

theorem c378349_1 : rowSum f378349 414 361 = 271388050 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 378349) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover378349 (by decide)
  decide +kernel

theorem c378349_2 : rowSum f378349 775 212 = 231034906 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 378349) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover378349 (by decide)
  decide +kernel

theorem c378349_3 : rowSum f378349 987 37 = 97601660 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 378349) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover378349 (by decide)
  decide +kernel

theorem sum378349 : rowSum f378349 0 1024 = 719652442 :=
  rowSum_append (F := f378349) (lo := 0) (n := 414) (m := 610) (A := 119627826) (B := 600024616) c378349_0 (rowSum_append (F := f378349) (lo := 414) (n := 361) (m := 249) (A := 271388050) (B := 328636566) c378349_1 (rowSum_append (F := f378349) (lo := 775) (n := 212) (m := 37) (A := 231034906) (B := 97601660) c378349_2 (c378349_3)))

theorem h378349 : P.leaf 36 378349 = 719652442 :=
  leaf_weighted (k := 26) (d := 10) (H := 378349) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 378349) (by decide) (by decide +kernel)) sum378349

theorem h242487 : P.leaf 36 242487 = 719652442 :=
  orient6 (v := 378349) (by decide) (by decide +kernel) h378349

def seg : List (ℕ × ℕ) := [(241663, 90), (242467, 12), (242471, 120), (242479, 180), (242487, 360)]

theorem segOK : checkSeg 20 perms 241663 242495 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241663 242495 762 1251969011712 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1251969011712)
    (SegSum.cons (w := 90) h241663 (SegSum.cons (w := 12) h242467 (SegSum.cons (w := 120) h242471 (SegSum.cons (w := 180) h242479 (SegSum.cons (w := 360) h242487 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S86
