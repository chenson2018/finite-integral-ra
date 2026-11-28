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

namespace RACert.S6N0.C0.S78

open RACert RACert.Problem

theorem cover831359 : P.CoversSplit 26 10 831359 0xfffffffffffffffffffffafa00000000ffffffffffccffccfffffafa00000000fffffffffffffffffffffafa00000000ffffffffffccffccfffffafa00000000fffffffffffffffffffffafa00000000ffffffffffccffccfffffafa00000000fffffffffffffffffffffafa00000000ffffffffffccffccfffffafa00000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1265, 1266, 1273]) (by decide +kernel)

theorem c831359_0 : P.sumLeaves 26 851311616 176 = 279625780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 0) (len := 176) (W := 279625780) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_1 : P.sumLeaves 26 851311792 132 = 567344731 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 176) (len := 132) (W := 567344731) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_2 : P.sumLeaves 26 851311924 140 = 416061542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 308) (len := 140) (W := 416061542) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_3 : P.sumLeaves 26 851312064 136 = 638256516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 448) (len := 136) (W := 638256516) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_4 : P.sumLeaves 26 851312200 136 = 523109505 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 584) (len := 136) (W := 523109505) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_5 : P.sumLeaves 26 851312336 140 = 608002164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 720) (len := 140) (W := 608002164) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_6 : P.sumLeaves 26 851312476 132 = 648521995 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 860) (len := 132) (W := 648521995) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem c831359_7 : P.sumLeaves 26 851312608 32 = 417419890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 831359) (lo := 992) (len := 32) (W := 417419890) check rows elimOK (by decide) (by decide) cover831359 (by decide)
  decide +kernel

theorem h831359 : P.leaf 36 831359 = 4098342123 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(176, 279625780), (132, 567344731), (140, 416061542), (136, 638256516), (136, 523109505), (140, 608002164), (132, 648521995), (32, 417419890)]) (.cons c831359_0 (.cons c831359_1 (.cons c831359_2 (.cons c831359_3 (.cons c831359_4 (.cons c831359_5 (.cons c831359_6 (.cons c831359_7 (.nil))))))))) (by decide) (by decide))

theorem h122875 : P.leaf 36 122875 = 4098342123 :=
  orient84 (v := 831359) (by decide) (by decide +kernel) h831359

theorem cover294910 : P.CoversSplit 26 10 294910 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294910 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301987840 + i)

theorem c294910_0 : rowSum f294910 0 241 = 273879304 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294910) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294910 (by decide)
  decide +kernel

theorem c294910_1 : rowSum f294910 241 148 = 892732344 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294910) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294910 (by decide)
  decide +kernel

theorem c294910_2 : rowSum f294910 389 102 = 1556462610 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294910) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294910 (by decide)
  decide +kernel

theorem c294910_3 : rowSum f294910 491 403 = 1706625614 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294910) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294910 (by decide)
  decide +kernel

theorem c294910_4 : rowSum f294910 894 130 = 904485389 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294910) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294910 (by decide)
  decide +kernel

theorem sum294910 : rowSum f294910 0 1024 = 5334185261 :=
  rowSum_append (F := f294910) (lo := 0) (n := 241) (m := 783) (A := 273879304) (B := 5060305957) c294910_0 (rowSum_append (F := f294910) (lo := 241) (n := 148) (m := 635) (A := 892732344) (B := 4167573613) c294910_1 (rowSum_append (F := f294910) (lo := 389) (n := 102) (m := 533) (A := 1556462610) (B := 2611111003) c294910_2 (rowSum_append (F := f294910) (lo := 491) (n := 403) (m := 130) (A := 1706625614) (B := 904485389) c294910_3 (c294910_4))))

theorem h294910 : P.leaf 36 294910 = 5334185261 :=
  leaf_weighted (k := 26) (d := 10) (H := 294910) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294910) (by decide) (by decide +kernel)) sum294910

theorem h122878 : P.leaf 36 122878 = 5334185261 :=
  orient6 (v := 294910) (by decide) (by decide +kernel) h294910

theorem cover294911 : P.CoversSplit 26 10 294911 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294911 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301988864 + i)

theorem c294911_0 : rowSum f294911 0 241 = 1164389576 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294911) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294911 (by decide)
  decide +kernel

theorem c294911_1 : rowSum f294911 241 148 = 2051929730 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294911) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294911 (by decide)
  decide +kernel

theorem c294911_2 : rowSum f294911 389 102 = 2317391942 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294911) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294911 (by decide)
  decide +kernel

theorem c294911_3 : rowSum f294911 491 403 = 2841042416 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294911) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294911 (by decide)
  decide +kernel

theorem c294911_4 : rowSum f294911 894 130 = 1240287721 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294911) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294911 (by decide)
  decide +kernel

theorem sum294911 : rowSum f294911 0 1024 = 9615041385 :=
  rowSum_append (F := f294911) (lo := 0) (n := 241) (m := 783) (A := 1164389576) (B := 8450651809) c294911_0 (rowSum_append (F := f294911) (lo := 241) (n := 148) (m := 635) (A := 2051929730) (B := 6398722079) c294911_1 (rowSum_append (F := f294911) (lo := 389) (n := 102) (m := 533) (A := 2317391942) (B := 4081330137) c294911_2 (rowSum_append (F := f294911) (lo := 491) (n := 403) (m := 130) (A := 2841042416) (B := 1240287721) c294911_3 (c294911_4))))

theorem h294911 : P.leaf 36 294911 = 9615041385 :=
  leaf_weighted (k := 26) (d := 10) (H := 294911) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294911) (by decide) (by decide +kernel)) sum294911

theorem h122879 : P.leaf 36 122879 = 9615041385 :=
  orient6 (v := 294911) (by decide) (by decide +kernel) h294911

def seg : List (ℕ × ℕ) := [(122875, 720), (122878, 360), (122879, 360)]

theorem segOK : checkSeg 20 perms 122875 131056 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122875 131056 1440 8332527921120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 8332527921120)
    (SegSum.cons (w := 720) h122875 (SegSum.cons (w := 360) h122878 (SegSum.cons (w := 360) h122879 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S78
