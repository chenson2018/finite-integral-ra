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

namespace RACert.S6N0.C0.S77

open RACert RACert.Problem

theorem cover518637 : P.CoversSplit 26 10 518637 0xfffffffffffffffffffffefefffffefeffffffffffeeffeefffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffeeffeefffffafaffccfac8ffffffffffccffccfffffefeffccfeccffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [580, 629, 636, 881, 1658, 1665]) (by decide +kernel)

noncomputable def f518637 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (531084288 + i)

theorem c518637_0 : rowSum f518637 0 451 = 348674053 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 518637) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover518637 (by decide)
  decide +kernel

theorem c518637_1 : rowSum f518637 451 186 = 485995397 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 518637) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover518637 (by decide)
  decide +kernel

theorem c518637_2 : rowSum f518637 637 172 = 450337070 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 518637) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover518637 (by decide)
  decide +kernel

theorem c518637_3 : rowSum f518637 809 163 = 802540190 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 518637) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover518637 (by decide)
  decide +kernel

theorem c518637_4 : rowSum f518637 972 52 = 444704388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 518637) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover518637 (by decide)
  decide +kernel

theorem sum518637 : rowSum f518637 0 1024 = 2532251098 :=
  rowSum_append (F := f518637) (lo := 0) (n := 451) (m := 573) (A := 348674053) (B := 2183577045) c518637_0 (rowSum_append (F := f518637) (lo := 451) (n := 186) (m := 387) (A := 485995397) (B := 1697581648) c518637_1 (rowSum_append (F := f518637) (lo := 637) (n := 172) (m := 215) (A := 450337070) (B := 1247244578) c518637_2 (rowSum_append (F := f518637) (lo := 809) (n := 163) (m := 52) (A := 802540190) (B := 444704388) c518637_3 (c518637_4))))

theorem h518637 : P.leaf 36 518637 = 2532251098 :=
  leaf_weighted (k := 26) (d := 10) (H := 518637) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 518637) (by decide) (by decide +kernel)) sum518637

theorem h122870 : P.leaf 36 122870 = 2532251098 :=
  orient348 (v := 518637) (by decide) (by decide +kernel) h518637

theorem cover294909 : P.CoversSplit 26 10 294909 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f294909 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (301986816 + i)

theorem c294909_0 : rowSum f294909 0 241 = 469897274 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294909) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294909 (by decide)
  decide +kernel

theorem c294909_1 : rowSum f294909 241 148 = 778032790 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294909) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294909 (by decide)
  decide +kernel

theorem c294909_2 : rowSum f294909 389 102 = 1129343602 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294909) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294909 (by decide)
  decide +kernel

theorem c294909_3 : rowSum f294909 491 403 = 1340784966 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294909) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294909 (by decide)
  decide +kernel

theorem c294909_4 : rowSum f294909 894 130 = 870809311 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 294909) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover294909 (by decide)
  decide +kernel

theorem sum294909 : rowSum f294909 0 1024 = 4588867943 :=
  rowSum_append (F := f294909) (lo := 0) (n := 241) (m := 783) (A := 469897274) (B := 4118970669) c294909_0 (rowSum_append (F := f294909) (lo := 241) (n := 148) (m := 635) (A := 778032790) (B := 3340937879) c294909_1 (rowSum_append (F := f294909) (lo := 389) (n := 102) (m := 533) (A := 1129343602) (B := 2211594277) c294909_2 (rowSum_append (F := f294909) (lo := 491) (n := 403) (m := 130) (A := 1340784966) (B := 870809311) c294909_3 (c294909_4))))

theorem h294909 : P.leaf 36 294909 = 4588867943 :=
  leaf_weighted (k := 26) (d := 10) (H := 294909) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 294909) (by decide) (by decide +kernel)) sum294909

theorem h122871 : P.leaf 36 122871 = 4588867943 :=
  orient6 (v := 294909) (by decide) (by decide +kernel) h294909

theorem cover831327 : P.CoversSplit 26 10 831327 0xfffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1265, 1266, 1272, 1273]) (by decide +kernel)

noncomputable def f831327 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (851278848 + i)

theorem c831327_0 : rowSum f831327 0 350 = 481833508 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831327) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover831327 (by decide)
  decide +kernel

theorem c831327_1 : rowSum f831327 350 148 = 683175324 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831327) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover831327 (by decide)
  decide +kernel

theorem c831327_2 : rowSum f831327 498 526 = 890794144 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831327) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover831327 (by decide)
  decide +kernel

theorem sum831327 : rowSum f831327 0 1024 = 2055802976 :=
  rowSum_append (F := f831327) (lo := 0) (n := 350) (m := 674) (A := 481833508) (B := 1573969468) c831327_0 (rowSum_append (F := f831327) (lo := 350) (n := 148) (m := 526) (A := 683175324) (B := 890794144) c831327_1 (c831327_2))

theorem h831327 : P.leaf 36 831327 = 2055802976 :=
  leaf_weighted (k := 26) (d := 10) (H := 831327) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 831327) (by decide) (by decide +kernel)) sum831327

theorem h122873 : P.leaf 36 122873 = 2055802976 :=
  orient84 (v := 831327) (by decide) (by decide +kernel) h831327

theorem cover899995 : P.CoversSplit 26 10 899995 0xffffffffaaaaaaaafffffafaaaaaaaaaffffffffaa88aa88fffffafaaa88aa88ffffffffaaaaaaaafffffafaaaaaaaaaffffffffaa88aa88fffffafaaa88aa88ffffffffaaaaaaaafffffafaaaaaaaaaffccffcc88888888ffccfac888888888ffffffffaaaaaaaafffffafaaaaaaaaaffccffcc88888888ffccfac888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 930, 1273]) (by decide +kernel)

theorem c899995_0 : P.sumLeaves 26 921594880 183 = 200071931 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 0) (len := 183) (W := 200071931) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem c899995_1 : P.sumLeaves 26 921595063 175 = 298740987 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 183) (len := 175) (W := 298740987) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem c899995_2 : P.sumLeaves 26 921595238 136 = 332642197 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 358) (len := 136) (W := 332642197) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem c899995_3 : P.sumLeaves 26 921595374 140 = 293909550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 494) (len := 140) (W := 293909550) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem c899995_4 : P.sumLeaves 26 921595514 132 = 403195126 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 634) (len := 132) (W := 403195126) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem c899995_5 : P.sumLeaves 26 921595646 151 = 293491529 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 766) (len := 151) (W := 293491529) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem c899995_6 : P.sumLeaves 26 921595797 107 = 430696342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 899995) (lo := 917) (len := 107) (W := 430696342) check rows elimOK (by decide) (by decide) cover899995 (by decide)
  decide +kernel

theorem h899995 : P.leaf 36 899995 = 2252747662 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 200071931), (175, 298740987), (136, 332642197), (140, 293909550), (132, 403195126), (151, 293491529), (107, 430696342)]) (.cons c899995_0 (.cons c899995_1 (.cons c899995_2 (.cons c899995_3 (.cons c899995_4 (.cons c899995_5 (.cons c899995_6 (.nil)))))))) (by decide) (by decide))

theorem h122874 : P.leaf 36 122874 = 2252747662 :=
  orient93 (v := 899995) (by decide) (by decide +kernel) h899995

def seg : List (ℕ × ℕ) := [(122870, 360), (122871, 360), (122873, 180), (122874, 720)]

theorem segOK : checkSeg 20 perms 122870 122875 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122870 122875 1620 4555625707080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4555625707080)
    (SegSum.cons (w := 360) h122870 (SegSum.cons (w := 360) h122871 (SegSum.cons (w := 180) h122873 (SegSum.cons (w := 720) h122874 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S77
