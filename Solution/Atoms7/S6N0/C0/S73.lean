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

namespace RACert.S6N0.C0.S73

open RACert RACert.Problem

theorem cover321533 : P.CoversSplit 26 10 321533 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 1658, 1665]) (by decide +kernel)

noncomputable def f321533 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (329249792 + i)

theorem c321533_0 : rowSum f321533 0 241 = 455414723 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321533 (by decide)
  decide +kernel

theorem c321533_1 : rowSum f321533 241 148 = 583079912 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321533 (by decide)
  decide +kernel

theorem c321533_2 : rowSum f321533 389 102 = 675829492 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321533 (by decide)
  decide +kernel

theorem c321533_3 : rowSum f321533 491 403 = 837110478 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321533 (by decide)
  decide +kernel

theorem c321533_4 : rowSum f321533 894 130 = 489713888 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321533 (by decide)
  decide +kernel

theorem sum321533 : rowSum f321533 0 1024 = 3041148493 :=
  rowSum_append (F := f321533) (lo := 0) (n := 241) (m := 783) (A := 455414723) (B := 2585733770) c321533_0 (rowSum_append (F := f321533) (lo := 241) (n := 148) (m := 635) (A := 583079912) (B := 2002653858) c321533_1 (rowSum_append (F := f321533) (lo := 389) (n := 102) (m := 533) (A := 675829492) (B := 1326824366) c321533_2 (rowSum_append (F := f321533) (lo := 491) (n := 403) (m := 130) (A := 837110478) (B := 489713888) c321533_3 (c321533_4))))

theorem h321533 : P.leaf 36 321533 = 3041148493 :=
  leaf_weighted (k := 26) (d := 10) (H := 321533) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 321533) (by decide) (by decide +kernel)) sum321533

theorem h120823 : P.leaf 36 120823 = 3041148493 :=
  orient80 (v := 321533) (by decide) (by decide +kernel) h321533

theorem cover604671 : P.CoversSplit 26 10 604671 0xff00ff0000000000ff00fe0000000000ff00ff0000000002ff00fe0000000002ff00fa0000000000ff00fa0000000000ff00fa0000000002ff00fa000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 874, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f604671 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619183104 + i)

theorem c604671_0 : rowSum f604671 0 1024 = 646901339 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604671) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604671 (by decide)
  decide +kernel

theorem sum604671 : rowSum f604671 0 1024 = 646901339 :=
  c604671_0

theorem h604671 : P.leaf 36 604671 = 646901339 :=
  leaf_weighted (k := 26) (d := 10) (H := 604671) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604671) (by decide) (by decide +kernel)) sum604671

theorem h120827 : P.leaf 36 120827 = 646901339 :=
  orient86 (v := 604671) (by decide) (by decide +kernel) h604671

theorem cover321523 : P.CoversSplit 26 10 321523 0xffffff00f0f0f000fffffa00f0f0f000ffffff00f0c0f000fac8fa00f0c0f000ffffff00f0f0f000fafafa00f0f0f000ffffff00f0c0f000fac8fa00f0c0f000ffffff00f0f0f000fffffa00f0f0f000ffccff00f0c0f000fac8fa00f0c0f000ffffff00f0f0f000fafafa00f0f0f000ffccff00f0c0f000fac8fa00f0c0f000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 874, 880, 1658, 1665]) (by decide +kernel)

noncomputable def f321523 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (329239552 + i)

theorem c321523_0 : rowSum f321523 0 343 = 183198636 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321523 (by decide)
  decide +kernel

theorem c321523_1 : rowSum f321523 343 438 = 472564100 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321523 (by decide)
  decide +kernel

theorem c321523_2 : rowSum f321523 781 243 = 346530161 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover321523 (by decide)
  decide +kernel

theorem sum321523 : rowSum f321523 0 1024 = 1002292897 :=
  rowSum_append (F := f321523) (lo := 0) (n := 343) (m := 681) (A := 183198636) (B := 819094261) c321523_0 (rowSum_append (F := f321523) (lo := 343) (n := 438) (m := 243) (A := 472564100) (B := 346530161) c321523_1 (c321523_2))

theorem h321523 : P.leaf 36 321523 = 1002292897 :=
  leaf_weighted (k := 26) (d := 10) (H := 321523) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 321523) (by decide) (by decide +kernel)) sum321523

theorem h120828 : P.leaf 36 120828 = 1002292897 :=
  orient80 (v := 321523) (by decide) (by decide +kernel) h321523

theorem cover321527 : P.CoversSplit 26 10 321527 0xffffff00ffffff00fffffa00fffffa00ffffff00ffccff00fac8fa00fac8fa00ffffff00ffffff00fafafa00fafafa00ffffff00ffccff00fac8fa00fac8fa00ffffff00ffffff00fffffa00fffffa00ffccff00ffccff00fac8fa00fac8fa00ffffff00ffffff00fafafa00fafafa00ffccff00ffccff00fac8fa00fac8fa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 874, 881, 1658, 1665]) (by decide +kernel)

theorem c321527_0 : P.sumLeaves 26 329243648 180 = 204713881 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 0) (len := 180) (W := 204713881) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem c321527_1 : P.sumLeaves 26 329243828 158 = 297318415 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 180) (len := 158) (W := 297318415) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem c321527_2 : P.sumLeaves 26 329243986 138 = 384944853 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 338) (len := 138) (W := 384944853) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem c321527_3 : P.sumLeaves 26 329244124 158 = 430171975 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 476) (len := 158) (W := 430171975) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem c321527_4 : P.sumLeaves 26 329244282 153 = 450482997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 634) (len := 153) (W := 450482997) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem c321527_5 : P.sumLeaves 26 329244435 157 = 412050985 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 787) (len := 157) (W := 412050985) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem c321527_6 : P.sumLeaves 26 329244592 80 = 437316582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 321527) (lo := 944) (len := 80) (W := 437316582) check rows elimOK (by decide) (by decide) cover321527 (by decide)
  decide +kernel

theorem h321527 : P.leaf 36 321527 = 2616999688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(180, 204713881), (158, 297318415), (138, 384944853), (158, 430171975), (153, 450482997), (157, 412050985), (80, 437316582)]) (.cons c321527_0 (.cons c321527_1 (.cons c321527_2 (.cons c321527_3 (.cons c321527_4 (.cons c321527_5 (.cons c321527_6 (.nil)))))))) (by decide) (by decide))

theorem h120829 : P.leaf 36 120829 = 2616999688 :=
  orient80 (v := 321527) (by decide) (by decide +kernel) h321527

def seg : List (ℕ × ℕ) := [(120823, 360), (120827, 360), (120828, 360), (120829, 720)]

theorem segOK : checkSeg 20 perms 120823 120831 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120823 120831 1800 3572763157800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3572763157800)
    (SegSum.cons (w := 360) h120823 (SegSum.cons (w := 360) h120827 (SegSum.cons (w := 360) h120828 (SegSum.cons (w := 720) h120829 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S73
