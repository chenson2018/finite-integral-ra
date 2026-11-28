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

namespace RACert.S6N0.C0.S79

open RACert RACert.Problem

theorem cover227821 : P.CoversSplit 26 10 227821 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h227821 : P.leaf 36 227821 = 16853208 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 227821) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 227821) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 227821) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover227821 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h131056 : P.leaf 36 131056 = 16853208 :=
  orient348 (v := 227821) (by decide) (by decide +kernel) h227821

theorem cover228333 : P.CoversSplit 26 10 228333 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228333 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (233812992 + i)

theorem c228333_0 : rowSum f228333 0 375 = 194970260 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228333) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228333 (by decide)
  decide +kernel

theorem c228333_1 : rowSum f228333 375 102 = 368999754 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228333) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228333 (by decide)
  decide +kernel

theorem c228333_2 : rowSum f228333 477 394 = 683120020 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228333) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228333 (by decide)
  decide +kernel

theorem c228333_3 : rowSum f228333 871 153 = 775629560 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228333) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228333 (by decide)
  decide +kernel

theorem sum228333 : rowSum f228333 0 1024 = 2022719594 :=
  rowSum_append (F := f228333) (lo := 0) (n := 375) (m := 649) (A := 194970260) (B := 1827749334) c228333_0 (rowSum_append (F := f228333) (lo := 375) (n := 102) (m := 547) (A := 368999754) (B := 1458749580) c228333_1 (rowSum_append (F := f228333) (lo := 477) (n := 394) (m := 153) (A := 683120020) (B := 775629560) c228333_2 (c228333_3)))

theorem h228333 : P.leaf 36 228333 = 2022719594 :=
  leaf_weighted (k := 26) (d := 10) (H := 228333) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 228333) (by decide) (by decide +kernel)) sum228333

theorem h131057 : P.leaf 36 131057 = 2022719594 :=
  orient348 (v := 228333) (by decide) (by decide +kernel) h228333

theorem cover261101 : P.CoversSplit 26 10 261101 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261101 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (267367424 + i)

theorem c261101_0 : rowSum f261101 0 375 = 440419632 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261101) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261101 (by decide)
  decide +kernel

theorem c261101_1 : rowSum f261101 375 100 = 749608434 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261101) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261101 (by decide)
  decide +kernel

theorem c261101_2 : rowSum f261101 475 392 = 1207132772 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261101) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261101 (by decide)
  decide +kernel

theorem c261101_3 : rowSum f261101 867 157 = 1227134760 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261101) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261101 (by decide)
  decide +kernel

theorem sum261101 : rowSum f261101 0 1024 = 3624295598 :=
  rowSum_append (F := f261101) (lo := 0) (n := 375) (m := 649) (A := 440419632) (B := 3183875966) c261101_0 (rowSum_append (F := f261101) (lo := 375) (n := 100) (m := 549) (A := 749608434) (B := 2434267532) c261101_1 (rowSum_append (F := f261101) (lo := 475) (n := 392) (m := 157) (A := 1207132772) (B := 1227134760) c261101_2 (c261101_3)))

theorem h261101 : P.leaf 36 261101 = 3624295598 :=
  leaf_weighted (k := 26) (d := 10) (H := 261101) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 261101) (by decide) (by decide +kernel)) sum261101

theorem h131059 : P.leaf 36 131059 = 3624295598 :=
  orient348 (v := 261101) (by decide) (by decide +kernel) h261101

theorem cover327677 : P.CoversSplit 26 10 327677 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffffffafafffffafaffccffccffccffccfac8fac8fac8fac8fffffffffffffffffafafafafafafafaffccffccffccffccfac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f327677 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (335541248 + i)

theorem c327677_0 : rowSum f327677 0 241 = 918939654 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327677) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327677 (by decide)
  decide +kernel

theorem c327677_1 : rowSum f327677 241 148 = 1110670456 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327677) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327677 (by decide)
  decide +kernel

theorem c327677_2 : rowSum f327677 389 102 = 1455002676 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327677) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327677 (by decide)
  decide +kernel

theorem c327677_3 : rowSum f327677 491 403 = 1612518172 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327677) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327677 (by decide)
  decide +kernel

theorem c327677_4 : rowSum f327677 894 130 = 983201012 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 327677) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover327677 (by decide)
  decide +kernel

theorem sum327677 : rowSum f327677 0 1024 = 6080331970 :=
  rowSum_append (F := f327677) (lo := 0) (n := 241) (m := 783) (A := 918939654) (B := 5161392316) c327677_0 (rowSum_append (F := f327677) (lo := 241) (n := 148) (m := 635) (A := 1110670456) (B := 4050721860) c327677_1 (rowSum_append (F := f327677) (lo := 389) (n := 102) (m := 533) (A := 1455002676) (B := 2595719184) c327677_2 (rowSum_append (F := f327677) (lo := 491) (n := 403) (m := 130) (A := 1612518172) (B := 983201012) c327677_3 (c327677_4))))

theorem h327677 : P.leaf 36 327677 = 6080331970 :=
  leaf_weighted (k := 26) (d := 10) (H := 327677) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 327677) (by decide) (by decide +kernel)) sum327677

theorem h131063 : P.leaf 36 131063 = 6080331970 :=
  orient6 (v := 327677) (by decide) (by decide +kernel) h327677

theorem cover752109 : P.CoversSplit 26 10 752109 0xfffffffffffffffffffffefafffffafaffffffffffecffccfffffefaffecfac8fffffffffffffffffffffafafffffafaffffffffffecffccfffffafaffecfac8fffffffffffffffffffffefafffffafaffffffffffccffccfffffefaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 972, 979, 1315, 1322]) (by decide +kernel)

noncomputable def f752109 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (770159616 + i)

theorem c752109_0 : rowSum f752109 0 374 = 281448954 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 752109) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover752109 (by decide)
  decide +kernel

theorem c752109_1 : rowSum f752109 374 103 = 418658748 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 752109) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover752109 (by decide)
  decide +kernel

theorem c752109_2 : rowSum f752109 477 394 = 871050312 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 752109) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover752109 (by decide)
  decide +kernel

theorem c752109_3 : rowSum f752109 871 153 = 756012252 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 752109) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover752109 (by decide)
  decide +kernel

theorem sum752109 : rowSum f752109 0 1024 = 2327170266 :=
  rowSum_append (F := f752109) (lo := 0) (n := 374) (m := 650) (A := 281448954) (B := 2045721312) c752109_0 (rowSum_append (F := f752109) (lo := 374) (n := 103) (m := 547) (A := 418658748) (B := 1627062564) c752109_1 (rowSum_append (F := f752109) (lo := 477) (n := 394) (m := 153) (A := 871050312) (B := 756012252) c752109_2 (c752109_3)))

theorem h752109 : P.leaf 36 752109 = 2327170266 :=
  leaf_weighted (k := 26) (d := 10) (H := 752109) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 752109) (by decide) (by decide +kernel)) sum752109

theorem h131064 : P.leaf 36 131064 = 2327170266 :=
  orient348 (v := 752109) (by decide) (by decide +kernel) h752109

def seg : List (ℕ × ℕ) := [(131056, 60), (131057, 180), (131059, 180), (131063, 60), (131064, 60)]

theorem segOK : checkSeg 20 perms 131056 131065 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131056 131065 540 1521924061200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1521924061200)
    (SegSum.cons (w := 60) h131056 (SegSum.cons (w := 180) h131057 (SegSum.cons (w := 180) h131059 (SegSum.cons (w := 60) h131063 (SegSum.cons (w := 60) h131064 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S79
