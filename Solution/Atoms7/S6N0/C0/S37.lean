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

namespace RACert.S6N0.C0.S37

open RACert RACert.Problem

theorem cover227820 : P.CoversSplit 26 10 227820 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h227820 : P.leaf 36 227820 = 15610148 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 227820) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 227820) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 227820) (weight := rowWeight keep0 twice0) (xs := [256, 341, 512, 682, 768, 1023]) check rows elimOK (by decide) (by decide) cover227820 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h65520 : P.leaf 36 65520 = 15610148 :=
  orient348 (v := 227820) (by decide) (by decide +kernel) h227820

theorem cover228332 : P.CoversSplit 26 10 228332 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228332 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (233811968 + i)

theorem c228332_0 : rowSum f228332 0 375 = 80535052 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228332) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228332 (by decide)
  decide +kernel

theorem c228332_1 : rowSum f228332 375 102 = 136072398 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228332) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228332 (by decide)
  decide +kernel

theorem c228332_2 : rowSum f228332 477 394 = 281100072 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228332) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228332 (by decide)
  decide +kernel

theorem c228332_3 : rowSum f228332 871 153 = 343791888 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228332) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228332 (by decide)
  decide +kernel

theorem sum228332 : rowSum f228332 0 1024 = 841499410 :=
  rowSum_append (F := f228332) (lo := 0) (n := 375) (m := 649) (A := 80535052) (B := 760964358) c228332_0 (rowSum_append (F := f228332) (lo := 375) (n := 102) (m := 547) (A := 136072398) (B := 624891960) c228332_1 (rowSum_append (F := f228332) (lo := 477) (n := 394) (m := 153) (A := 281100072) (B := 343791888) c228332_2 (c228332_3)))

theorem h228332 : P.leaf 36 228332 = 841499410 :=
  leaf_weighted (k := 26) (d := 10) (H := 228332) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 228332) (by decide) (by decide +kernel)) sum228332

theorem h65521 : P.leaf 36 65521 = 841499410 :=
  orient348 (v := 228332) (by decide) (by decide +kernel) h228332

theorem cover261100 : P.CoversSplit 26 10 261100 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f261100 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (267366400 + i)

theorem c261100_0 : rowSum f261100 0 375 = 200573816 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261100) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261100 (by decide)
  decide +kernel

theorem c261100_1 : rowSum f261100 375 100 = 305707976 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261100) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261100 (by decide)
  decide +kernel

theorem c261100_2 : rowSum f261100 475 392 = 622089544 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261100) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261100 (by decide)
  decide +kernel

theorem c261100_3 : rowSum f261100 867 157 = 687351616 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 261100) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover261100 (by decide)
  decide +kernel

theorem sum261100 : rowSum f261100 0 1024 = 1815722952 :=
  rowSum_append (F := f261100) (lo := 0) (n := 375) (m := 649) (A := 200573816) (B := 1615149136) c261100_0 (rowSum_append (F := f261100) (lo := 375) (n := 100) (m := 549) (A := 305707976) (B := 1309441160) c261100_1 (rowSum_append (F := f261100) (lo := 475) (n := 392) (m := 157) (A := 622089544) (B := 687351616) c261100_2 (c261100_3)))

theorem h261100 : P.leaf 36 261100 = 1815722952 :=
  leaf_weighted (k := 26) (d := 10) (H := 261100) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 261100) (by decide) (by decide +kernel)) sum261100

theorem h65523 : P.leaf 36 65523 = 1815722952 :=
  orient348 (v := 261100) (by decide) (by decide +kernel) h261100

theorem cover65533 : P.CoversSplit 26 10 65533 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f65533 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (67105792 + i)

theorem c65533_0 : rowSum f65533 0 268 = 472054600 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65533 (by decide)
  decide +kernel

theorem c65533_1 : rowSum f65533 268 147 = 847184416 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65533 (by decide)
  decide +kernel

theorem c65533_2 : rowSum f65533 415 384 = 1372133016 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65533 (by decide)
  decide +kernel

theorem c65533_3 : rowSum f65533 799 225 = 1268454632 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65533) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65533 (by decide)
  decide +kernel

theorem sum65533 : rowSum f65533 0 1024 = 3959826664 :=
  rowSum_append (F := f65533) (lo := 0) (n := 268) (m := 756) (A := 472054600) (B := 3487772064) c65533_0 (rowSum_append (F := f65533) (lo := 268) (n := 147) (m := 609) (A := 847184416) (B := 2640587648) c65533_1 (rowSum_append (F := f65533) (lo := 415) (n := 384) (m := 225) (A := 1372133016) (B := 1268454632) c65533_2 (c65533_3)))

theorem h65533 : P.leaf 36 65533 = 3959826664 :=
  leaf_weighted (k := 26) (d := 10) (H := 65533) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65533) (by decide) (by decide +kernel)) sum65533

theorem h65527 : P.leaf 36 65527 = 3959826664 :=
  orient6 (v := 65533) (by decide) (by decide +kernel) h65533

theorem cover65535 : P.CoversSplit 26 10 65535 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f65535 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (67107840 + i)

theorem c65535_0 : rowSum f65535 0 268 = 1993478328 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_1 : rowSum f65535 268 147 = 2684633412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_2 : rowSum f65535 415 384 = 2993507876 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_3 : rowSum f65535 799 225 = 2865275576 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem sum65535 : rowSum f65535 0 1024 = 10536895192 :=
  rowSum_append (F := f65535) (lo := 0) (n := 268) (m := 756) (A := 1993478328) (B := 8543416864) c65535_0 (rowSum_append (F := f65535) (lo := 268) (n := 147) (m := 609) (A := 2684633412) (B := 5858783452) c65535_1 (rowSum_append (F := f65535) (lo := 415) (n := 384) (m := 225) (A := 2993507876) (B := 2865275576) c65535_2 (c65535_3)))

theorem h65535 : P.leaf 36 65535 = 10536895192 :=
  leaf_weighted (k := 26) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65535) (by decide) (by decide +kernel)) sum65535

def seg : List (ℕ × ℕ) := [(65520, 15), (65521, 60), (65523, 90), (65527, 60), (65535, 15)]

theorem segOK : checkSeg 20 perms 65520 76983 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 65520 76983 240 609782210220 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 609782210220)
    (SegSum.cons (w := 15) h65520 (SegSum.cons (w := 60) h65521 (SegSum.cons (w := 90) h65523 (SegSum.cons (w := 60) h65527 (SegSum.cons (w := 15) h65535 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S37
