/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S26

open RACert RACert.Problem

theorem cover4094 : P.CoversSplit 24 10 4094 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaa88aa88ffccffccaa88aa88ffffffffaa88aa88ffccffccaa88aa88ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaffffffffaa88aa88ffccffccaa88aa88ffccffccaa88aa88ffccffccaa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 915, 1209, 1217, 1258, 1609]) (by decide +kernel)

theorem c4094_0 : P.sumLeaves 24 4192256 178 = 6309642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 0) (len := 178) (W := 6309642) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_1 : P.sumLeaves 24 4192434 130 = 15581621 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 178) (len := 130) (W := 15581621) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_2 : P.sumLeaves 24 4192564 116 = 28392333 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 308) (len := 116) (W := 28392333) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_3 : P.sumLeaves 24 4192680 128 = 52463505 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 424) (len := 128) (W := 52463505) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_4 : P.sumLeaves 24 4192808 148 = 31162342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 552) (len := 148) (W := 31162342) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_5 : P.sumLeaves 24 4192956 124 = 52860930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 700) (len := 124) (W := 52860930) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_6 : P.sumLeaves 24 4193080 112 = 83025767 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 824) (len := 112) (W := 83025767) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem c4094_7 : P.sumLeaves 24 4193192 88 = 132202148 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4094) (lo := 936) (len := 88) (W := 132202148) check rows elimOK (by decide) (by decide) cover4094 (by decide)
  decide +kernel

theorem h4094 : P.leaf 34 4094 = 401998288 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(178, 6309642), (130, 15581621), (116, 28392333), (128, 52463505), (148, 31162342), (124, 52860930), (112, 83025767), (88, 132202148)]) (.cons c4094_0 (.cons c4094_1 (.cons c4094_2 (.cons c4094_3 (.cons c4094_4 (.cons c4094_5 (.cons c4094_6 (.cons c4094_7 (.nil))))))))) (by decide) (by decide))

theorem cover4095 : P.CoversSplit 24 10 4095 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaa88aa88ffccffccaa88aa88ffffffffaa88aa88ffccffccaa88aa88ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaffffffffaa88aa88ffccffccaa88aa88ffccffccaa88aa88ffccffccaa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [915, 1209, 1217, 1258, 1609]) (by decide +kernel)

theorem c4095_0 : P.sumLeaves 24 4193280 178 = 18440347 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 0) (len := 178) (W := 18440347) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_1 : P.sumLeaves 24 4193458 130 = 38838856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 178) (len := 130) (W := 38838856) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_2 : P.sumLeaves 24 4193588 116 = 65077191 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 308) (len := 116) (W := 65077191) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_3 : P.sumLeaves 24 4193704 128 = 101386164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 424) (len := 128) (W := 101386164) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_4 : P.sumLeaves 24 4193832 148 = 81647635 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 552) (len := 148) (W := 81647635) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_5 : P.sumLeaves 24 4193980 124 = 123161112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 700) (len := 124) (W := 123161112) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_6 : P.sumLeaves 24 4194104 112 = 180757347 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 824) (len := 112) (W := 180757347) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem c4095_7 : P.sumLeaves 24 4194216 88 = 240042354 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4095) (lo := 936) (len := 88) (W := 240042354) check rows elimOK (by decide) (by decide) cover4095 (by decide)
  decide +kernel

theorem h4095 : P.leaf 34 4095 = 849351006 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(178, 18440347), (130, 38838856), (116, 65077191), (128, 101386164), (148, 81647635), (124, 123161112), (112, 180757347), (88, 240042354)]) (.cons c4095_0 (.cons c4095_1 (.cons c4095_2 (.cons c4095_3 (.cons c4095_4 (.cons c4095_5 (.cons c4095_6 (.cons c4095_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(4094, 12), (4095, 12)]

theorem segOK : checkSeg 16 perms 4094 5280 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 4094 5280 24 15016191528 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 15016191528)
    (SegSum.cons (w := 12) h4094 (SegSum.cons (w := 12) h4095 (show SegSum (P.leaf 34) [] 0 from rfl))) (by decide)

end RACert.S4N1.C0.S26
