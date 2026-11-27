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

namespace RACert.S4N1.C0.S67

open RACert RACert.Problem

theorem cover16375 : P.CoversSplit 24 10 16375 0xfffffffffffffafafffffffffffffafafffffffffffffafafffffffffffffafafffffffffac8fac8ffccffccfac8fac8fffffffffac8fac8ffccffccfac8fac8fffffffffffffafafffffffffffffafafffffffffafafafafffffffffafafafafffffffffac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f16375 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16768000 + i)

theorem c16375_0 : rowSum f16375 0 173 = 48388056 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem c16375_1 : rowSum f16375 173 201 = 116670834 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem c16375_2 : rowSum f16375 374 109 = 218358544 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem c16375_3 : rowSum f16375 483 275 = 332032036 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem c16375_4 : rowSum f16375 758 266 = 264778100 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16375 (by decide)
  decide +kernel

theorem sum16375 : rowSum f16375 0 1024 = 980227570 :=
  rowSum_append (F := f16375) (lo := 0) (n := 173) (m := 851) (A := 48388056) (B := 931839514) c16375_0 (rowSum_append (F := f16375) (lo := 173) (n := 201) (m := 650) (A := 116670834) (B := 815168680) c16375_1 (rowSum_append (F := f16375) (lo := 374) (n := 109) (m := 541) (A := 218358544) (B := 596810136) c16375_2 (rowSum_append (F := f16375) (lo := 483) (n := 275) (m := 266) (A := 332032036) (B := 264778100) c16375_3 (c16375_4))))

theorem h16375 : P.leaf 34 16375 = 980227570 :=
  leaf_weighted (k := 24) (d := 10) (H := 16375) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 16375) (by decide) (by decide +kernel)) sum16375

theorem cover16380 : P.CoversSplit 24 10 16380 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473]) (by decide +kernel)

noncomputable def f16380 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16773120 + i)

theorem c16380_0 : rowSum f16380 0 173 = 22280862 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16380) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16380 (by decide)
  decide +kernel

theorem c16380_1 : rowSum f16380 173 216 = 73193574 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16380) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16380 (by decide)
  decide +kernel

theorem c16380_2 : rowSum f16380 389 110 = 135079616 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16380) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16380 (by decide)
  decide +kernel

theorem c16380_3 : rowSum f16380 499 449 = 185475904 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16380) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16380 (by decide)
  decide +kernel

theorem c16380_4 : rowSum f16380 948 76 = 98492132 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16380) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16380 (by decide)
  decide +kernel

theorem sum16380 : rowSum f16380 0 1024 = 514522088 :=
  rowSum_append (F := f16380) (lo := 0) (n := 173) (m := 851) (A := 22280862) (B := 492241226) c16380_0 (rowSum_append (F := f16380) (lo := 173) (n := 216) (m := 635) (A := 73193574) (B := 419047652) c16380_1 (rowSum_append (F := f16380) (lo := 389) (n := 110) (m := 525) (A := 135079616) (B := 283968036) c16380_2 (rowSum_append (F := f16380) (lo := 499) (n := 449) (m := 76) (A := 185475904) (B := 98492132) c16380_3 (c16380_4))))

theorem h16380 : P.leaf 34 16380 = 514522088 :=
  leaf_weighted (k := 24) (d := 10) (H := 16380) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 16380) (by decide) (by decide +kernel)) sum16380

theorem cover16381 : P.CoversSplit 24 10 16381 0xfffffffffffffafafffffffffffffafafffffffffffffafafffffffffffffafafffffffffac8fac8ffccffccfac8fac8fffffffffac8fac8ffccffccfac8fac8fffffffffffffafafffffffffffffafafffffffffafafafafffffffffafafafafffffffffac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f16381 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (16774144 + i)

theorem c16381_0 : rowSum f16381 0 245 = 79028702 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover16381 (by decide)
  decide +kernel

theorem c16381_1 : rowSum f16381 245 177 = 106263650 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover16381 (by decide)
  decide +kernel

theorem c16381_2 : rowSum f16381 422 202 = 190978104 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover16381 (by decide)
  decide +kernel

theorem c16381_3 : rowSum f16381 624 198 = 237058844 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover16381 (by decide)
  decide +kernel

theorem c16381_4 : rowSum f16381 822 170 = 285069022 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover16381 (by decide)
  decide +kernel

theorem c16381_5 : rowSum f16381 992 32 = 122024800 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover16381 (by decide)
  decide +kernel

theorem sum16381 : rowSum f16381 0 1024 = 1020423122 :=
  rowSum_append (F := f16381) (lo := 0) (n := 245) (m := 779) (A := 79028702) (B := 941394420) c16381_0 (rowSum_append (F := f16381) (lo := 245) (n := 177) (m := 602) (A := 106263650) (B := 835130770) c16381_1 (rowSum_append (F := f16381) (lo := 422) (n := 202) (m := 400) (A := 190978104) (B := 644152666) c16381_2 (rowSum_append (F := f16381) (lo := 624) (n := 198) (m := 202) (A := 237058844) (B := 407093822) c16381_3 (rowSum_append (F := f16381) (lo := 822) (n := 170) (m := 32) (A := 285069022) (B := 122024800) c16381_4 (c16381_5)))))

theorem h16381 : P.leaf 34 16381 = 1020423122 :=
  leaf_weighted (k := 24) (d := 10) (H := 16381) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 16381) (by decide) (by decide +kernel)) sum16381

theorem cover16383 : P.CoversSplit 24 10 16383 0xfffffffffffffafafffffffffffffafafffffffffffffafafffffffffffffafafffffffffac8fac8ffccffccfac8fac8fffffffffac8fac8ffccffccfac8fac8fffffffffffffafafffffffffffffafafffffffffafafafafffffffffafafafafffffffffac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f16383 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16776192 + i)

theorem c16383_0 : rowSum f16383 0 173 = 201215250 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_1 : rowSum f16383 173 201 = 343554458 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_2 : rowSum f16383 374 109 = 417010060 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_3 : rowSum f16383 483 275 = 592831626 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_4 : rowSum f16383 758 266 = 401641260 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem sum16383 : rowSum f16383 0 1024 = 1956252654 :=
  rowSum_append (F := f16383) (lo := 0) (n := 173) (m := 851) (A := 201215250) (B := 1755037404) c16383_0 (rowSum_append (F := f16383) (lo := 173) (n := 201) (m := 650) (A := 343554458) (B := 1411482946) c16383_1 (rowSum_append (F := f16383) (lo := 374) (n := 109) (m := 541) (A := 417010060) (B := 994472886) c16383_2 (rowSum_append (F := f16383) (lo := 483) (n := 275) (m := 266) (A := 592831626) (B := 401641260) c16383_3 (c16383_4))))

theorem h16383 : P.leaf 34 16383 = 1956252654 :=
  leaf_weighted (k := 24) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 16383) (by decide) (by decide +kernel)) sum16383

def seg : List (ℕ × ℕ) := [(16375, 12), (16380, 6), (16381, 12), (16383, 6)]

theorem segOK : checkSeg 16 perms 16375 21668 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 16375 21668 36 38832456756 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 38832456756)
    (SegSum.cons (w := 12) h16375 (SegSum.cons (w := 6) h16380 (SegSum.cons (w := 12) h16381 (SegSum.cons (w := 6) h16383 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S67
