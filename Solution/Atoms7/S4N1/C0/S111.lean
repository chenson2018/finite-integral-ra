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

namespace RACert.S4N1.C0.S111

open RACert RACert.Problem

theorem cover65535 : P.CoversSplit 24 10 65535 0xfffffffffffffffffffffffffffffffffffffffffffffafafffffffffffffafafffffffffffffffffffffffffffffffffffffffffffffafafffffffffffffafafffffffffffffffffffffffffffffffffffffffffafafafafffffffffafafafaffffffffffffffffffccffccffccffccffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1217, 1609]) (by decide +kernel)

noncomputable def f65535 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (67107840 + i)

theorem c65535_0 : rowSum f65535 0 167 = 328801528 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_1 : rowSum f65535 167 138 = 604443753 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_2 : rowSum f65535 305 150 = 673832248 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_3 : rowSum f65535 455 230 = 785075030 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_4 : rowSum f65535 685 338 = 1047692678 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_5 : rowSum f65535 1023 1 = 10017148 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem sum65535 : rowSum f65535 0 1024 = 3449862385 :=
  rowSum_append (F := f65535) (lo := 0) (n := 167) (m := 857) (A := 328801528) (B := 3121060857) c65535_0 (rowSum_append (F := f65535) (lo := 167) (n := 138) (m := 719) (A := 604443753) (B := 2516617104) c65535_1 (rowSum_append (F := f65535) (lo := 305) (n := 150) (m := 569) (A := 673832248) (B := 1842784856) c65535_2 (rowSum_append (F := f65535) (lo := 455) (n := 230) (m := 339) (A := 785075030) (B := 1057709826) c65535_3 (rowSum_append (F := f65535) (lo := 685) (n := 338) (m := 1) (A := 1047692678) (B := 10017148) c65535_4 (c65535_5)))))

theorem h65535 : P.leaf 34 65535 = 3449862385 :=
  leaf_weighted (k := 24) (d := 10) (H := 65535) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65535) (by decide) (by decide +kernel)) sum65535

def seg : List (ℕ × ℕ) := [(65535, 1)]

theorem segOK : checkSeg 16 perms 65535 65536 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 65535 65536 1 3449862385 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3449862385)
    (SegSum.cons (w := 1) h65535 (show SegSum (P.leaf 34) [] 0 from rfl)) (by decide)

end RACert.S4N1.C0.S111
