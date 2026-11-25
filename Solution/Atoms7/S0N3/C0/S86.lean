/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace S86

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(244459, 48), (244462, 24), (244463, 48), (244466, 48), (244467, 48), (244470, 48), (244471, 48), (244474, 48), (244475, 48), (244478, 48), (244479, 48), (244483, 48), (244487, 48), (244491, 48), (244495, 48), (244499, 48), (244503, 48), (244507, 48), (244511, 48), (244515, 48), (244519, 48), (244523, 48), (244527, 48), (244530, 24), (244531, 48), (244534, 48), (244535, 48), (244538, 48), (244539, 48), (244542, 48), (244543, 48), (244547, 48), (244551, 48), (244555, 48), (244559, 48), (244563, 48), (244567, 48), (244571, 48), (244575, 48), (244579, 48), (244583, 48), (244587, 48), (244591, 48), (244595, 48), (244598, 48), (244599, 48), (244602, 24), (244603, 48), (244606, 48), (244607, 48), (244611, 48), (244615, 48), (244619, 48), (244623, 48), (244627, 48), (244631, 48), (244635, 48), (244639, 48), (244643, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 438, 440, 0, 0, 438, 440, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 0, 438, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(244459, 348), (244462, 429), (244463, 1576), (244466, 125), (244467, 144), (244470, 637), (244471, 1999), (244474, 205), (244475, 571), (244478, 746), (244479, 2776), (244487, 129), (244495, 172), (244503, 132), (244511, 176), (244519, 324), (244527, 426), (244534, 120), (244535, 572), (244542, 152), (244543, 688), (244551, 354), (244559, 472), (244567, 570), (244575, 717), (244583, 759), (244591, 931), (244598, 208), (244599, 1274), (244606, 260), (244607, 1480), (244611, 36), (244615, 710), (244619, 215), (244623, 1172), (244627, 42), (244631, 924), (244635, 264), (244639, 1532), (244643, 84)]

theorem l244459 : P.leaf 18 244459 = 348 := by decide +kernel

theorem l244462 : P.leaf 18 244462 = 429 := by decide +kernel

theorem l244463 : P.leaf 18 244463 = 1576 := by decide +kernel

theorem l244466 : P.leaf 18 244466 = 125 := by decide +kernel

theorem l244467 : P.leaf 18 244467 = 144 := by decide +kernel

theorem l244470 : P.leaf 18 244470 = 637 := by decide +kernel

theorem l244471 : P.leaf 18 244471 = 1999 := by decide +kernel

theorem l244474 : P.leaf 18 244474 = 205 := by decide +kernel

theorem l244475 : P.leaf 18 244475 = 571 := by decide +kernel

theorem l244478 : P.leaf 18 244478 = 746 := by decide +kernel

theorem l244479 : P.leaf 18 244479 = 2776 := by decide +kernel

theorem l244487 : P.leaf 18 244487 = 129 := by decide +kernel

theorem l244495 : P.leaf 18 244495 = 172 := by decide +kernel

theorem l244503 : P.leaf 18 244503 = 132 := by decide +kernel

theorem l244511 : P.leaf 18 244511 = 176 := by decide +kernel

theorem l244519 : P.leaf 18 244519 = 324 := by decide +kernel

theorem l244527 : P.leaf 18 244527 = 426 := by decide +kernel

theorem l244534 : P.leaf 18 244534 = 120 := by decide +kernel

theorem l244535 : P.leaf 18 244535 = 572 := by decide +kernel

theorem l244542 : P.leaf 18 244542 = 152 := by decide +kernel

theorem l244543 : P.leaf 18 244543 = 688 := by decide +kernel

theorem l244551 : P.leaf 18 244551 = 354 := by decide +kernel

theorem l244559 : P.leaf 18 244559 = 472 := by decide +kernel

theorem l244567 : P.leaf 18 244567 = 570 := by decide +kernel

theorem l244575 : P.leaf 18 244575 = 717 := by decide +kernel

theorem l244583 : P.leaf 18 244583 = 759 := by decide +kernel

theorem l244591 : P.leaf 18 244591 = 931 := by decide +kernel

theorem l244598 : P.leaf 18 244598 = 208 := by decide +kernel

theorem l244599 : P.leaf 18 244599 = 1274 := by decide +kernel

theorem l244606 : P.leaf 18 244606 = 260 := by decide +kernel

theorem l244607 : P.leaf 18 244607 = 1480 := by decide +kernel

theorem l244611 : P.leaf 18 244611 = 36 := by decide +kernel

theorem l244615 : P.leaf 18 244615 = 710 := by decide +kernel

theorem l244619 : P.leaf 18 244619 = 215 := by decide +kernel

theorem l244623 : P.leaf 18 244623 = 1172 := by decide +kernel

theorem l244627 : P.leaf 18 244627 = 42 := by decide +kernel

theorem l244631 : P.leaf 18 244631 = 924 := by decide +kernel

theorem l244635 : P.leaf 18 244635 = 264 := by decide +kernel

theorem l244639 : P.leaf 18 244639 = 1532 := by decide +kernel

theorem l244643 : P.leaf 18 244643 = 84 := by decide +kernel

theorem segOK : checkSeg 20 perms 244459 244647 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1163352 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 244459 244647 2760 1163352 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l244459 (.cons l244462 (.cons l244463 (.cons l244466 (.cons l244467 (.cons l244470 (.cons l244471 (.cons l244474 (.cons l244475 (.cons l244478 (.cons l244479 (.cons l244487 (.cons l244495 (.cons l244503 (.cons l244511 (.cons l244519 (.cons l244527 (.cons l244534 (.cons l244535 (.cons l244542 (.cons l244543 (.cons l244551 (.cons l244559 (.cons l244567 (.cons l244575 (.cons l244583 (.cons l244591 (.cons l244598 (.cons l244599 (.cons l244606 (.cons l244607 (.cons l244611 (.cons l244615 (.cons l244619 (.cons l244623 (.cons l244627 (.cons l244631 (.cons l244635 (.cons l244639 (.cons l244643 (.nil))))))))))))))))))))))))))))))))))))))))))

end S86

end RACert.S0N3.C0
