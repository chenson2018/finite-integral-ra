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

namespace S20

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(91583, 48), (91606, 48), (91607, 48), (91610, 48), (91611, 48), (91613, 24), (91614, 48), (91615, 48), (91621, 48), (91623, 48), (91625, 48), (91627, 48), (91629, 48), (91631, 48), (91637, 48), (91638, 48), (91639, 48), (91641, 48), (91642, 48), (91643, 48), (91645, 48), (91646, 48), (91647, 48), (91738, 24), (91739, 48), (91742, 48), (91743, 48), (91753, 8), (91755, 48), (91759, 24), (91771, 24), (91773, 48), (91774, 48), (91775, 48), (91798, 24), (91799, 48), (91807, 24), (91829, 48), (91830, 48), (91831, 48), (91837, 48), (91838, 48), (91839, 48), (91893, 48), (91894, 24), (91895, 48), (91897, 24), (91899, 48), (91903, 24), (91998, 24), (91999, 48), (92015, 48), (92031, 24), (92054, 48), (92055, 48), (92062, 48), (92063, 48), (92071, 48), (92079, 48), (92085, 24), (92086, 48), (92087, 48), (92093, 48), (92094, 48), (92095, 48), (92118, 48), (92119, 48), (92123, 48), (92126, 48), (92127, 48), (92139, 16), (92143, 48), (92150, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 432, 0, 418, 0, 418, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 438, 440, 574, 574, 0, 440, 537, 440, 664, 664, 664, 0, 581, 574, 581, 427, 581, 581, 581, 581, 1224, 427, 1224, 1224, 1224, 1224, 684, 684, 684, 684, 427, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(91583, 306), (91606, 34), (91607, 118), (91610, 26), (91611, 66), (91613, 93), (91614, 112), (91615, 168), (91623, 48), (91627, 48), (91631, 144), (91637, 100), (91638, 200), (91639, 324), (91642, 116), (91643, 216), (91645, 153), (91646, 357), (91647, 564), (91753, 8), (91798, 0), (92055, 60), (92062, 49), (92063, 210), (92071, 60), (92079, 152), (92085, 80), (92086, 96), (92087, 384), (92093, 216), (92094, 438), (92095, 680), (92118, 98), (92119, 208), (92123, 88), (92126, 328), (92127, 312), (92139, 64), (92143, 252), (92150, 380)]

theorem l91583 : P.leaf 18 91583 = 306 := by decide +kernel

theorem l91606 : P.leaf 18 91606 = 34 := by decide +kernel

theorem l91607 : P.leaf 18 91607 = 118 := by decide +kernel

theorem l91610 : P.leaf 18 91610 = 26 := by decide +kernel

theorem l91611 : P.leaf 18 91611 = 66 := by decide +kernel

theorem l91613 : P.leaf 18 91613 = 93 := by decide +kernel

theorem l91614 : P.leaf 18 91614 = 112 := by decide +kernel

theorem l91615 : P.leaf 18 91615 = 168 := by decide +kernel

theorem l91623 : P.leaf 18 91623 = 48 := by decide +kernel

theorem l91627 : P.leaf 18 91627 = 48 := by decide +kernel

theorem l91631 : P.leaf 18 91631 = 144 := by decide +kernel

theorem l91637 : P.leaf 18 91637 = 100 := by decide +kernel

theorem l91638 : P.leaf 18 91638 = 200 := by decide +kernel

theorem l91639 : P.leaf 18 91639 = 324 := by decide +kernel

theorem l91642 : P.leaf 18 91642 = 116 := by decide +kernel

theorem l91643 : P.leaf 18 91643 = 216 := by decide +kernel

theorem l91645 : P.leaf 18 91645 = 153 := by decide +kernel

theorem l91646 : P.leaf 18 91646 = 357 := by decide +kernel

theorem l91647 : P.leaf 18 91647 = 564 := by decide +kernel

theorem l91753 : P.leaf 18 91753 = 8 := by decide +kernel

theorem l91798 : P.leaf 18 91798 = 0 := by decide +kernel

theorem l92055 : P.leaf 18 92055 = 60 := by decide +kernel

theorem l92062 : P.leaf 18 92062 = 49 := by decide +kernel

theorem l92063 : P.leaf 18 92063 = 210 := by decide +kernel

theorem l92071 : P.leaf 18 92071 = 60 := by decide +kernel

theorem l92079 : P.leaf 18 92079 = 152 := by decide +kernel

theorem l92085 : P.leaf 18 92085 = 80 := by decide +kernel

theorem l92086 : P.leaf 18 92086 = 96 := by decide +kernel

theorem l92087 : P.leaf 18 92087 = 384 := by decide +kernel

theorem l92093 : P.leaf 18 92093 = 216 := by decide +kernel

theorem l92094 : P.leaf 18 92094 = 438 := by decide +kernel

theorem l92095 : P.leaf 18 92095 = 680 := by decide +kernel

theorem l92118 : P.leaf 18 92118 = 98 := by decide +kernel

theorem l92119 : P.leaf 18 92119 = 208 := by decide +kernel

theorem l92123 : P.leaf 18 92123 = 88 := by decide +kernel

theorem l92126 : P.leaf 18 92126 = 328 := by decide +kernel

theorem l92127 : P.leaf 18 92127 = 312 := by decide +kernel

theorem l92139 : P.leaf 18 92139 = 64 := by decide +kernel

theorem l92143 : P.leaf 18 92143 = 252 := by decide +kernel

theorem l92150 : P.leaf 18 92150 = 380 := by decide +kernel

theorem segOK : checkSeg 20 perms 91583 92151 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 346568 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 91583 92151 3144 346568 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l91583 (.cons l91606 (.cons l91607 (.cons l91610 (.cons l91611 (.cons l91613 (.cons l91614 (.cons l91615 (.cons l91623 (.cons l91627 (.cons l91631 (.cons l91637 (.cons l91638 (.cons l91639 (.cons l91642 (.cons l91643 (.cons l91645 (.cons l91646 (.cons l91647 (.cons l91753 (.cons l91798 (.cons l92055 (.cons l92062 (.cons l92063 (.cons l92071 (.cons l92079 (.cons l92085 (.cons l92086 (.cons l92087 (.cons l92093 (.cons l92094 (.cons l92095 (.cons l92118 (.cons l92119 (.cons l92123 (.cons l92126 (.cons l92127 (.cons l92139 (.cons l92143 (.cons l92150 (.nil))))))))))))))))))))))))))))))))))))))))))

end S20

end RACert.S0N3.C0
