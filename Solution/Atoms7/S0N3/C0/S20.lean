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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 91583 92151 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 346568 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 91583 92151 3144 346568 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S20

end RACert.S0N3.C0
