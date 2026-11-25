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

namespace S82

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(243582, 48), (243583, 48), (243586, 48), (243587, 48), (243590, 48), (243591, 48), (243594, 48), (243595, 48), (243598, 48), (243599, 48), (243602, 48), (243603, 48), (243606, 48), (243607, 48), (243610, 48), (243611, 48), (243614, 48), (243615, 48), (243618, 48), (243619, 48), (243622, 48), (243623, 48), (243626, 48), (243627, 48), (243630, 48), (243631, 48), (243634, 48), (243635, 48), (243637, 24), (243638, 48), (243639, 48), (243642, 48), (243643, 48), (243645, 48), (243646, 48), (243647, 48), (243650, 48), (243651, 48), (243654, 48), (243655, 48), (243658, 48), (243659, 48), (243662, 48), (243663, 48), (243666, 48), (243667, 48), (243670, 48), (243671, 48), (243674, 48), (243675, 48), (243678, 48), (243679, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 424, 0, 424, 0, 424, 0, 0, 0, 424, 0, 424, 0, 424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 424, 0, 424, 0, 424, 0, 0, 0, 424, 0, 424, 0, 424, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(243582, 386), (243583, 2062), (243586, 6), (243587, 82), (243591, 937), (243595, 391), (243599, 1544), (243602, 0), (243603, 122), (243607, 1265), (243611, 566), (243615, 2271), (243618, 78), (243619, 252), (243622, 681), (243623, 2076), (243626, 316), (243627, 924), (243630, 1144), (243631, 3414), (243634, 138), (243635, 368), (243637, 2112), (243638, 1182), (243639, 3582), (243642, 476), (243643, 1232), (243645, 2660), (243646, 1686), (243647, 5414), (243650, 24), (243651, 124), (243655, 1463), (243659, 411), (243663, 1856), (243666, 77), (243667, 190), (243671, 2058), (243675, 670), (243679, 2906)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 243582 243682 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2212320 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 243582 243682 2472 2212320 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S82

end RACert.S0N3.C0
