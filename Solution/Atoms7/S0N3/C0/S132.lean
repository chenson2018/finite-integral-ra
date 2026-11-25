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

namespace S132

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(521215, 48), (521557, 48), (521558, 24), (521559, 48), (521561, 24), (521562, 48), (521563, 48), (521565, 48), (521566, 48), (521567, 48), (521573, 24), (521575, 48), (521577, 48), (521578, 48), (521579, 48), (521581, 48), (521582, 48), (521583, 48), (521591, 24), (521593, 48), (521594, 48), (521595, 48), (521597, 48), (521598, 48), (521599, 48), (521621, 24), (521622, 48), (521623, 48), (521626, 48), (521627, 48), (521629, 48), (521630, 48), (521631, 48), (521637, 48), (521639, 48), (521642, 16), (521643, 48), (521645, 48), (521646, 48), (521647, 48), (521653, 48), (521654, 48), (521655, 48), (521659, 48), (521661, 48), (521662, 48), (521663, 48), (521686, 48), (521687, 48), (521690, 48), (521691, 48), (521693, 24), (521694, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 650, 650, 650, 0, 0, 0, 502, 0, 439, 650, 650, 502, 0, 0, 0, 650, 650, 650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(521215, 12972), (521557, 2027), (521558, 1608), (521559, 3956), (521565, 2681), (521566, 2185), (521567, 5001), (521575, 2955), (521582, 2930), (521583, 3577), (521591, 6455), (521597, 3673), (521598, 5121), (521599, 8782), (521621, 2472), (521622, 1724), (521623, 4239), (521626, 1835), (521627, 3909), (521629, 3898), (521630, 3442), (521631, 8007), (521639, 2710), (521642, 2230), (521643, 2940), (521646, 4364), (521647, 5498), (521653, 3454), (521654, 4618), (521655, 7099), (521659, 6145), (521661, 5357), (521662, 7813), (521663, 13454), (521686, 4016), (521687, 6829), (521690, 2494), (521691, 4797), (521693, 5347), (521694, 5325)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 521215 521695 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 8568544 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 521215 521695 2368 8568544 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S132

end RACert.S0N3.C0
