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

namespace S125

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(517563, 24), (517565, 24), (517566, 24), (517567, 24), (517590, 24), (517591, 24), (517594, 24), (517595, 24), (517597, 12), (517598, 24), (517599, 24), (517605, 24), (517607, 24), (517609, 24), (517611, 24), (517613, 24), (517615, 24), (517621, 24), (517622, 24), (517623, 24), (517625, 24), (517626, 24), (517627, 24), (517629, 24), (517630, 24), (517631, 24), (517722, 12), (517723, 24), (517726, 24), (517727, 24), (517737, 4), (517739, 24), (517743, 12), (517755, 12), (517757, 24), (517758, 24), (517759, 24), (517782, 12), (517783, 24), (517791, 12), (517813, 24), (517814, 24), (517815, 24), (517821, 24), (517822, 24), (517823, 24), (517877, 24), (517878, 12), (517879, 24), (517881, 12), (517883, 24), (517887, 12), (517982, 12), (517983, 24), (517999, 24), (518015, 12), (518038, 24), (518039, 24), (518046, 24), (518047, 24), (518055, 24), (518063, 24), (518069, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 440, 1224, 1224, 0, 440, 0, 440, 1224, 1224, 1224, 0, 0, 0, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(517563, 2780), (517565, 1851), (517566, 4506), (517567, 6296), (517590, 2074), (517591, 3556), (517594, 973), (517595, 1886), (517597, 2027), (517598, 2733), (517599, 5042), (517605, 192), (517607, 1996), (517611, 1358), (517615, 2814), (517621, 1748), (517622, 4416), (517623, 5445), (517625, 885), (517626, 2277), (517627, 2812), (517629, 2237), (517630, 5796), (517631, 7914), (517737, 752), (517743, 516), (517782, 68), (517783, 466), (517791, 906), (517982, 904), (517983, 1823), (517999, 1076), (518015, 2612), (518038, 1434), (518039, 2824), (518046, 2212), (518047, 4285), (518055, 1326), (518063, 2367), (518069, 1592)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 517563 518070 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2252108 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 517563 518070 1348 2252108 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S125

end RACert.S0N3.C0
