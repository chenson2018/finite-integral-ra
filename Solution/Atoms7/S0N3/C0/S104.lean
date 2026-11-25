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

namespace S104

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439257, 48), (439258, 48), (439259, 48), (439261, 48), (439262, 48), (439263, 48), (439269, 48), (439270, 48), (439271, 48), (439273, 48), (439274, 48), (439275, 48), (439277, 48), (439278, 48), (439279, 48), (439285, 48), (439286, 48), (439287, 48), (439289, 48), (439290, 48), (439291, 48), (439292, 24), (439293, 48), (439294, 48), (439295, 48), (439637, 48), (439638, 24), (439639, 48), (439641, 48), (439642, 48), (439643, 48), (439645, 48), (439646, 48), (439647, 48), (439653, 24), (439655, 48), (439657, 48), (439658, 24), (439659, 48), (439661, 48), (439662, 48), (439663, 48), (439671, 24), (439673, 48), (439674, 48), (439675, 48), (439677, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 0, 0, 0, 0, 502, 0, 439, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439257, 618), (439258, 211), (439259, 1273), (439261, 1215), (439262, 851), (439263, 2619), (439270, 695), (439271, 1571), (439274, 636), (439275, 1482), (439278, 1255), (439279, 2851), (439285, 1274), (439286, 992), (439287, 2270), (439289, 1146), (439290, 904), (439291, 2192), (439292, 780), (439293, 2112), (439294, 1736), (439295, 4734), (439637, 181), (439638, 32), (439639, 520), (439641, 16), (439643, 51), (439645, 415), (439646, 110), (439647, 792), (439655, 606), (439658, 24), (439659, 195), (439662, 412), (439663, 936), (439671, 1519), (439673, 138), (439674, 72), (439675, 445), (439677, 1217)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 439257 439678 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1916184 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439257 439678 2136 1916184 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S104

end RACert.S0N3.C0
