/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C1

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 3), (3, 3), (7, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 6087), (1, 9975), (3, 87534), (7, 354357)]

theorem leavesOK0 : P.checkLeavesR 21 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 3 perms 0 8 seg = true := by decide +kernel

theorem evOK : P.checkEv 21 seg ev live 0 652971 = true := by decide +kernel

theorem total : OrbitSeg 3 perms (P.leaf 21) 0 8 8 652971 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S5N0.C1
