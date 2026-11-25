/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S1N2.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S1N2.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 4), (7, 4), (15, 1)]

/-- Evidence: `0` for a leaf evaluated below, `i + 1` for a leaf killed by the `i`-th quadruple. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 8420), (1, 10505), (3, 20369), (5, 13841), (7, 27156), (15, 57342)]

theorem leavesOK0 : P.checkLeavesR 21 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 4 perms 0 16 seg = true := by decide +kernel

theorem evOK : P.checkEvR 21 qmFlat seg ev live 0 312508 = true := by decide +kernel

theorem total : OrbitSeg 4 perms (P.leaf 21) 0 16 16 312508 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEvR_sum check rows flatOK evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S1N2.C0
