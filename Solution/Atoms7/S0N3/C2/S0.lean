/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C2.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C2

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 1), (2, 4), (3, 4), (6, 2), (7, 2), (10, 2), (11, 2), (12, 2), (13, 2), (14, 4), (15, 4), (30, 1), (31, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 10916), (1, 12242), (2, 16259), (3, 18676), (6, 28600), (7, 33293), (10, 30942), (11, 36653), (12, 26375), (13, 30306), (14, 45601), (15, 53499), (30, 69904), (31, 81749)]

theorem leavesOK0 : P.checkLeavesR 21 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 5 perms 0 32 seg = true := by decide +kernel

theorem evOK : P.checkEv 21 seg ev live 0 1083289 = true := by decide +kernel

theorem total : OrbitSeg 5 perms (P.leaf 21) 0 32 32 1083289 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S0N3.C2
