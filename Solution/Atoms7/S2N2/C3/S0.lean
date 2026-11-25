/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C3.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C3

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (3, 1), (4, 2), (5, 4), (7, 2), (12, 1), (13, 2), (15, 1), (16, 2), (17, 2), (18, 2), (19, 2), (20, 4), (21, 4), (22, 4), (23, 4), (28, 2), (29, 2), (30, 2), (31, 2), (48, 1), (49, 2), (51, 1), (52, 2), (53, 4), (55, 2), (60, 1), (61, 2), (63, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 812, 812, 0, 0, 0, 0, 0, 411, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 411, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 392), (1, 612), (3, 1498), (4, 0), (5, 0), (7, 15116), (15, 47103), (16, 486), (17, 1417), (18, 184), (19, 9126), (21, 0), (22, 0), (23, 47642), (28, 4166), (29, 28534), (30, 31176), (31, 151749), (48, 2724), (49, 206), (51, 17852), (53, 0), (55, 105612), (60, 13831), (61, 60490), (63, 209452)]

theorem leavesOK0 : P.checkLeavesR 20 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 1301168 = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf 20) 0 64 64 1301168 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S2N2.C3
