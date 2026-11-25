/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C7.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C7

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 1), (2, 4), (3, 4), (6, 2), (7, 2), (10, 4), (11, 4), (14, 4), (15, 4), (30, 1), (31, 1), (32, 2), (33, 2), (34, 4), (35, 4), (38, 2), (39, 2), (40, 4), (41, 4), (42, 8), (43, 8), (46, 4), (47, 4), (56, 2), (57, 2), (58, 4), (59, 4), (62, 2), (63, 2), (96, 1), (97, 1), (98, 4), (99, 4), (102, 2), (103, 2), (106, 4), (107, 4), (110, 4), (111, 4), (126, 1), (127, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [409, 0, 0, 403, 0, 0, 0, 405, 0, 405, 0, 0, 409, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 409, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(1, 10264), (2, 3), (6, 12), (7, 24), (10, 0), (14, 0), (30, 6661), (31, 16276), (33, 144), (34, 127), (35, 14466), (38, 16692), (39, 42392), (40, 34), (41, 16062), (42, 12985), (43, 35963), (46, 34033), (47, 50697), (56, 7242), (57, 40488), (58, 26910), (59, 53407), (62, 44548), (63, 72584), (97, 31142), (98, 131), (99, 49030), (102, 19150), (103, 75508), (106, 23010), (107, 77710), (110, 78870), (111, 115907), (126, 161469), (127, 187944)]

theorem leavesOK0 : P.checkLeavesR 21 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 7 perms 0 128 seg = true := by decide +kernel

theorem evOK : P.checkEv 21 seg ev live 0 3604496 = true := by decide +kernel

theorem total : OrbitSeg 7 perms (P.leaf 21) 0 128 128 3604496 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S2N2.C7
