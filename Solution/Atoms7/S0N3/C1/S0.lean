/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 4), (6, 2), (7, 4), (15, 1), (16, 2), (17, 8), (19, 4), (21, 4), (22, 4), (23, 8), (31, 2), (48, 1), (49, 4), (51, 4), (54, 2), (55, 4), (63, 1), (64, 1), (65, 4), (67, 4), (70, 2), (71, 4), (79, 1), (80, 2), (81, 8), (83, 4), (85, 4), (86, 4), (87, 8), (95, 2), (112, 1), (113, 4), (115, 4), (118, 2), (119, 4), (127, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 1316, 0, 1316, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 1311), (1, 23), (3, 0), (6, 367), (7, 0), (15, 5414), (16, 786), (19, 5141), (22, 4112), (23, 9644), (31, 70392), (48, 2626), (49, 2565), (51, 11220), (54, 18652), (55, 31082), (63, 143409), (64, 1835), (65, 23), (67, 0), (70, 367), (71, 0), (79, 5414), (80, 763), (81, 418), (83, 6146), (85, 2220), (86, 5161), (87, 12793), (95, 96910), (112, 2325), (113, 2565), (115, 11220), (118, 18656), (119, 31114), (127, 154301)]

theorem leavesOK : P.checkLeavesR 21 qm live = true := by decide +kernel

theorem segOK : checkSeg 7 perms 0 128 seg = true := by decide +kernel

theorem evOK : P.checkEv 21 seg ev live 0 1363629 = true := by decide +kernel

theorem total : OrbitSeg 7 perms (P.leaf 21) 0 128 128 1363629 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S0

end RACert.S0N3.C1
