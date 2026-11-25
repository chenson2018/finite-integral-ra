/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C5.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 3), (3, 3), (7, 1), (8, 4), (9, 12), (11, 12), (15, 4), (24, 6), (25, 12), (27, 6), (28, 6), (29, 12), (31, 6), (56, 4), (57, 12), (59, 12), (63, 4), (120, 1), (121, 3), (123, 3), (127, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 3218), (1, 2778), (3, 2571), (7, 2490), (8, 3733), (9, 3810), (11, 4078), (15, 4470), (24, 12968), (25, 15164), (27, 18045), (28, 12956), (29, 15959), (31, 19643), (56, 36874), (57, 45172), (59, 56696), (63, 71648), (120, 122802), (121, 178147), (123, 245819), (127, 331798)]

theorem leavesOK : P.checkLeavesR 21 qm live = true := by decide +kernel

theorem segOK : checkSeg 7 perms 0 128 seg = true := by decide +kernel

theorem evOK : P.checkEv 21 seg ev live 0 4287373 = true := by decide +kernel

theorem total : OrbitSeg 7 perms (P.leaf 21) 0 128 128 4287373 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S0

end RACert.S0N3.C5
