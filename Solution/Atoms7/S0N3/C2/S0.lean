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
  [(0, 1), (1, 2), (3, 1), (4, 4), (5, 8), (7, 4), (12, 2), (13, 4), (15, 2), (20, 2), (21, 4), (23, 2), (24, 2), (25, 4), (27, 2), (28, 4), (29, 8), (31, 4), (60, 1), (61, 2), (63, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 2423), (1, 1620), (3, 4184), (4, 29), (5, 387), (7, 7332), (12, 40), (13, 1952), (15, 34177), (20, 1294), (21, 5594), (23, 24436), (24, 1902), (25, 9846), (27, 66455), (28, 2312), (29, 12284), (31, 83389), (60, 27612), (61, 47456), (63, 151126)]

theorem leavesOK : P.checkLeavesR 20 qm live = true := by decide +kernel

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 1083289 = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf 20) 0 64 64 1083289 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S0

end RACert.S0N3.C2
