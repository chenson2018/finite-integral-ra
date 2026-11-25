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
  [(0, 1), (1, 6), (3, 3), (5, 3), (6, 6), (7, 6), (12, 3), (13, 6), (15, 3), (19, 6), (23, 3), (25, 2), (27, 6), (30, 3), (31, 6), (63, 1), (64, 4), (65, 24), (67, 12), (69, 12), (70, 24), (71, 24), (76, 12), (77, 24), (79, 12), (83, 24), (87, 12), (89, 8), (91, 24), (94, 12), (95, 24), (127, 4), (192, 6), (193, 12), (194, 12), (195, 12), (197, 6), (198, 12), (199, 12), (200, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (3, 6), (5, 0), (6, 0), (7, 0), (12, 22), (13, 0), (15, 0), (19, 375), (23, 721), (25, 8), (27, 56), (30, 910), (31, 540), (63, 10936), (64, 2), (65, 0), (67, 0), (69, 0), (70, 0), (71, 0), (76, 3), (77, 0), (79, 0), (83, 0), (87, 17), (89, 8), (91, 136), (94, 201), (95, 1794), (127, 19606), (192, 0), (193, 0), (194, 0), (195, 0), (197, 0), (198, 0), (199, 0), (200, 0)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 10 perms 0 201 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 149223 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 18) 0 201 404 149223 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S0

end RACert.S0N3.C5
