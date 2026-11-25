/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C6.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C6

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (3, 1), (4, 2), (5, 2), (6, 2), (7, 2), (12, 1), (13, 2), (15, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 95), (1, 184), (3, 2704), (4, 225), (5, 2142), (6, 564), (7, 5817), (12, 1050), (13, 5289), (15, 12290)]

theorem l0 : P.leaf 18 0 = 95 := by decide +kernel

theorem l1 : P.leaf 18 1 = 184 := by decide +kernel

theorem l3 : P.leaf 18 3 = 2704 := by decide +kernel

theorem l4 : P.leaf 18 4 = 225 := by decide +kernel

theorem l5 : P.leaf 18 5 = 2142 := by decide +kernel

theorem l6 : P.leaf 18 6 = 564 := by decide +kernel

theorem l7 : P.leaf 18 7 = 5817 := by decide +kernel

theorem l12 : P.leaf 18 12 = 1050 := by decide +kernel

theorem l13 : P.leaf 18 13 = 5289 := by decide +kernel

theorem l15 : P.leaf 18 15 = 12290 := by decide +kernel

theorem segOK : checkSeg 4 perms 0 16 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 44581 = true := by decide +kernel

theorem total : OrbitSeg 4 perms (P.leaf 18) 0 16 16 44581 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7 (.cons l12 (.cons l13 (.cons l15 (.nil))))))))))))

end S0

end RACert.S0N3.C6
