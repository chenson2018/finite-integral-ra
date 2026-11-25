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
  [(0, 1), (1, 3), (3, 3), (7, 1), (8, 3), (9, 6), (11, 3), (12, 3), (13, 6), (15, 3), (24, 3), (25, 3), (26, 6), (27, 6), (30, 3), (31, 3), (56, 1), (57, 3), (59, 3), (63, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 1971), (1, 412), (3, 384), (7, 1728), (8, 128), (9, 572), (11, 1520), (12, 238), (13, 1172), (15, 4601), (24, 1581), (25, 5785), (26, 4870), (27, 13826), (30, 17296), (31, 25480), (56, 14778), (57, 28524), (59, 52032), (63, 97911)]

theorem l0 : P.leaf 18 0 = 1971 := by decide +kernel

theorem l1 : P.leaf 18 1 = 412 := by decide +kernel

theorem l3 : P.leaf 18 3 = 384 := by decide +kernel

theorem l7 : P.leaf 18 7 = 1728 := by decide +kernel

theorem l8 : P.leaf 18 8 = 128 := by decide +kernel

theorem l9 : P.leaf 18 9 = 572 := by decide +kernel

theorem l11 : P.leaf 18 11 = 1520 := by decide +kernel

theorem l12 : P.leaf 18 12 = 238 := by decide +kernel

theorem l13 : P.leaf 18 13 = 1172 := by decide +kernel

theorem l15 : P.leaf 18 15 = 4601 := by decide +kernel

theorem l24 : P.leaf 18 24 = 1581 := by decide +kernel

theorem l25 : P.leaf 18 25 = 5785 := by decide +kernel

theorem l26 : P.leaf 18 26 = 4870 := by decide +kernel

theorem l27 : P.leaf 18 27 = 13826 := by decide +kernel

theorem l30 : P.leaf 18 30 = 17296 := by decide +kernel

theorem l31 : P.leaf 18 31 = 25480 := by decide +kernel

theorem l56 : P.leaf 18 56 = 14778 := by decide +kernel

theorem l57 : P.leaf 18 57 = 28524 := by decide +kernel

theorem l59 : P.leaf 18 59 = 52032 := by decide +kernel

theorem l63 : P.leaf 18 63 = 97911 := by decide +kernel

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 652971 = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf 18) 0 64 64 652971 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l7 (.cons l8 (.cons l9 (.cons l11 (.cons l12 (.cons l13 (.cons l15 (.cons l24 (.cons l25 (.cons l26 (.cons l27 (.cons l30 (.cons l31 (.cons l56 (.cons l57 (.cons l59 (.cons l63 (.nil))))))))))))))))))))))

end S0

end RACert.S5N0.C1
