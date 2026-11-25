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
  [(0, 1), (1, 4), (3, 4), (6, 2), (7, 4), (15, 1), (16, 2), (17, 8), (19, 4), (21, 4), (22, 4), (23, 8), (31, 2), (48, 1), (49, 4), (51, 4), (54, 2), (55, 4), (63, 1), (64, 1), (65, 4), (67, 4), (70, 2), (71, 4), (79, 1), (80, 2), (81, 8), (83, 4), (85, 4), (86, 4), (87, 8), (95, 2), (112, 1), (113, 4), (115, 4), (118, 2), (119, 4), (127, 1), (128, 1), (129, 4), (131, 4), (134, 2), (135, 4), (143, 1), (144, 2), (145, 8), (147, 4), (149, 4), (150, 4), (151, 8)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 1217, 0, 433, 433, 0, 1323, 0, 1323, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1217, 0, 433, 433, 0, 1323, 0, 1323, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 0), (1, 0), (6, 0), (16, 92), (19, 1967), (22, 1741), (23, 3904), (31, 19674), (48, 1053), (49, 868), (51, 4057), (54, 8099), (55, 11679), (63, 32546), (64, 490), (65, 2), (67, 0), (70, 164), (71, 0), (79, 17770), (80, 584), (81, 406), (83, 2645), (85, 2766), (86, 2971), (87, 7666), (95, 60903), (112, 2614), (113, 906), (115, 4926), (118, 9556), (119, 15551), (127, 78137), (128, 241), (129, 0), (134, 0), (144, 93), (147, 2135), (150, 2165), (151, 5133)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 8 perms 0 159 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 685569 = true := by decide +kernel

theorem total : OrbitSeg 8 perms (P.leaf 20) 0 159 174 685569 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S0

end RACert.S0N3.C1
