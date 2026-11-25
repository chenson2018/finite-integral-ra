/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 5), (3, 10), (7, 10), (15, 5), (31, 1), (32, 10), (33, 30), (35, 30), (39, 10), (40, 20), (41, 60), (43, 60), (47, 20), (56, 10), (57, 30), (59, 30), (63, 10), (96, 30), (97, 60), (99, 30), (100, 60), (101, 120), (103, 60), (108, 30), (109, 60), (111, 30), (112, 30), (113, 60), (115, 30), (116, 60), (117, 120), (119, 60), (124, 30), (125, 60), (127, 30), (224, 10), (225, 20), (227, 10), (228, 30)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 541), (1, 541), (3, 541), (7, 541), (15, 541), (31, 541), (32, 133), (33, 165), (35, 205), (39, 317), (40, 133), (41, 165), (43, 205), (47, 317), (56, 133), (57, 165), (59, 205), (63, 317), (96, 45), (97, 49), (99, 87), (100, 57), (101, 57), (103, 111), (108, 69), (109, 65), (111, 135), (112, 45), (113, 49), (115, 87), (116, 57), (117, 57), (119, 111), (124, 69), (125, 65), (127, 135), (224, 78), (225, 69), (227, 139), (228, 96)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 0 229 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 153822 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 0 229 1382 153822 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S0

end RACert.S5N0.C0
