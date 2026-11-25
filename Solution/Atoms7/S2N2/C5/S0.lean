/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C5.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C5

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 4), (7, 4), (15, 1), (16, 4), (17, 8), (18, 8), (19, 8), (21, 4), (22, 8), (23, 8), (26, 4), (27, 8), (31, 4), (48, 4), (49, 4), (50, 4), (51, 4), (52, 8), (53, 8), (54, 8), (55, 8), (60, 4), (61, 4), (62, 4), (63, 4), (96, 2), (97, 8), (99, 4), (101, 4), (102, 4), (103, 8), (111, 2), (112, 4), (113, 8), (114, 8), (115, 8), (117, 4), (118, 8), (119, 8), (122, 4), (123, 8), (127, 4), (240, 1), (241, 4), (243, 2), (245, 4), (247, 4), (255, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 1350, 0, 1350, 0, 0, 0, 0, 1350, 0, 0, 1350, 0, 1350, 0, 1302, 0, 1302, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1350, 0, 1350, 0, 0, 0, 0, 1350, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 16), (1, 0), (3, 1596), (5, 0), (7, 416), (15, 5589), (17, 0), (19, 178), (21, 112), (22, 0), (23, 741), (27, 259), (31, 3551), (49, 508), (51, 664), (53, 1196), (55, 2073), (60, 1285), (61, 9811), (62, 1404), (63, 14518), (96, 6), (97, 0), (99, 4113), (101, 0), (102, 752), (103, 4246), (111, 28616), (113, 1406), (115, 5511), (117, 6264), (118, 1662), (119, 14886), (123, 6032), (127, 38242), (240, 8878), (241, 11276), (243, 40570), (245, 18423), (247, 53571), (255, 174869)]

theorem leavesOK0 : P.checkLeavesR 20 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 8 perms 0 256 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 1296088 = true := by decide +kernel

theorem total : OrbitSeg 8 perms (P.leaf 20) 0 256 256 1296088 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S2N2.C5
