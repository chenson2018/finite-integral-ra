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
  [(0, 1), (1, 2), (3, 1), (4, 2), (5, 2), (6, 2), (7, 2), (12, 1), (13, 2), (15, 1), (16, 2), (17, 2), (18, 2), (19, 2), (20, 2), (21, 2), (22, 2), (23, 2), (24, 2), (25, 2), (26, 2), (27, 2), (28, 2), (29, 2), (30, 2), (31, 2), (48, 1), (49, 2), (51, 1), (52, 2), (53, 2), (54, 2), (55, 2), (60, 1), (61, 2), (63, 1), (64, 4), (65, 8), (67, 4), (68, 8), (69, 8), (70, 8), (71, 8), (76, 4), (77, 8), (79, 4), (80, 8), (81, 8), (82, 8), (83, 8), (84, 8), (85, 8), (86, 8), (87, 8), (88, 8), (89, 8), (90, 8), (91, 8), (92, 8), (93, 8), (94, 8)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 417, 0, 0, 0, 0, 0, 0, 0, 417, 0, 0, 0, 0, 0, 0, 0, 417, 0, 0, 433, 0, 0, 0, 0, 0, 0, 501, 529, 529, 503, 601, 622, 620, 0, 0, 0, 417, 601, 622, 621, 420, 601, 622, 622, 417, 0, 0, 0, 420, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 531), (1, 50), (3, 507), (4, 51), (5, 24), (6, 18), (7, 12), (12, 779), (13, 48), (15, 200), (17, 24), (18, 4), (19, 12), (20, 130), (21, 227), (22, 48), (23, 58), (25, 32), (26, 0), (27, 32), (28, 282), (29, 147), (30, 144), (31, 480), (49, 0), (51, 16), (53, 0), (54, 88), (55, 320), (60, 530), (61, 371), (63, 2080), (76, 19), (77, 1), (79, 8), (89, 0), (90, 0), (91, 16), (93, 10), (94, 31)]

theorem l0 : P.leaf 16 0 = 531 := by decide +kernel

theorem l1 : P.leaf 16 1 = 50 := by decide +kernel

theorem l3 : P.leaf 16 3 = 507 := by decide +kernel

theorem l4 : P.leaf 16 4 = 51 := by decide +kernel

theorem l5 : P.leaf 16 5 = 24 := by decide +kernel

theorem l6 : P.leaf 16 6 = 18 := by decide +kernel

theorem l7 : P.leaf 16 7 = 12 := by decide +kernel

theorem l12 : P.leaf 16 12 = 779 := by decide +kernel

theorem l13 : P.leaf 16 13 = 48 := by decide +kernel

theorem l15 : P.leaf 16 15 = 200 := by decide +kernel

theorem l17 : P.leaf 16 17 = 24 := by decide +kernel

theorem l18 : P.leaf 16 18 = 4 := by decide +kernel

theorem l19 : P.leaf 16 19 = 12 := by decide +kernel

theorem l20 : P.leaf 16 20 = 130 := by decide +kernel

theorem l21 : P.leaf 16 21 = 227 := by decide +kernel

theorem l22 : P.leaf 16 22 = 48 := by decide +kernel

theorem l23 : P.leaf 16 23 = 58 := by decide +kernel

theorem l25 : P.leaf 16 25 = 32 := by decide +kernel

theorem l26 : P.leaf 16 26 = 0 := by decide +kernel

theorem l27 : P.leaf 16 27 = 32 := by decide +kernel

theorem l28 : P.leaf 16 28 = 282 := by decide +kernel

theorem l29 : P.leaf 16 29 = 147 := by decide +kernel

theorem l30 : P.leaf 16 30 = 144 := by decide +kernel

theorem l31 : P.leaf 16 31 = 480 := by decide +kernel

theorem l49 : P.leaf 16 49 = 0 := by decide +kernel

theorem l51 : P.leaf 16 51 = 16 := by decide +kernel

theorem l53 : P.leaf 16 53 = 0 := by decide +kernel

theorem l54 : P.leaf 16 54 = 88 := by decide +kernel

theorem l55 : P.leaf 16 55 = 320 := by decide +kernel

theorem l60 : P.leaf 16 60 = 530 := by decide +kernel

theorem l61 : P.leaf 16 61 = 371 := by decide +kernel

theorem l63 : P.leaf 16 63 = 2080 := by decide +kernel

theorem l76 : P.leaf 16 76 = 19 := by decide +kernel

theorem l77 : P.leaf 16 77 = 1 := by decide +kernel

theorem l79 : P.leaf 16 79 = 8 := by decide +kernel

theorem l89 : P.leaf 16 89 = 0 := by decide +kernel

theorem l90 : P.leaf 16 90 = 0 := by decide +kernel

theorem l91 : P.leaf 16 91 = 16 := by decide +kernel

theorem l93 : P.leaf 16 93 = 10 := by decide +kernel

theorem l94 : P.leaf 16 94 = 31 := by decide +kernel

theorem segOK : checkSeg 10 perms 0 95 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 10419 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 16) 0 95 248 10419 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7 (.cons l12 (.cons l13 (.cons l15 (.cons l17 (.cons l18 (.cons l19 (.cons l20 (.cons l21 (.cons l22 (.cons l23 (.cons l25 (.cons l26 (.cons l27 (.cons l28 (.cons l29 (.cons l30 (.cons l31 (.cons l49 (.cons l51 (.cons l53 (.cons l54 (.cons l55 (.cons l60 (.cons l61 (.cons l63 (.cons l76 (.cons l77 (.cons l79 (.cons l89 (.cons l90 (.cons l91 (.cons l93 (.cons l94 (.nil))))))))))))))))))))))))))))))))))))))))))

end S0

end RACert.S0N3.C2
