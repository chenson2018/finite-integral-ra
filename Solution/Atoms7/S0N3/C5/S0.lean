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
  [(0, 1), (1, 12), (3, 6), (5, 12), (7, 12), (15, 3), (17, 6), (18, 6), (19, 12), (20, 24), (21, 24), (22, 24), (23, 24), (28, 12), (29, 12), (30, 12), (31, 12), (51, 3), (52, 12), (53, 24), (55, 12), (60, 6), (61, 12), (63, 6), (80, 12), (81, 24), (82, 24), (83, 24), (85, 12), (86, 24), (87, 24), (90, 12), (91, 24), (95, 12), (112, 12), (113, 24), (115, 12), (116, 12), (117, 24), (119, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 258), (1, 60), (3, 124), (5, 8), (7, 27), (15, 88), (17, 92), (18, 72), (19, 188), (20, 6), (21, 7), (22, 4), (23, 20), (28, 0), (29, 12), (30, 0), (31, 32), (51, 446), (52, 31), (53, 31), (55, 132), (60, 46), (61, 38), (63, 172), (80, 10), (81, 9), (82, 20), (83, 18), (85, 66), (86, 27), (87, 162), (90, 71), (91, 62), (95, 359), (112, 61), (113, 122), (115, 169), (116, 249), (117, 292), (119, 376)]

theorem l0 : P.leaf 16 0 = 258 := by decide +kernel

theorem l1 : P.leaf 16 1 = 60 := by decide +kernel

theorem l3 : P.leaf 16 3 = 124 := by decide +kernel

theorem l5 : P.leaf 16 5 = 8 := by decide +kernel

theorem l7 : P.leaf 16 7 = 27 := by decide +kernel

theorem l15 : P.leaf 16 15 = 88 := by decide +kernel

theorem l17 : P.leaf 16 17 = 92 := by decide +kernel

theorem l18 : P.leaf 16 18 = 72 := by decide +kernel

theorem l19 : P.leaf 16 19 = 188 := by decide +kernel

theorem l20 : P.leaf 16 20 = 6 := by decide +kernel

theorem l21 : P.leaf 16 21 = 7 := by decide +kernel

theorem l22 : P.leaf 16 22 = 4 := by decide +kernel

theorem l23 : P.leaf 16 23 = 20 := by decide +kernel

theorem l28 : P.leaf 16 28 = 0 := by decide +kernel

theorem l29 : P.leaf 16 29 = 12 := by decide +kernel

theorem l30 : P.leaf 16 30 = 0 := by decide +kernel

theorem l31 : P.leaf 16 31 = 32 := by decide +kernel

theorem l51 : P.leaf 16 51 = 446 := by decide +kernel

theorem l52 : P.leaf 16 52 = 31 := by decide +kernel

theorem l53 : P.leaf 16 53 = 31 := by decide +kernel

theorem l55 : P.leaf 16 55 = 132 := by decide +kernel

theorem l60 : P.leaf 16 60 = 46 := by decide +kernel

theorem l61 : P.leaf 16 61 = 38 := by decide +kernel

theorem l63 : P.leaf 16 63 = 172 := by decide +kernel

theorem l80 : P.leaf 16 80 = 10 := by decide +kernel

theorem l81 : P.leaf 16 81 = 9 := by decide +kernel

theorem l82 : P.leaf 16 82 = 20 := by decide +kernel

theorem l83 : P.leaf 16 83 = 18 := by decide +kernel

theorem l85 : P.leaf 16 85 = 66 := by decide +kernel

theorem l86 : P.leaf 16 86 = 27 := by decide +kernel

theorem l87 : P.leaf 16 87 = 162 := by decide +kernel

theorem l90 : P.leaf 16 90 = 71 := by decide +kernel

theorem l91 : P.leaf 16 91 = 62 := by decide +kernel

theorem l95 : P.leaf 16 95 = 359 := by decide +kernel

theorem l112 : P.leaf 16 112 = 61 := by decide +kernel

theorem l113 : P.leaf 16 113 = 122 := by decide +kernel

theorem l115 : P.leaf 16 115 = 169 := by decide +kernel

theorem l116 : P.leaf 16 116 = 249 := by decide +kernel

theorem l117 : P.leaf 16 117 = 292 := by decide +kernel

theorem l119 : P.leaf 16 119 = 376 := by decide +kernel

theorem segOK : checkSeg 12 perms 0 120 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 46284 = true := by decide +kernel

theorem total : OrbitSeg 12 perms (P.leaf 16) 0 120 577 46284 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l5 (.cons l7 (.cons l15 (.cons l17 (.cons l18 (.cons l19 (.cons l20 (.cons l21 (.cons l22 (.cons l23 (.cons l28 (.cons l29 (.cons l30 (.cons l31 (.cons l51 (.cons l52 (.cons l53 (.cons l55 (.cons l60 (.cons l61 (.cons l63 (.cons l80 (.cons l81 (.cons l82 (.cons l83 (.cons l85 (.cons l86 (.cons l87 (.cons l90 (.cons l91 (.cons l95 (.cons l112 (.cons l113 (.cons l115 (.cons l116 (.cons l117 (.cons l119 (.nil))))))))))))))))))))))))))))))))))))))))))

end S0

end RACert.S0N3.C5
