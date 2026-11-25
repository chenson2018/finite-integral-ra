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

theorem l0 : P.leaf 20 0 = 541 := by decide +kernel

theorem l1 : P.leaf 20 1 = 541 := by decide +kernel

theorem l3 : P.leaf 20 3 = 541 := by decide +kernel

theorem l7 : P.leaf 20 7 = 541 := by decide +kernel

theorem l15 : P.leaf 20 15 = 541 := by decide +kernel

theorem l31 : P.leaf 20 31 = 541 := by decide +kernel

theorem l32 : P.leaf 20 32 = 133 := by decide +kernel

theorem l33 : P.leaf 20 33 = 165 := by decide +kernel

theorem l35 : P.leaf 20 35 = 205 := by decide +kernel

theorem l39 : P.leaf 20 39 = 317 := by decide +kernel

theorem l40 : P.leaf 20 40 = 133 := by decide +kernel

theorem l41 : P.leaf 20 41 = 165 := by decide +kernel

theorem l43 : P.leaf 20 43 = 205 := by decide +kernel

theorem l47 : P.leaf 20 47 = 317 := by decide +kernel

theorem l56 : P.leaf 20 56 = 133 := by decide +kernel

theorem l57 : P.leaf 20 57 = 165 := by decide +kernel

theorem l59 : P.leaf 20 59 = 205 := by decide +kernel

theorem l63 : P.leaf 20 63 = 317 := by decide +kernel

theorem l96 : P.leaf 20 96 = 45 := by decide +kernel

theorem l97 : P.leaf 20 97 = 49 := by decide +kernel

theorem l99 : P.leaf 20 99 = 87 := by decide +kernel

theorem l100 : P.leaf 20 100 = 57 := by decide +kernel

theorem l101 : P.leaf 20 101 = 57 := by decide +kernel

theorem l103 : P.leaf 20 103 = 111 := by decide +kernel

theorem l108 : P.leaf 20 108 = 69 := by decide +kernel

theorem l109 : P.leaf 20 109 = 65 := by decide +kernel

theorem l111 : P.leaf 20 111 = 135 := by decide +kernel

theorem l112 : P.leaf 20 112 = 45 := by decide +kernel

theorem l113 : P.leaf 20 113 = 49 := by decide +kernel

theorem l115 : P.leaf 20 115 = 87 := by decide +kernel

theorem l116 : P.leaf 20 116 = 57 := by decide +kernel

theorem l117 : P.leaf 20 117 = 57 := by decide +kernel

theorem l119 : P.leaf 20 119 = 111 := by decide +kernel

theorem l124 : P.leaf 20 124 = 69 := by decide +kernel

theorem l125 : P.leaf 20 125 = 65 := by decide +kernel

theorem l127 : P.leaf 20 127 = 135 := by decide +kernel

theorem l224 : P.leaf 20 224 = 78 := by decide +kernel

theorem l225 : P.leaf 20 225 = 69 := by decide +kernel

theorem l227 : P.leaf 20 227 = 139 := by decide +kernel

theorem l228 : P.leaf 20 228 = 96 := by decide +kernel

theorem segOK : checkSeg 15 perms 0 229 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 153822 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 0 229 1382 153822 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l7 (.cons l15 (.cons l31 (.cons l32 (.cons l33 (.cons l35 (.cons l39 (.cons l40 (.cons l41 (.cons l43 (.cons l47 (.cons l56 (.cons l57 (.cons l59 (.cons l63 (.cons l96 (.cons l97 (.cons l99 (.cons l100 (.cons l101 (.cons l103 (.cons l108 (.cons l109 (.cons l111 (.cons l112 (.cons l113 (.cons l115 (.cons l116 (.cons l117 (.cons l119 (.cons l124 (.cons l125 (.cons l127 (.cons l224 (.cons l225 (.cons l227 (.cons l228 (.nil))))))))))))))))))))))))))))))))))))))))))

end S0

end RACert.S5N0.C0
