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

namespace S8

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(7136, 10), (7137, 30), (7139, 30), (7143, 10), (7144, 20), (7145, 60), (7147, 60), (7151, 20), (7160, 10), (7161, 30), (7163, 30), (7167, 10), (7520, 15), (7521, 60), (7523, 60), (7526, 30), (7527, 60), (7535, 15), (7536, 15), (7537, 60), (7539, 60), (7542, 30), (7543, 60), (7551, 15), (7552, 12), (7553, 60), (7555, 60), (7558, 60), (7559, 60), (7565, 60), (7567, 60), (7583, 12), (7584, 60), (7585, 60), (7586, 120), (7587, 120), (7590, 60), (7591, 60), (7592, 120), (7593, 120)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(7136, 893), (7137, 1268), (7139, 1848), (7143, 2730), (7144, 1045), (7145, 1540), (7147, 2296), (7151, 3418), (7160, 1197), (7161, 1812), (7163, 2744), (7167, 4106), (7520, 1896), (7521, 2535), (7523, 3501), (7526, 3601), (7527, 5105), (7535, 7521), (7536, 2148), (7537, 2834), (7539, 3836), (7542, 4138), (7543, 5702), (7551, 8583), (7552, 220), (7553, 282), (7555, 366), (7558, 353), (7559, 465), (7565, 447), (7567, 570), (7583, 703), (7584, 3901), (7585, 5000), (7586, 5679), (7587, 7304), (7590, 8621), (7591, 11074), (7592, 4004), (7593, 5126)]

theorem l7136 : P.leaf 20 7136 = 893 := by decide +kernel

theorem l7137 : P.leaf 20 7137 = 1268 := by decide +kernel

theorem l7139 : P.leaf 20 7139 = 1848 := by decide +kernel

theorem l7143 : P.leaf 20 7143 = 2730 := by decide +kernel

theorem l7144 : P.leaf 20 7144 = 1045 := by decide +kernel

theorem l7145 : P.leaf 20 7145 = 1540 := by decide +kernel

theorem l7147 : P.leaf 20 7147 = 2296 := by decide +kernel

theorem l7151 : P.leaf 20 7151 = 3418 := by decide +kernel

theorem l7160 : P.leaf 20 7160 = 1197 := by decide +kernel

theorem l7161 : P.leaf 20 7161 = 1812 := by decide +kernel

theorem l7163 : P.leaf 20 7163 = 2744 := by decide +kernel

theorem l7167 : P.leaf 20 7167 = 4106 := by decide +kernel

theorem l7520 : P.leaf 20 7520 = 1896 := by decide +kernel

theorem l7521 : P.leaf 20 7521 = 2535 := by decide +kernel

theorem l7523 : P.leaf 20 7523 = 3501 := by decide +kernel

theorem l7526 : P.leaf 20 7526 = 3601 := by decide +kernel

theorem l7527 : P.leaf 20 7527 = 5105 := by decide +kernel

theorem l7535 : P.leaf 20 7535 = 7521 := by decide +kernel

theorem l7536 : P.leaf 20 7536 = 2148 := by decide +kernel

theorem l7537 : P.leaf 20 7537 = 2834 := by decide +kernel

theorem l7539 : P.leaf 20 7539 = 3836 := by decide +kernel

theorem l7542 : P.leaf 20 7542 = 4138 := by decide +kernel

theorem l7543 : P.leaf 20 7543 = 5702 := by decide +kernel

theorem l7551 : P.leaf 20 7551 = 8583 := by decide +kernel

theorem l7552 : P.leaf 20 7552 = 220 := by decide +kernel

theorem l7553 : P.leaf 20 7553 = 282 := by decide +kernel

theorem l7555 : P.leaf 20 7555 = 366 := by decide +kernel

theorem l7558 : P.leaf 20 7558 = 353 := by decide +kernel

theorem l7559 : P.leaf 20 7559 = 465 := by decide +kernel

theorem l7565 : P.leaf 20 7565 = 447 := by decide +kernel

theorem l7567 : P.leaf 20 7567 = 570 := by decide +kernel

theorem l7583 : P.leaf 20 7583 = 703 := by decide +kernel

theorem l7584 : P.leaf 20 7584 = 3901 := by decide +kernel

theorem l7585 : P.leaf 20 7585 = 5000 := by decide +kernel

theorem l7586 : P.leaf 20 7586 = 5679 := by decide +kernel

theorem l7587 : P.leaf 20 7587 = 7304 := by decide +kernel

theorem l7590 : P.leaf 20 7590 = 8621 := by decide +kernel

theorem l7591 : P.leaf 20 7591 = 11074 := by decide +kernel

theorem l7592 : P.leaf 20 7592 = 4004 := by decide +kernel

theorem l7593 : P.leaf 20 7593 = 5126 := by decide +kernel

theorem segOK : checkSeg 15 perms 7136 7594 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 7113386 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 7136 7594 1904 7113386 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l7136 (.cons l7137 (.cons l7139 (.cons l7143 (.cons l7144 (.cons l7145 (.cons l7147 (.cons l7151 (.cons l7160 (.cons l7161 (.cons l7163 (.cons l7167 (.cons l7520 (.cons l7521 (.cons l7523 (.cons l7526 (.cons l7527 (.cons l7535 (.cons l7536 (.cons l7537 (.cons l7539 (.cons l7542 (.cons l7543 (.cons l7551 (.cons l7552 (.cons l7553 (.cons l7555 (.cons l7558 (.cons l7559 (.cons l7565 (.cons l7567 (.cons l7583 (.cons l7584 (.cons l7585 (.cons l7586 (.cons l7587 (.cons l7590 (.cons l7591 (.cons l7592 (.cons l7593 (.nil))))))))))))))))))))))))))))))))))))))))))

end S8

end RACert.S5N0.C0
