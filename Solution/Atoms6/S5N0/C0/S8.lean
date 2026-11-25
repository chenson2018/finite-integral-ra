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

theorem leavesOK : P.checkLeavesR 20 qm live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 7136 7594 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 7113386 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 7136 7594 1904 7113386 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S8

end RACert.S5N0.C0
