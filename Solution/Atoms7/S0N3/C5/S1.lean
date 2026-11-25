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

namespace S1

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(201, 12), (202, 12), (203, 12), (204, 12), (205, 12), (206, 12), (207, 12), (210, 6), (211, 12), (215, 6), (216, 12), (217, 12), (218, 12), (219, 12), (220, 12), (221, 12), (222, 12), (223, 12), (232, 6), (233, 12), (234, 12), (235, 12), (237, 6), (238, 12), (239, 12), (250, 6), (251, 12), (255, 6), (448, 4), (449, 24), (451, 12), (453, 12), (454, 24), (455, 24), (460, 12), (461, 24), (463, 12), (467, 24), (471, 12), (473, 8)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(201, 0), (202, 0), (203, 0), (204, 1), (205, 0), (206, 0), (207, 8), (210, 6), (211, 28), (215, 138), (216, 0), (217, 268), (218, 0), (219, 2404), (220, 232), (221, 3287), (222, 2666), (223, 13382), (232, 0), (233, 80), (234, 0), (235, 692), (237, 2062), (238, 796), (239, 11094), (250, 0), (251, 8327), (255, 37122), (448, 0), (449, 0), (451, 0), (453, 0), (454, 0), (455, 0), (460, 13), (461, 35), (463, 480), (467, 984), (471, 1776), (473, 4138)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 10 perms 201 475 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 839936 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 18) 201 475 492 839936 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S1

end RACert.S0N3.C5
