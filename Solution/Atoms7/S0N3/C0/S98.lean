/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace S98

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(430559, 48), (430576, 24), (430577, 48), (430579, 24), (430580, 48), (430581, 48), (430582, 48), (430583, 48), (430588, 24), (430589, 48), (430591, 24), (430863, 12), (430877, 12), (430878, 12), (430879, 24), (430911, 6), (430919, 24), (430923, 24), (430927, 24), (430933, 48), (430934, 48), (430935, 48), (430937, 48), (430938, 48), (430939, 48), (430941, 48), (430942, 48), (430943, 48), (430964, 12), (430965, 48), (430967, 24), (430968, 12), (430969, 48), (430971, 24), (430972, 24), (430973, 48), (430975, 24), (431043, 4), (431047, 24), (431055, 12), (431061, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(430559, 683), (430576, 19), (430577, 25), (430579, 434), (430580, 52), (430581, 70), (430582, 163), (430583, 641), (430588, 509), (430589, 593), (430591, 2646), (430863, 98), (430877, 69), (430878, 25), (430879, 122), (430911, 196), (430919, 119), (430923, 65), (430927, 184), (430933, 44), (430934, 8), (430935, 148), (430937, 9), (430939, 65), (430941, 184), (430942, 52), (430943, 312), (430964, 20), (430965, 102), (430967, 280), (430968, 12), (430969, 56), (430971, 216), (430972, 316), (430973, 324), (430975, 558), (431043, 918), (431047, 1106), (431055, 1964), (431061, 606)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 430559 431062 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 387456 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 430559 431062 1354 387456 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S98

end RACert.S0N3.C0
