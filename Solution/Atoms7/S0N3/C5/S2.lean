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

namespace S2

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(475, 24), (478, 12), (479, 24), (511, 4), (960, 1), (961, 6), (963, 3), (965, 3), (966, 6), (967, 6), (972, 3), (973, 6), (975, 3), (979, 6), (983, 3), (985, 2), (987, 6), (990, 3), (991, 6), (1023, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(475, 13759), (478, 11818), (479, 35044), (511, 64657), (960, 8), (961, 128), (963, 128), (965, 1024), (966, 1808), (967, 2696), (972, 3606), (973, 24046), (975, 72244), (979, 4276), (983, 5142), (985, 32348), (987, 61134), (990, 46684), (991, 98394), (1023, 120418)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 10 perms 475 1024 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 3298214 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 18) 475 1024 128 3298214 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S2

end RACert.S0N3.C5
