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
  [(0, 1), (1, 2), (3, 1), (4, 4), (5, 4), (6, 4), (7, 4), (12, 2), (13, 2), (14, 2), (15, 2), (20, 2), (21, 4), (23, 2), (24, 2), (25, 4), (27, 2), (28, 4), (29, 4), (30, 4), (31, 4), (60, 1), (61, 2), (63, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 4731), (1, 5681), (3, 7065), (4, 6845), (5, 7108), (6, 9580), (7, 11402), (12, 12355), (13, 13586), (14, 16805), (15, 19147), (20, 13068), (21, 16009), (23, 22509), (24, 9523), (25, 14746), (27, 17666), (28, 20005), (29, 23846), (30, 25350), (31, 29899), (60, 33098), (61, 37553), (63, 43449)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 1083289 = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf 20) 0 64 64 1083289 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S0

end RACert.S0N3.C2
