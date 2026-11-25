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

namespace S123

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(517023, 24), (517029, 24), (517030, 24), (517031, 24), (517033, 24), (517034, 24), (517035, 24), (517037, 24), (517038, 24), (517039, 24), (517044, 12), (517045, 24), (517046, 24), (517047, 24), (517049, 24), (517050, 24), (517051, 24), (517052, 24), (517053, 24), (517054, 24), (517055, 24), (517059, 8), (517063, 24), (517067, 24), (517071, 24), (517077, 24), (517078, 24), (517079, 24), (517081, 24), (517082, 24), (517083, 24), (517085, 24), (517086, 24), (517087, 24), (517093, 24), (517094, 24), (517095, 24), (517097, 24), (517098, 24), (517099, 24), (517101, 24), (517102, 24), (517103, 24), (517109, 24), (517110, 24), (517111, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(517023, 856), (517030, 197), (517031, 204), (517034, 280), (517035, 280), (517038, 560), (517039, 560), (517044, 52), (517045, 188), (517046, 484), (517047, 484), (517049, 136), (517050, 384), (517051, 400), (517052, 288), (517053, 312), (517054, 768), (517055, 856), (517059, 729), (517063, 1300), (517067, 872), (517071, 1648), (517077, 829), (517078, 2092), (517079, 2834), (517081, 494), (517082, 1060), (517083, 1712), (517085, 1065), (517086, 2527), (517087, 4511), (517094, 1487), (517095, 1519), (517098, 1072), (517099, 1080), (517102, 2150), (517103, 2150), (517109, 963), (517110, 3043), (517111, 3253)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 517023 517113 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1084008 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 517023 517113 1076 1084008 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S123

end RACert.S0N3.C0
