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

namespace S70

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(238967, 24), (238969, 24), (238970, 24), (238971, 24), (238973, 24), (238974, 24), (238975, 24), (238979, 24), (238983, 24), (238987, 24), (238991, 24), (238994, 24), (238995, 24), (238997, 12), (238998, 24), (238999, 24), (239002, 24), (239003, 24), (239005, 24), (239006, 24), (239007, 24), (239009, 24), (239011, 24), (239013, 24), (239014, 12), (239015, 24), (239017, 24), (239019, 24), (239021, 24), (239022, 24), (239023, 24), (239025, 24), (239026, 24), (239027, 24), (239029, 24), (239030, 24), (239031, 24), (239033, 24), (239034, 24), (239035, 24), (239037, 24), (239038, 24), (239039, 24), (239043, 24), (239047, 24), (239051, 24), (239055, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 419, 426, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 424, 0, 0, 0, 0, 424, 0, 0, 0, 0, 0, 0, 418, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(238967, 306), (238973, 56), (238974, 56), (238975, 400), (238979, 10), (238983, 50), (238987, 20), (238991, 50), (238994, 0), (238995, 46), (238997, 116), (238999, 320), (239002, 16), (239003, 112), (239005, 152), (239007, 536), (239009, 9), (239011, 52), (239013, 35), (239014, 92), (239015, 310), (239019, 128), (239022, 172), (239023, 616), (239025, 78), (239026, 42), (239027, 132), (239029, 286), (239030, 265), (239031, 909), (239033, 120), (239034, 132), (239035, 315), (239037, 360), (239038, 372), (239039, 1224), (239043, 12), (239047, 60), (239051, 24), (239055, 60)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 238967 239058 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 190728 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 238967 239058 1104 190728 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S70

end RACert.S0N3.C0
