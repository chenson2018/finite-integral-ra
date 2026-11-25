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

namespace S11

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(16352, 10), (16353, 20), (16355, 10), (16356, 30), (16357, 60), (16359, 30), (16364, 30), (16365, 60), (16367, 30), (16380, 10), (16381, 20), (16383, 10), (32736, 1), (32737, 5), (32739, 10), (32743, 10), (32751, 5), (32767, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(16352, 103056), (16353, 176980), (16355, 294204), (16356, 122590), (16357, 216910), (16359, 371712), (16364, 146034), (16365, 266467), (16367, 470720), (16380, 174396), (16381, 328776), (16383, 600576), (32736, 165399), (32737, 223381), (32739, 308796), (32743, 440192), (32751, 655360), (32767, 1048576)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 16352 32768 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 97269300 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 16352 32768 352 97269300 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S11

end RACert.S5N0.C0
