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

namespace S67

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(238395, 12), (238396, 12), (238397, 24), (238399, 12), (238401, 24), (238403, 12), (238405, 24), (238407, 12), (238409, 24), (238411, 12), (238413, 24), (238415, 12), (238417, 24), (238418, 24), (238419, 24), (238421, 24), (238422, 24), (238423, 24), (238425, 24), (238426, 24), (238427, 24), (238429, 24), (238430, 24), (238431, 24), (238449, 24), (238451, 12), (238452, 12), (238453, 24), (238455, 12), (238456, 6), (238457, 24), (238459, 12), (238460, 12), (238461, 24), (238463, 12), (238465, 24), (238467, 12), (238469, 24), (238471, 12), (238473, 24), (238475, 12), (238477, 24), (238479, 12), (238481, 24), (238482, 24), (238483, 24), (238485, 24), (238486, 24), (238487, 24), (238489, 24), (238490, 24), (238491, 24), (238493, 24), (238494, 24), (238495, 24), (238513, 24), (238515, 12), (238516, 6), (238517, 24), (238519, 12), (238521, 24), (238523, 12), (238524, 12), (238525, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 419, 538, 418, 0, 418, 538, 418, 0, 419, 426, 538, 0, 424, 0, 419, 424, 538, 0, 424, 0, 419, 538, 0, 0, 0, 0, 419, 538, 0, 0, 0, 0, 0, 418, 0, 418, 0, 418, 0, 0, 0, 0, 0, 424, 0, 0, 424, 0, 0, 424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(238395, 136), (238396, 20), (238397, 24), (238399, 144), (238407, 190), (238415, 331), (238421, 35), (238423, 247), (238429, 53), (238431, 363), (238452, 20), (238453, 40), (238455, 541), (238456, 96), (238460, 40), (238461, 60), (238463, 590), (238465, 3), (238467, 20), (238471, 195), (238475, 88), (238479, 488), (238481, 8), (238482, 0), (238483, 20), (238485, 83), (238487, 204), (238489, 24), (238491, 88), (238493, 176), (238495, 560), (238513, 20), (238515, 32), (238516, 52), (238517, 164), (238519, 428), (238521, 72), (238523, 144), (238524, 216), (238525, 240)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 238395 238527 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 103980 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 238395 238527 1248 103980 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S67

end RACert.S0N3.C0
