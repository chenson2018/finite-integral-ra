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

namespace S118

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516459, 24), (516460, 24), (516461, 24), (516462, 24), (516463, 24), (516464, 24), (516465, 24), (516466, 24), (516467, 24), (516468, 24), (516469, 24), (516470, 24), (516471, 24), (516472, 24), (516473, 24), (516474, 24), (516475, 24), (516476, 24), (516477, 24), (516478, 24), (516479, 24), (516482, 8), (516483, 24), (516485, 24), (516486, 24), (516487, 24), (516489, 24), (516490, 24), (516491, 24), (516493, 24), (516494, 24), (516495, 24), (516499, 24), (516500, 12), (516501, 24), (516502, 24), (516503, 24), (516505, 24), (516506, 24), (516507, 24), (516508, 24), (516509, 24), (516510, 24), (516511, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516459, 117), (516462, 494), (516463, 626), (516464, 0), (516465, 60), (516466, 171), (516467, 275), (516468, 44), (516469, 185), (516470, 598), (516471, 728), (516472, 0), (516473, 0), (516474, 222), (516475, 418), (516476, 171), (516477, 216), (516478, 1057), (516479, 1301), (516482, 2), (516483, 10), (516485, 22), (516486, 24), (516487, 26), (516490, 9), (516491, 20), (516494, 36), (516495, 36), (516499, 106), (516500, 39), (516501, 117), (516502, 285), (516503, 390), (516505, 85), (516506, 222), (516507, 300), (516508, 216), (516509, 234), (516510, 595), (516511, 705)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 516459 516515 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 243388 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516459 516515 1028 243388 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S118

end RACert.S0N3.C0
