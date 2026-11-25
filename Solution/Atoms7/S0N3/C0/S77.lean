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

namespace S77

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(242548, 48), (242549, 48), (242550, 48), (242551, 48), (242552, 24), (242553, 48), (242554, 48), (242555, 48), (242556, 48), (242557, 48), (242558, 48), (242559, 48), (242561, 48), (242562, 48), (242563, 48), (242565, 48), (242566, 48), (242567, 48), (242569, 48), (242570, 48), (242571, 48), (242573, 48), (242574, 48), (242575, 48), (242577, 48), (242578, 48), (242579, 48), (242581, 48), (242582, 48), (242583, 48), (242585, 48), (242586, 48), (242587, 48), (242589, 48), (242590, 48), (242591, 48), (242593, 48), (242594, 48), (242595, 48), (242597, 48), (242598, 48), (242599, 48), (242601, 48), (242602, 48), (242603, 48), (242605, 48), (242606, 48), (242607, 48), (242609, 48), (242610, 48), (242611, 48), (242612, 24), (242613, 48), (242614, 48), (242615, 48), (242617, 48), (242618, 48), (242619, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 552, 439, 438, 671, 0, 0, 0, 0, 502, 0, 0, 502, 424, 0, 502, 424, 0, 502, 424, 0, 0, 0, 0, 0, 424, 0, 0, 424, 0, 0, 424, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(242548, 20), (242549, 90), (242550, 32), (242551, 186), (242556, 40), (242557, 122), (242558, 44), (242559, 260), (242562, 2), (242563, 24), (242567, 192), (242571, 132), (242575, 488), (242577, 12), (242578, 0), (242579, 28), (242581, 121), (242583, 201), (242585, 76), (242587, 152), (242589, 304), (242591, 560), (242594, 12), (242595, 44), (242598, 103), (242599, 295), (242602, 64), (242603, 200), (242606, 208), (242607, 676), (242609, 24), (242610, 20), (242611, 60), (242612, 52), (242613, 274), (242614, 164), (242615, 446), (242617, 152), (242618, 96), (242619, 240)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 242548 242620 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 297120 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 242548 242620 2736 297120 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S77

end RACert.S0N3.C0
