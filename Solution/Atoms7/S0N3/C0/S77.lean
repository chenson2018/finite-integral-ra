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

theorem l242548 : P.leaf 18 242548 = 20 := by decide +kernel

theorem l242549 : P.leaf 18 242549 = 90 := by decide +kernel

theorem l242550 : P.leaf 18 242550 = 32 := by decide +kernel

theorem l242551 : P.leaf 18 242551 = 186 := by decide +kernel

theorem l242556 : P.leaf 18 242556 = 40 := by decide +kernel

theorem l242557 : P.leaf 18 242557 = 122 := by decide +kernel

theorem l242558 : P.leaf 18 242558 = 44 := by decide +kernel

theorem l242559 : P.leaf 18 242559 = 260 := by decide +kernel

theorem l242562 : P.leaf 18 242562 = 2 := by decide +kernel

theorem l242563 : P.leaf 18 242563 = 24 := by decide +kernel

theorem l242567 : P.leaf 18 242567 = 192 := by decide +kernel

theorem l242571 : P.leaf 18 242571 = 132 := by decide +kernel

theorem l242575 : P.leaf 18 242575 = 488 := by decide +kernel

theorem l242577 : P.leaf 18 242577 = 12 := by decide +kernel

theorem l242578 : P.leaf 18 242578 = 0 := by decide +kernel

theorem l242579 : P.leaf 18 242579 = 28 := by decide +kernel

theorem l242581 : P.leaf 18 242581 = 121 := by decide +kernel

theorem l242583 : P.leaf 18 242583 = 201 := by decide +kernel

theorem l242585 : P.leaf 18 242585 = 76 := by decide +kernel

theorem l242587 : P.leaf 18 242587 = 152 := by decide +kernel

theorem l242589 : P.leaf 18 242589 = 304 := by decide +kernel

theorem l242591 : P.leaf 18 242591 = 560 := by decide +kernel

theorem l242594 : P.leaf 18 242594 = 12 := by decide +kernel

theorem l242595 : P.leaf 18 242595 = 44 := by decide +kernel

theorem l242598 : P.leaf 18 242598 = 103 := by decide +kernel

theorem l242599 : P.leaf 18 242599 = 295 := by decide +kernel

theorem l242602 : P.leaf 18 242602 = 64 := by decide +kernel

theorem l242603 : P.leaf 18 242603 = 200 := by decide +kernel

theorem l242606 : P.leaf 18 242606 = 208 := by decide +kernel

theorem l242607 : P.leaf 18 242607 = 676 := by decide +kernel

theorem l242609 : P.leaf 18 242609 = 24 := by decide +kernel

theorem l242610 : P.leaf 18 242610 = 20 := by decide +kernel

theorem l242611 : P.leaf 18 242611 = 60 := by decide +kernel

theorem l242612 : P.leaf 18 242612 = 52 := by decide +kernel

theorem l242613 : P.leaf 18 242613 = 274 := by decide +kernel

theorem l242614 : P.leaf 18 242614 = 164 := by decide +kernel

theorem l242615 : P.leaf 18 242615 = 446 := by decide +kernel

theorem l242617 : P.leaf 18 242617 = 152 := by decide +kernel

theorem l242618 : P.leaf 18 242618 = 96 := by decide +kernel

theorem l242619 : P.leaf 18 242619 = 240 := by decide +kernel

theorem segOK : checkSeg 20 perms 242548 242620 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 297120 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 242548 242620 2736 297120 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l242548 (.cons l242549 (.cons l242550 (.cons l242551 (.cons l242556 (.cons l242557 (.cons l242558 (.cons l242559 (.cons l242562 (.cons l242563 (.cons l242567 (.cons l242571 (.cons l242575 (.cons l242577 (.cons l242578 (.cons l242579 (.cons l242581 (.cons l242583 (.cons l242585 (.cons l242587 (.cons l242589 (.cons l242591 (.cons l242594 (.cons l242595 (.cons l242598 (.cons l242599 (.cons l242602 (.cons l242603 (.cons l242606 (.cons l242607 (.cons l242609 (.cons l242610 (.cons l242611 (.cons l242612 (.cons l242613 (.cons l242614 (.cons l242615 (.cons l242617 (.cons l242618 (.cons l242619 (.nil))))))))))))))))))))))))))))))))))))))))))

end S77

end RACert.S0N3.C0
