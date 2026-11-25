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

namespace S17

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(90492, 48), (90493, 48), (90494, 48), (90495, 48), (90498, 16), (90499, 48), (90501, 48), (90502, 48), (90503, 48), (90505, 48), (90506, 48), (90507, 48), (90509, 48), (90510, 48), (90511, 48), (90515, 48), (90516, 24), (90517, 48), (90518, 48), (90519, 48), (90521, 48), (90522, 48), (90523, 48), (90524, 48), (90525, 48), (90526, 48), (90527, 48), (90531, 48), (90532, 48), (90533, 48), (90534, 48), (90535, 48), (90536, 48), (90537, 48), (90538, 48), (90539, 48), (90540, 48), (90541, 48), (90542, 48), (90543, 48), (90547, 48), (90548, 48), (90549, 48), (90550, 48), (90551, 48), (90552, 48), (90553, 48), (90554, 48), (90555, 48), (90556, 48), (90557, 48), (90558, 48), (90559, 48), (90561, 48), (90563, 48), (90565, 48), (90567, 48), (90569, 48), (90571, 48), (90573, 48), (90575, 48), (90577, 48), (90578, 48), (90579, 48), (90581, 48), (90582, 48), (90583, 48), (90585, 48), (90586, 48), (90587, 48), (90588, 24), (90589, 48), (90590, 48), (90591, 48), (90592, 48), (90593, 48), (90594, 48), (90595, 48), (90596, 48), (90597, 48), (90598, 48), (90599, 48), (90600, 48), (90601, 48), (90602, 48), (90603, 48), (90604, 48), (90605, 48), (90606, 48), (90607, 48), (90608, 48), (90609, 48), (90610, 48), (90611, 48), (90612, 48), (90613, 48), (90614, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 684, 684, 427, 628, 0, 427, 628, 418, 669, 0, 418, 669, 0, 628, 669, 0, 427, 628, 439, 669, 0, 628, 628, 669, 0, 628, 427, 0, 628, 628, 418, 418, 0, 0, 418, 418, 0, 0, 628, 427, 0, 628, 628, 628, 439, 0, 0, 628, 628, 0, 0, 439, 0, 614, 0, 418, 0, 418, 0, 439, 669, 0, 0, 669, 0, 439, 669, 0, 669, 0, 669, 0, 427, 439, 0, 0, 427, 614, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 427, 439, 0, 0, 427, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(90492, 6), (90493, 21), (90501, 0), (90507, 4), (90511, 8), (90517, 3), (90523, 8), (90527, 16), (90533, 0), (90538, 2), (90539, 8), (90542, 12), (90543, 16), (90549, 13), (90554, 6), (90555, 42), (90558, 33), (90559, 84), (90563, 1), (90567, 4), (90571, 4), (90575, 22), (90579, 4), (90581, 5), (90583, 23), (90587, 12), (90589, 24), (90591, 36), (90594, 2), (90595, 2), (90598, 8), (90599, 14), (90602, 2), (90603, 8), (90606, 32), (90607, 44), (90610, 6), (90611, 20), (90613, 15), (90614, 59)]

theorem l90492 : P.leaf 18 90492 = 6 := by decide +kernel

theorem l90493 : P.leaf 18 90493 = 21 := by decide +kernel

theorem l90501 : P.leaf 18 90501 = 0 := by decide +kernel

theorem l90507 : P.leaf 18 90507 = 4 := by decide +kernel

theorem l90511 : P.leaf 18 90511 = 8 := by decide +kernel

theorem l90517 : P.leaf 18 90517 = 3 := by decide +kernel

theorem l90523 : P.leaf 18 90523 = 8 := by decide +kernel

theorem l90527 : P.leaf 18 90527 = 16 := by decide +kernel

theorem l90533 : P.leaf 18 90533 = 0 := by decide +kernel

theorem l90538 : P.leaf 18 90538 = 2 := by decide +kernel

theorem l90539 : P.leaf 18 90539 = 8 := by decide +kernel

theorem l90542 : P.leaf 18 90542 = 12 := by decide +kernel

theorem l90543 : P.leaf 18 90543 = 16 := by decide +kernel

theorem l90549 : P.leaf 18 90549 = 13 := by decide +kernel

theorem l90554 : P.leaf 18 90554 = 6 := by decide +kernel

theorem l90555 : P.leaf 18 90555 = 42 := by decide +kernel

theorem l90558 : P.leaf 18 90558 = 33 := by decide +kernel

theorem l90559 : P.leaf 18 90559 = 84 := by decide +kernel

theorem l90563 : P.leaf 18 90563 = 1 := by decide +kernel

theorem l90567 : P.leaf 18 90567 = 4 := by decide +kernel

theorem l90571 : P.leaf 18 90571 = 4 := by decide +kernel

theorem l90575 : P.leaf 18 90575 = 22 := by decide +kernel

theorem l90579 : P.leaf 18 90579 = 4 := by decide +kernel

theorem l90581 : P.leaf 18 90581 = 5 := by decide +kernel

theorem l90583 : P.leaf 18 90583 = 23 := by decide +kernel

theorem l90587 : P.leaf 18 90587 = 12 := by decide +kernel

theorem l90589 : P.leaf 18 90589 = 24 := by decide +kernel

theorem l90591 : P.leaf 18 90591 = 36 := by decide +kernel

theorem l90594 : P.leaf 18 90594 = 2 := by decide +kernel

theorem l90595 : P.leaf 18 90595 = 2 := by decide +kernel

theorem l90598 : P.leaf 18 90598 = 8 := by decide +kernel

theorem l90599 : P.leaf 18 90599 = 14 := by decide +kernel

theorem l90602 : P.leaf 18 90602 = 2 := by decide +kernel

theorem l90603 : P.leaf 18 90603 = 8 := by decide +kernel

theorem l90606 : P.leaf 18 90606 = 32 := by decide +kernel

theorem l90607 : P.leaf 18 90607 = 44 := by decide +kernel

theorem l90610 : P.leaf 18 90610 = 6 := by decide +kernel

theorem l90611 : P.leaf 18 90611 = 20 := by decide +kernel

theorem l90613 : P.leaf 18 90613 = 15 := by decide +kernel

theorem l90614 : P.leaf 18 90614 = 59 := by decide +kernel

theorem segOK : checkSeg 20 perms 90492 90615 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 30192 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 90492 90615 4576 30192 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l90492 (.cons l90493 (.cons l90501 (.cons l90507 (.cons l90511 (.cons l90517 (.cons l90523 (.cons l90527 (.cons l90533 (.cons l90538 (.cons l90539 (.cons l90542 (.cons l90543 (.cons l90549 (.cons l90554 (.cons l90555 (.cons l90558 (.cons l90559 (.cons l90563 (.cons l90567 (.cons l90571 (.cons l90575 (.cons l90579 (.cons l90581 (.cons l90583 (.cons l90587 (.cons l90589 (.cons l90591 (.cons l90594 (.cons l90595 (.cons l90598 (.cons l90599 (.cons l90602 (.cons l90603 (.cons l90606 (.cons l90607 (.cons l90610 (.cons l90611 (.cons l90613 (.cons l90614 (.nil))))))))))))))))))))))))))))))))))))))))))

end S17

end RACert.S0N3.C0
