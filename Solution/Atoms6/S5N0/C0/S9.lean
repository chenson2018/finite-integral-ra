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

namespace S9

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(7594, 120), (7595, 120), (7596, 120), (7597, 120), (7598, 120), (7599, 120), (7608, 60), (7609, 60), (7610, 120), (7611, 120), (7614, 60), (7615, 60), (7648, 60), (7649, 120), (7651, 60), (7652, 120), (7653, 120), (7654, 120), (7655, 120), (7660, 60), (7661, 120), (7663, 60), (7664, 60), (7665, 120), (7667, 60), (7668, 120), (7669, 120), (7670, 120), (7671, 120), (7676, 60), (7677, 120), (7679, 60), (8128, 30), (8129, 30), (8130, 60), (8131, 60), (8134, 30), (8135, 30), (8136, 60), (8137, 60)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(7594, 5898), (7595, 7578), (7596, 5919), (7597, 7591), (7598, 8970), (7599, 11498), (7608, 4107), (7609, 5252), (7610, 6138), (7611, 7875), (7614, 9319), (7615, 11937), (7648, 12472), (7649, 19438), (7651, 30988), (7652, 15866), (7653, 24613), (7654, 25542), (7655, 40306), (7660, 20772), (7661, 33196), (7663, 53364), (7664, 12720), (7665, 19942), (7667, 31922), (7668, 16160), (7669, 25251), (7670, 26088), (7671, 41299), (7676, 21120), (7677, 33874), (7679, 54416), (8128, 25688), (8129, 45506), (8130, 31344), (8131, 54662), (8134, 38737), (8135, 66373), (8136, 30952), (8137, 55967)]

theorem l7594 : P.leaf 20 7594 = 5898 := by decide +kernel

theorem l7595 : P.leaf 20 7595 = 7578 := by decide +kernel

theorem l7596 : P.leaf 20 7596 = 5919 := by decide +kernel

theorem l7597 : P.leaf 20 7597 = 7591 := by decide +kernel

theorem l7598 : P.leaf 20 7598 = 8970 := by decide +kernel

theorem l7599 : P.leaf 20 7599 = 11498 := by decide +kernel

theorem l7608 : P.leaf 20 7608 = 4107 := by decide +kernel

theorem l7609 : P.leaf 20 7609 = 5252 := by decide +kernel

theorem l7610 : P.leaf 20 7610 = 6138 := by decide +kernel

theorem l7611 : P.leaf 20 7611 = 7875 := by decide +kernel

theorem l7614 : P.leaf 20 7614 = 9319 := by decide +kernel

theorem l7615 : P.leaf 20 7615 = 11937 := by decide +kernel

theorem l7648 : P.leaf 20 7648 = 12472 := by decide +kernel

theorem l7649 : P.leaf 20 7649 = 19438 := by decide +kernel

theorem l7651 : P.leaf 20 7651 = 30988 := by decide +kernel

theorem l7652 : P.leaf 20 7652 = 15866 := by decide +kernel

theorem l7653 : P.leaf 20 7653 = 24613 := by decide +kernel

theorem l7654 : P.leaf 20 7654 = 25542 := by decide +kernel

theorem l7655 : P.leaf 20 7655 = 40306 := by decide +kernel

theorem l7660 : P.leaf 20 7660 = 20772 := by decide +kernel

theorem l7661 : P.leaf 20 7661 = 33196 := by decide +kernel

theorem l7663 : P.leaf 20 7663 = 53364 := by decide +kernel

theorem l7664 : P.leaf 20 7664 = 12720 := by decide +kernel

theorem l7665 : P.leaf 20 7665 = 19942 := by decide +kernel

theorem l7667 : P.leaf 20 7667 = 31922 := by decide +kernel

theorem l7668 : P.leaf 20 7668 = 16160 := by decide +kernel

theorem l7669 : P.leaf 20 7669 = 25251 := by decide +kernel

theorem l7670 : P.leaf 20 7670 = 26088 := by decide +kernel

theorem l7671 : P.leaf 20 7671 = 41299 := by decide +kernel

theorem l7676 : P.leaf 20 7676 = 21120 := by decide +kernel

theorem l7677 : P.leaf 20 7677 = 33874 := by decide +kernel

theorem l7679 : P.leaf 20 7679 = 54416 := by decide +kernel

theorem l8128 : P.leaf 20 8128 = 25688 := by decide +kernel

theorem l8129 : P.leaf 20 8129 = 45506 := by decide +kernel

theorem l8130 : P.leaf 20 8130 = 31344 := by decide +kernel

theorem l8131 : P.leaf 20 8131 = 54662 := by decide +kernel

theorem l8134 : P.leaf 20 8134 = 38737 := by decide +kernel

theorem l8135 : P.leaf 20 8135 = 66373 := by decide +kernel

theorem l8136 : P.leaf 20 8136 = 30952 := by decide +kernel

theorem l8137 : P.leaf 20 8137 = 55967 := by decide +kernel

theorem segOK : checkSeg 15 perms 7594 8138 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 77733000 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 7594 8138 3480 77733000 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l7594 (.cons l7595 (.cons l7596 (.cons l7597 (.cons l7598 (.cons l7599 (.cons l7608 (.cons l7609 (.cons l7610 (.cons l7611 (.cons l7614 (.cons l7615 (.cons l7648 (.cons l7649 (.cons l7651 (.cons l7652 (.cons l7653 (.cons l7654 (.cons l7655 (.cons l7660 (.cons l7661 (.cons l7663 (.cons l7664 (.cons l7665 (.cons l7667 (.cons l7668 (.cons l7669 (.cons l7670 (.cons l7671 (.cons l7676 (.cons l7677 (.cons l7679 (.cons l8128 (.cons l8129 (.cons l8130 (.cons l8131 (.cons l8134 (.cons l8135 (.cons l8136 (.cons l8137 (.nil))))))))))))))))))))))))))))))))))))))))))

end S9

end RACert.S5N0.C0
