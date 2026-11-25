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

namespace S68

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(238527, 12), (238529, 24), (238531, 12), (238533, 24), (238535, 12), (238537, 24), (238539, 12), (238541, 24), (238543, 12), (238545, 24), (238546, 24), (238547, 24), (238549, 24), (238550, 24), (238551, 24), (238553, 24), (238554, 24), (238555, 24), (238557, 24), (238558, 24), (238559, 24), (238577, 24), (238579, 12), (238581, 24), (238583, 12), (238585, 24), (238587, 12), (238588, 6), (238589, 24), (238591, 12), (238593, 12), (238594, 12), (238595, 24), (238597, 24), (238598, 24), (238599, 24), (238601, 24), (238602, 24), (238603, 24), (238605, 24), (238606, 24), (238607, 24), (238609, 24), (238610, 24), (238611, 24), (238613, 24), (238614, 24), (238615, 24), (238617, 24), (238618, 24), (238619, 24), (238621, 24), (238622, 24), (238623, 24), (238625, 24), (238626, 24), (238627, 24), (238629, 24), (238630, 24), (238631, 24), (238633, 24), (238634, 24), (238635, 24), (238637, 24), (238638, 24), (238639, 24), (238641, 24), (238642, 24), (238643, 24), (238645, 24), (238646, 24), (238647, 24), (238649, 24), (238650, 24), (238651, 24), (238653, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 418, 0, 418, 0, 418, 0, 0, 0, 0, 0, 424, 0, 0, 424, 0, 0, 424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 573, 434, 440, 573, 517, 517, 573, 426, 440, 573, 517, 517, 538, 434, 440, 0, 0, 0, 538, 426, 440, 0, 0, 0, 0, 434, 440, 517, 0, 0, 0, 426, 440, 517, 0, 0, 538, 434, 440, 0, 0, 0, 538, 426, 440, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(238527, 752), (238529, 7), (238531, 70), (238535, 935), (238539, 146), (238543, 1264), (238545, 24), (238546, 14), (238547, 68), (238549, 323), (238551, 1114), (238553, 48), (238555, 160), (238557, 445), (238559, 1483), (238577, 56), (238579, 164), (238581, 524), (238583, 2008), (238585, 96), (238587, 312), (238588, 440), (238589, 636), (238591, 2762), (238613, 4), (238614, 1), (238615, 15), (238621, 4), (238622, 4), (238623, 20), (238625, 4), (238630, 2), (238631, 12), (238633, 5), (238638, 2), (238639, 17), (238645, 7), (238646, 3), (238647, 87), (238653, 8)]

theorem l238527 : P.leaf 18 238527 = 752 := by decide +kernel

theorem l238529 : P.leaf 18 238529 = 7 := by decide +kernel

theorem l238531 : P.leaf 18 238531 = 70 := by decide +kernel

theorem l238535 : P.leaf 18 238535 = 935 := by decide +kernel

theorem l238539 : P.leaf 18 238539 = 146 := by decide +kernel

theorem l238543 : P.leaf 18 238543 = 1264 := by decide +kernel

theorem l238545 : P.leaf 18 238545 = 24 := by decide +kernel

theorem l238546 : P.leaf 18 238546 = 14 := by decide +kernel

theorem l238547 : P.leaf 18 238547 = 68 := by decide +kernel

theorem l238549 : P.leaf 18 238549 = 323 := by decide +kernel

theorem l238551 : P.leaf 18 238551 = 1114 := by decide +kernel

theorem l238553 : P.leaf 18 238553 = 48 := by decide +kernel

theorem l238555 : P.leaf 18 238555 = 160 := by decide +kernel

theorem l238557 : P.leaf 18 238557 = 445 := by decide +kernel

theorem l238559 : P.leaf 18 238559 = 1483 := by decide +kernel

theorem l238577 : P.leaf 18 238577 = 56 := by decide +kernel

theorem l238579 : P.leaf 18 238579 = 164 := by decide +kernel

theorem l238581 : P.leaf 18 238581 = 524 := by decide +kernel

theorem l238583 : P.leaf 18 238583 = 2008 := by decide +kernel

theorem l238585 : P.leaf 18 238585 = 96 := by decide +kernel

theorem l238587 : P.leaf 18 238587 = 312 := by decide +kernel

theorem l238588 : P.leaf 18 238588 = 440 := by decide +kernel

theorem l238589 : P.leaf 18 238589 = 636 := by decide +kernel

theorem l238591 : P.leaf 18 238591 = 2762 := by decide +kernel

theorem l238613 : P.leaf 18 238613 = 4 := by decide +kernel

theorem l238614 : P.leaf 18 238614 = 1 := by decide +kernel

theorem l238615 : P.leaf 18 238615 = 15 := by decide +kernel

theorem l238621 : P.leaf 18 238621 = 4 := by decide +kernel

theorem l238622 : P.leaf 18 238622 = 4 := by decide +kernel

theorem l238623 : P.leaf 18 238623 = 20 := by decide +kernel

theorem l238625 : P.leaf 18 238625 = 4 := by decide +kernel

theorem l238630 : P.leaf 18 238630 = 2 := by decide +kernel

theorem l238631 : P.leaf 18 238631 = 12 := by decide +kernel

theorem l238633 : P.leaf 18 238633 = 5 := by decide +kernel

theorem l238638 : P.leaf 18 238638 = 2 := by decide +kernel

theorem l238639 : P.leaf 18 238639 = 17 := by decide +kernel

theorem l238645 : P.leaf 18 238645 = 7 := by decide +kernel

theorem l238646 : P.leaf 18 238646 = 3 := by decide +kernel

theorem l238647 : P.leaf 18 238647 = 87 := by decide +kernel

theorem l238653 : P.leaf 18 238653 = 8 := by decide +kernel

theorem segOK : checkSeg 20 perms 238527 238654 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 228228 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 238527 238654 1674 228228 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l238527 (.cons l238529 (.cons l238531 (.cons l238535 (.cons l238539 (.cons l238543 (.cons l238545 (.cons l238546 (.cons l238547 (.cons l238549 (.cons l238551 (.cons l238553 (.cons l238555 (.cons l238557 (.cons l238559 (.cons l238577 (.cons l238579 (.cons l238581 (.cons l238583 (.cons l238585 (.cons l238587 (.cons l238588 (.cons l238589 (.cons l238591 (.cons l238613 (.cons l238614 (.cons l238615 (.cons l238621 (.cons l238622 (.cons l238623 (.cons l238625 (.cons l238630 (.cons l238631 (.cons l238633 (.cons l238638 (.cons l238639 (.cons l238645 (.cons l238646 (.cons l238647 (.cons l238653 (.nil))))))))))))))))))))))))))))))))))))))))))

end S68

end RACert.S0N3.C0
