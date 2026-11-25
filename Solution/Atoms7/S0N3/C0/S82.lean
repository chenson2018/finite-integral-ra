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

namespace S82

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(243582, 48), (243583, 48), (243586, 48), (243587, 48), (243590, 48), (243591, 48), (243594, 48), (243595, 48), (243598, 48), (243599, 48), (243602, 48), (243603, 48), (243606, 48), (243607, 48), (243610, 48), (243611, 48), (243614, 48), (243615, 48), (243618, 48), (243619, 48), (243622, 48), (243623, 48), (243626, 48), (243627, 48), (243630, 48), (243631, 48), (243634, 48), (243635, 48), (243637, 24), (243638, 48), (243639, 48), (243642, 48), (243643, 48), (243645, 48), (243646, 48), (243647, 48), (243650, 48), (243651, 48), (243654, 48), (243655, 48), (243658, 48), (243659, 48), (243662, 48), (243663, 48), (243666, 48), (243667, 48), (243670, 48), (243671, 48), (243674, 48), (243675, 48), (243678, 48), (243679, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 424, 0, 424, 0, 424, 0, 0, 0, 424, 0, 424, 0, 424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 424, 0, 424, 0, 424, 0, 0, 0, 424, 0, 424, 0, 424, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(243582, 386), (243583, 2062), (243586, 6), (243587, 82), (243591, 937), (243595, 391), (243599, 1544), (243602, 0), (243603, 122), (243607, 1265), (243611, 566), (243615, 2271), (243618, 78), (243619, 252), (243622, 681), (243623, 2076), (243626, 316), (243627, 924), (243630, 1144), (243631, 3414), (243634, 138), (243635, 368), (243637, 2112), (243638, 1182), (243639, 3582), (243642, 476), (243643, 1232), (243645, 2660), (243646, 1686), (243647, 5414), (243650, 24), (243651, 124), (243655, 1463), (243659, 411), (243663, 1856), (243666, 77), (243667, 190), (243671, 2058), (243675, 670), (243679, 2906)]

theorem l243582 : P.leaf 18 243582 = 386 := by decide +kernel

theorem l243583 : P.leaf 18 243583 = 2062 := by decide +kernel

theorem l243586 : P.leaf 18 243586 = 6 := by decide +kernel

theorem l243587 : P.leaf 18 243587 = 82 := by decide +kernel

theorem l243591 : P.leaf 18 243591 = 937 := by decide +kernel

theorem l243595 : P.leaf 18 243595 = 391 := by decide +kernel

theorem l243599 : P.leaf 18 243599 = 1544 := by decide +kernel

theorem l243602 : P.leaf 18 243602 = 0 := by decide +kernel

theorem l243603 : P.leaf 18 243603 = 122 := by decide +kernel

theorem l243607 : P.leaf 18 243607 = 1265 := by decide +kernel

theorem l243611 : P.leaf 18 243611 = 566 := by decide +kernel

theorem l243615 : P.leaf 18 243615 = 2271 := by decide +kernel

theorem l243618 : P.leaf 18 243618 = 78 := by decide +kernel

theorem l243619 : P.leaf 18 243619 = 252 := by decide +kernel

theorem l243622 : P.leaf 18 243622 = 681 := by decide +kernel

theorem l243623 : P.leaf 18 243623 = 2076 := by decide +kernel

theorem l243626 : P.leaf 18 243626 = 316 := by decide +kernel

theorem l243627 : P.leaf 18 243627 = 924 := by decide +kernel

theorem l243630 : P.leaf 18 243630 = 1144 := by decide +kernel

theorem l243631 : P.leaf 18 243631 = 3414 := by decide +kernel

theorem l243634 : P.leaf 18 243634 = 138 := by decide +kernel

theorem l243635 : P.leaf 18 243635 = 368 := by decide +kernel

theorem l243637 : P.leaf 18 243637 = 2112 := by decide +kernel

theorem l243638 : P.leaf 18 243638 = 1182 := by decide +kernel

theorem l243639 : P.leaf 18 243639 = 3582 := by decide +kernel

theorem l243642 : P.leaf 18 243642 = 476 := by decide +kernel

theorem l243643 : P.leaf 18 243643 = 1232 := by decide +kernel

theorem l243645 : P.leaf 18 243645 = 2660 := by decide +kernel

theorem l243646 : P.leaf 18 243646 = 1686 := by decide +kernel

theorem l243647 : P.leaf 18 243647 = 5414 := by decide +kernel

theorem l243650 : P.leaf 18 243650 = 24 := by decide +kernel

theorem l243651 : P.leaf 18 243651 = 124 := by decide +kernel

theorem l243655 : P.leaf 18 243655 = 1463 := by decide +kernel

theorem l243659 : P.leaf 18 243659 = 411 := by decide +kernel

theorem l243663 : P.leaf 18 243663 = 1856 := by decide +kernel

theorem l243666 : P.leaf 18 243666 = 77 := by decide +kernel

theorem l243667 : P.leaf 18 243667 = 190 := by decide +kernel

theorem l243671 : P.leaf 18 243671 = 2058 := by decide +kernel

theorem l243675 : P.leaf 18 243675 = 670 := by decide +kernel

theorem l243679 : P.leaf 18 243679 = 2906 := by decide +kernel

theorem segOK : checkSeg 20 perms 243582 243682 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2212320 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 243582 243682 2472 2212320 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l243582 (.cons l243583 (.cons l243586 (.cons l243587 (.cons l243591 (.cons l243595 (.cons l243599 (.cons l243602 (.cons l243603 (.cons l243607 (.cons l243611 (.cons l243615 (.cons l243618 (.cons l243619 (.cons l243622 (.cons l243623 (.cons l243626 (.cons l243627 (.cons l243630 (.cons l243631 (.cons l243634 (.cons l243635 (.cons l243637 (.cons l243638 (.cons l243639 (.cons l243642 (.cons l243643 (.cons l243645 (.cons l243646 (.cons l243647 (.cons l243650 (.cons l243651 (.cons l243655 (.cons l243659 (.cons l243663 (.cons l243666 (.cons l243667 (.cons l243671 (.cons l243675 (.cons l243679 (.nil))))))))))))))))))))))))))))))))))))))))))

end S82

end RACert.S0N3.C0
