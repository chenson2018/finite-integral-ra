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

namespace S87

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(244647, 48), (244651, 48), (244655, 48), (244659, 48), (244662, 24), (244663, 48), (244667, 48), (244670, 48), (244671, 48), (244675, 48), (244679, 48), (244683, 48), (244687, 48), (244691, 48), (244695, 48), (244699, 48), (244703, 48), (244707, 48), (244711, 48), (244715, 48), (244719, 48), (244723, 48), (244727, 48), (244731, 48), (244734, 24), (244735, 48), (244739, 24), (244743, 48), (244747, 48), (244751, 48), (244755, 48), (244759, 48), (244763, 48), (244767, 48), (244771, 48), (244775, 48), (244779, 48), (244783, 48), (244787, 48), (244791, 48), (244795, 48), (244799, 48), (244807, 48), (244811, 24), (244815, 48), (244819, 48), (244823, 48), (244827, 48), (244831, 48), (244835, 48), (244839, 48), (244843, 48), (244847, 48), (244851, 48), (244855, 48), (244859, 48), (244863, 48), (244871, 24), (244879, 48), (244883, 48), (244887, 48), (244891, 48), (244895, 48), (244899, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 663, 440, 663, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 663, 440, 663, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 663, 663, 669, 0, 669, 0, 663]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(244647, 1314), (244651, 408), (244655, 1958), (244659, 120), (244662, 928), (244663, 2384), (244667, 528), (244670, 1060), (244671, 3116), (244675, 59), (244679, 1116), (244683, 232), (244687, 1426), (244691, 70), (244695, 1432), (244699, 300), (244703, 1888), (244707, 112), (244711, 1928), (244715, 456), (244719, 2590), (244723, 144), (244727, 2812), (244731, 596), (244734, 1212), (244735, 3896), (244759, 54), (244767, 80), (244775, 28), (244783, 36), (244791, 171), (244799, 280), (244823, 174), (244831, 232), (244839, 84), (244847, 108), (244855, 898), (244863, 1005), (244887, 295), (244895, 500)]

theorem l244647 : P.leaf 18 244647 = 1314 := by decide +kernel

theorem l244651 : P.leaf 18 244651 = 408 := by decide +kernel

theorem l244655 : P.leaf 18 244655 = 1958 := by decide +kernel

theorem l244659 : P.leaf 18 244659 = 120 := by decide +kernel

theorem l244662 : P.leaf 18 244662 = 928 := by decide +kernel

theorem l244663 : P.leaf 18 244663 = 2384 := by decide +kernel

theorem l244667 : P.leaf 18 244667 = 528 := by decide +kernel

theorem l244670 : P.leaf 18 244670 = 1060 := by decide +kernel

theorem l244671 : P.leaf 18 244671 = 3116 := by decide +kernel

theorem l244675 : P.leaf 18 244675 = 59 := by decide +kernel

theorem l244679 : P.leaf 18 244679 = 1116 := by decide +kernel

theorem l244683 : P.leaf 18 244683 = 232 := by decide +kernel

theorem l244687 : P.leaf 18 244687 = 1426 := by decide +kernel

theorem l244691 : P.leaf 18 244691 = 70 := by decide +kernel

theorem l244695 : P.leaf 18 244695 = 1432 := by decide +kernel

theorem l244699 : P.leaf 18 244699 = 300 := by decide +kernel

theorem l244703 : P.leaf 18 244703 = 1888 := by decide +kernel

theorem l244707 : P.leaf 18 244707 = 112 := by decide +kernel

theorem l244711 : P.leaf 18 244711 = 1928 := by decide +kernel

theorem l244715 : P.leaf 18 244715 = 456 := by decide +kernel

theorem l244719 : P.leaf 18 244719 = 2590 := by decide +kernel

theorem l244723 : P.leaf 18 244723 = 144 := by decide +kernel

theorem l244727 : P.leaf 18 244727 = 2812 := by decide +kernel

theorem l244731 : P.leaf 18 244731 = 596 := by decide +kernel

theorem l244734 : P.leaf 18 244734 = 1212 := by decide +kernel

theorem l244735 : P.leaf 18 244735 = 3896 := by decide +kernel

theorem l244759 : P.leaf 18 244759 = 54 := by decide +kernel

theorem l244767 : P.leaf 18 244767 = 80 := by decide +kernel

theorem l244775 : P.leaf 18 244775 = 28 := by decide +kernel

theorem l244783 : P.leaf 18 244783 = 36 := by decide +kernel

theorem l244791 : P.leaf 18 244791 = 171 := by decide +kernel

theorem l244799 : P.leaf 18 244799 = 280 := by decide +kernel

theorem l244823 : P.leaf 18 244823 = 174 := by decide +kernel

theorem l244831 : P.leaf 18 244831 = 232 := by decide +kernel

theorem l244839 : P.leaf 18 244839 = 84 := by decide +kernel

theorem l244847 : P.leaf 18 244847 = 108 := by decide +kernel

theorem l244855 : P.leaf 18 244855 = 898 := by decide +kernel

theorem l244863 : P.leaf 18 244863 = 1005 := by decide +kernel

theorem l244887 : P.leaf 18 244887 = 295 := by decide +kernel

theorem l244895 : P.leaf 18 244895 = 500 := by decide +kernel

theorem segOK : checkSeg 20 perms 244647 244903 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1678080 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 244647 244903 2952 1678080 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l244647 (.cons l244651 (.cons l244655 (.cons l244659 (.cons l244662 (.cons l244663 (.cons l244667 (.cons l244670 (.cons l244671 (.cons l244675 (.cons l244679 (.cons l244683 (.cons l244687 (.cons l244691 (.cons l244695 (.cons l244699 (.cons l244703 (.cons l244707 (.cons l244711 (.cons l244715 (.cons l244719 (.cons l244723 (.cons l244727 (.cons l244731 (.cons l244734 (.cons l244735 (.cons l244759 (.cons l244767 (.cons l244775 (.cons l244783 (.cons l244791 (.cons l244799 (.cons l244823 (.cons l244831 (.cons l244839 (.cons l244847 (.cons l244855 (.cons l244863 (.cons l244887 (.cons l244895 (.nil))))))))))))))))))))))))))))))))))))))))))

end S87

end RACert.S0N3.C0
