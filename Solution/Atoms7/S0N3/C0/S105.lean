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

namespace S105

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439678, 48), (439679, 48), (439701, 48), (439702, 48), (439703, 48), (439705, 16), (439707, 48), (439709, 48), (439710, 48), (439711, 48), (439717, 48), (439718, 24), (439719, 48), (439723, 48), (439725, 48), (439726, 48), (439727, 48), (439733, 48), (439734, 48), (439735, 48), (439739, 48), (439741, 48), (439742, 48), (439743, 48), (439766, 48), (439767, 48), (439770, 48), (439771, 48), (439774, 48), (439775, 48), (439781, 48), (439783, 48), (439785, 48), (439787, 48), (439789, 48), (439790, 24), (439791, 48), (439797, 48), (439798, 48), (439799, 48), (439801, 48), (439802, 48), (439803, 48), (439805, 48), (439806, 48), (439807, 48), (439898, 8), (439899, 48), (439903, 24), (439913, 24), (439915, 48), (439917, 48), (439919, 48), (439931, 24), (439933, 48), (439934, 48), (439935, 48), (439973, 24), (439975, 48), (439983, 24), (439989, 48), (439990, 48), (439991, 48), (439997, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 602, 431, 602, 0, 0, 0, 0, 0, 502, 602, 602, 0, 502, 0, 0, 602, 602, 602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 502, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 684, 0, 502, 684, 502, 0, 684, 0, 0, 0, 502, 602, 0, 602, 602, 602, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439678, 1002), (439679, 2318), (439705, 155), (439707, 393), (439709, 571), (439710, 100), (439711, 957), (439723, 515), (439726, 613), (439727, 1143), (439739, 1157), (439741, 1527), (439742, 1331), (439743, 2609), (439766, 138), (439767, 1105), (439770, 100), (439771, 867), (439774, 500), (439775, 1916), (439783, 1451), (439787, 997), (439790, 1262), (439791, 2401), (439797, 1476), (439798, 1367), (439799, 3007), (439801, 1187), (439802, 868), (439803, 2299), (439805, 2907), (439806, 2611), (439807, 5512), (439903, 230), (439919, 304), (439933, 541), (439934, 323), (439935, 1201), (439983, 374), (439997, 796)]

theorem l439678 : P.leaf 18 439678 = 1002 := by decide +kernel

theorem l439679 : P.leaf 18 439679 = 2318 := by decide +kernel

theorem l439705 : P.leaf 18 439705 = 155 := by decide +kernel

theorem l439707 : P.leaf 18 439707 = 393 := by decide +kernel

theorem l439709 : P.leaf 18 439709 = 571 := by decide +kernel

theorem l439710 : P.leaf 18 439710 = 100 := by decide +kernel

theorem l439711 : P.leaf 18 439711 = 957 := by decide +kernel

theorem l439723 : P.leaf 18 439723 = 515 := by decide +kernel

theorem l439726 : P.leaf 18 439726 = 613 := by decide +kernel

theorem l439727 : P.leaf 18 439727 = 1143 := by decide +kernel

theorem l439739 : P.leaf 18 439739 = 1157 := by decide +kernel

theorem l439741 : P.leaf 18 439741 = 1527 := by decide +kernel

theorem l439742 : P.leaf 18 439742 = 1331 := by decide +kernel

theorem l439743 : P.leaf 18 439743 = 2609 := by decide +kernel

theorem l439766 : P.leaf 18 439766 = 138 := by decide +kernel

theorem l439767 : P.leaf 18 439767 = 1105 := by decide +kernel

theorem l439770 : P.leaf 18 439770 = 100 := by decide +kernel

theorem l439771 : P.leaf 18 439771 = 867 := by decide +kernel

theorem l439774 : P.leaf 18 439774 = 500 := by decide +kernel

theorem l439775 : P.leaf 18 439775 = 1916 := by decide +kernel

theorem l439783 : P.leaf 18 439783 = 1451 := by decide +kernel

theorem l439787 : P.leaf 18 439787 = 997 := by decide +kernel

theorem l439790 : P.leaf 18 439790 = 1262 := by decide +kernel

theorem l439791 : P.leaf 18 439791 = 2401 := by decide +kernel

theorem l439797 : P.leaf 18 439797 = 1476 := by decide +kernel

theorem l439798 : P.leaf 18 439798 = 1367 := by decide +kernel

theorem l439799 : P.leaf 18 439799 = 3007 := by decide +kernel

theorem l439801 : P.leaf 18 439801 = 1187 := by decide +kernel

theorem l439802 : P.leaf 18 439802 = 868 := by decide +kernel

theorem l439803 : P.leaf 18 439803 = 2299 := by decide +kernel

theorem l439805 : P.leaf 18 439805 = 2907 := by decide +kernel

theorem l439806 : P.leaf 18 439806 = 2611 := by decide +kernel

theorem l439807 : P.leaf 18 439807 = 5512 := by decide +kernel

theorem l439903 : P.leaf 18 439903 = 230 := by decide +kernel

theorem l439919 : P.leaf 18 439919 = 304 := by decide +kernel

theorem l439933 : P.leaf 18 439933 = 541 := by decide +kernel

theorem l439934 : P.leaf 18 439934 = 323 := by decide +kernel

theorem l439935 : P.leaf 18 439935 = 1201 := by decide +kernel

theorem l439983 : P.leaf 18 439983 = 374 := by decide +kernel

theorem l439997 : P.leaf 18 439997 = 796 := by decide +kernel

theorem segOK : checkSeg 20 perms 439678 439998 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2356544 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439678 439998 2832 2356544 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l439678 (.cons l439679 (.cons l439705 (.cons l439707 (.cons l439709 (.cons l439710 (.cons l439711 (.cons l439723 (.cons l439726 (.cons l439727 (.cons l439739 (.cons l439741 (.cons l439742 (.cons l439743 (.cons l439766 (.cons l439767 (.cons l439770 (.cons l439771 (.cons l439774 (.cons l439775 (.cons l439783 (.cons l439787 (.cons l439790 (.cons l439791 (.cons l439797 (.cons l439798 (.cons l439799 (.cons l439801 (.cons l439802 (.cons l439803 (.cons l439805 (.cons l439806 (.cons l439807 (.cons l439903 (.cons l439919 (.cons l439933 (.cons l439934 (.cons l439935 (.cons l439983 (.cons l439997 (.nil))))))))))))))))))))))))))))))))))))))))))

end S105

end RACert.S0N3.C0
