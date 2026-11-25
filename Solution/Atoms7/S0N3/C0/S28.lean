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

namespace S28

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(99326, 24), (99327, 24), (99669, 8), (99670, 24), (99671, 24), (99673, 24), (99674, 24), (99675, 24), (99677, 24), (99678, 24), (99679, 24), (99686, 24), (99687, 24), (99689, 24), (99690, 12), (99691, 24), (99693, 24), (99694, 24), (99695, 24), (99702, 24), (99703, 24), (99705, 24), (99706, 24), (99707, 24), (99709, 24), (99710, 24), (99711, 24), (99734, 24), (99735, 24), (99738, 12), (99739, 24), (99742, 24), (99743, 24), (99749, 24), (99750, 12), (99751, 24), (99753, 12), (99755, 24), (99757, 24), (99758, 24), (99759, 24), (99765, 24), (99766, 24), (99767, 24), (99771, 12), (99773, 24), (99774, 24), (99775, 24), (99798, 24), (99799, 24), (99802, 24), (99803, 24), (99806, 24), (99807, 24), (99813, 24), (99815, 24), (99817, 24), (99819, 24), (99821, 24), (99822, 12), (99823, 24), (99829, 24), (99830, 24), (99831, 24), (99833, 24), (99834, 24), (99835, 24), (99837, 24), (99838, 24), (99839, 24), (99930, 12), (99931, 24), (99934, 24), (99935, 24), (99945, 12), (99947, 24), (99951, 12), (99961, 24), (99962, 24), (99963, 24), (99965, 24), (99966, 24), (99967, 24), (99990, 4), (99991, 24), (99999, 12), (100023, 12), (100029, 24), (100030, 24), (100031, 24), (100085, 24), (100086, 12), (100087, 24), (100089, 12), (100091, 24), (100095, 12), (100187, 24), (100191, 24), (100201, 24), (100203, 24), (100205, 24), (100207, 24), (100217, 24), (100218, 12), (100219, 24), (100221, 24), (100222, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 424, 0, 419, 426, 440, 0, 424, 0, 518, 518, 418, 426, 440, 418, 518, 518, 0, 0, 419, 426, 440, 0, 0, 0, 424, 434, 0, 0, 424, 0, 420, 0, 434, 418, 518, 418, 518, 518, 434, 0, 434, 0, 0, 0, 0, 424, 0, 0, 0, 424, 0, 420, 518, 418, 518, 418, 518, 518, 0, 0, 0, 419, 0, 0, 0, 0, 0, 424, 440, 424, 1224, 0, 440, 0, 538, 426, 440, 1224, 1224, 1224, 0, 434, 0, 434, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 440, 0, 418, 440, 418, 0, 419, 426, 440, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(99326, 104), (99327, 248), (99669, 18), (99671, 24), (99677, 32), (99679, 32), (99702, 32), (99703, 108), (99709, 48), (99710, 48), (99711, 120), (99738, 5), (99739, 32), (99743, 32), (99750, 1), (99766, 22), (99771, 45), (99773, 48), (99774, 108), (99775, 120), (99799, 90), (99802, 5), (99803, 36), (99807, 162), (99829, 40), (99830, 172), (99831, 189), (99834, 40), (99835, 45), (99837, 144), (99838, 276), (99839, 432), (99945, 8), (99951, 16), (99990, 1), (99999, 124), (100191, 152), (100207, 56), (100221, 56), (100222, 56)]

theorem l99326 : P.leaf 18 99326 = 104 := by decide +kernel

theorem l99327 : P.leaf 18 99327 = 248 := by decide +kernel

theorem l99669 : P.leaf 18 99669 = 18 := by decide +kernel

theorem l99671 : P.leaf 18 99671 = 24 := by decide +kernel

theorem l99677 : P.leaf 18 99677 = 32 := by decide +kernel

theorem l99679 : P.leaf 18 99679 = 32 := by decide +kernel

theorem l99702 : P.leaf 18 99702 = 32 := by decide +kernel

theorem l99703 : P.leaf 18 99703 = 108 := by decide +kernel

theorem l99709 : P.leaf 18 99709 = 48 := by decide +kernel

theorem l99710 : P.leaf 18 99710 = 48 := by decide +kernel

theorem l99711 : P.leaf 18 99711 = 120 := by decide +kernel

theorem l99738 : P.leaf 18 99738 = 5 := by decide +kernel

theorem l99739 : P.leaf 18 99739 = 32 := by decide +kernel

theorem l99743 : P.leaf 18 99743 = 32 := by decide +kernel

theorem l99750 : P.leaf 18 99750 = 1 := by decide +kernel

theorem l99766 : P.leaf 18 99766 = 22 := by decide +kernel

theorem l99771 : P.leaf 18 99771 = 45 := by decide +kernel

theorem l99773 : P.leaf 18 99773 = 48 := by decide +kernel

theorem l99774 : P.leaf 18 99774 = 108 := by decide +kernel

theorem l99775 : P.leaf 18 99775 = 120 := by decide +kernel

theorem l99799 : P.leaf 18 99799 = 90 := by decide +kernel

theorem l99802 : P.leaf 18 99802 = 5 := by decide +kernel

theorem l99803 : P.leaf 18 99803 = 36 := by decide +kernel

theorem l99807 : P.leaf 18 99807 = 162 := by decide +kernel

theorem l99829 : P.leaf 18 99829 = 40 := by decide +kernel

theorem l99830 : P.leaf 18 99830 = 172 := by decide +kernel

theorem l99831 : P.leaf 18 99831 = 189 := by decide +kernel

theorem l99834 : P.leaf 18 99834 = 40 := by decide +kernel

theorem l99835 : P.leaf 18 99835 = 45 := by decide +kernel

theorem l99837 : P.leaf 18 99837 = 144 := by decide +kernel

theorem l99838 : P.leaf 18 99838 = 276 := by decide +kernel

theorem l99839 : P.leaf 18 99839 = 432 := by decide +kernel

theorem l99945 : P.leaf 18 99945 = 8 := by decide +kernel

theorem l99951 : P.leaf 18 99951 = 16 := by decide +kernel

theorem l99990 : P.leaf 18 99990 = 1 := by decide +kernel

theorem l99999 : P.leaf 18 99999 = 124 := by decide +kernel

theorem l100191 : P.leaf 18 100191 = 152 := by decide +kernel

theorem l100207 : P.leaf 18 100207 = 56 := by decide +kernel

theorem l100221 : P.leaf 18 100221 = 56 := by decide +kernel

theorem l100222 : P.leaf 18 100222 = 56 := by decide +kernel

theorem segOK : checkSeg 20 perms 99326 100223 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 77152 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 99326 100223 2352 77152 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l99326 (.cons l99327 (.cons l99669 (.cons l99671 (.cons l99677 (.cons l99679 (.cons l99702 (.cons l99703 (.cons l99709 (.cons l99710 (.cons l99711 (.cons l99738 (.cons l99739 (.cons l99743 (.cons l99750 (.cons l99766 (.cons l99771 (.cons l99773 (.cons l99774 (.cons l99775 (.cons l99799 (.cons l99802 (.cons l99803 (.cons l99807 (.cons l99829 (.cons l99830 (.cons l99831 (.cons l99834 (.cons l99835 (.cons l99837 (.cons l99838 (.cons l99839 (.cons l99945 (.cons l99951 (.cons l99990 (.cons l99999 (.cons l100191 (.cons l100207 (.cons l100221 (.cons l100222 (.nil))))))))))))))))))))))))))))))))))))))))))

end S28

end RACert.S0N3.C0
