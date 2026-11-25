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

namespace S124

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(517113, 24), (517114, 24), (517115, 24), (517116, 12), (517117, 24), (517118, 24), (517119, 24), (517461, 24), (517462, 12), (517463, 24), (517465, 12), (517466, 24), (517467, 24), (517469, 24), (517470, 24), (517471, 24), (517477, 12), (517479, 24), (517481, 24), (517482, 24), (517483, 24), (517485, 24), (517486, 24), (517487, 24), (517495, 12), (517497, 24), (517498, 24), (517499, 24), (517501, 24), (517502, 24), (517503, 24), (517525, 12), (517526, 24), (517527, 24), (517530, 24), (517531, 24), (517533, 24), (517534, 24), (517535, 24), (517541, 24), (517543, 24), (517546, 8), (517547, 24), (517549, 24), (517550, 24), (517551, 24), (517557, 24), (517558, 24), (517559, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 440, 0, 0, 0, 0, 0, 418, 440, 440, 418, 0, 0, 0, 0, 440, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(517113, 596), (517114, 1744), (517115, 2000), (517116, 816), (517117, 1246), (517118, 3736), (517119, 5394), (517461, 554), (517462, 541), (517463, 1539), (517465, 130), (517469, 689), (517470, 705), (517471, 1539), (517477, 23), (517479, 829), (517486, 806), (517487, 988), (517495, 2570), (517497, 266), (517501, 941), (517502, 1823), (517503, 2612), (517525, 1088), (517526, 1010), (517527, 2432), (517530, 822), (517531, 1660), (517533, 1484), (517534, 1812), (517535, 3580), (517541, 139), (517543, 1153), (517546, 918), (517547, 1203), (517550, 2085), (517551, 2175), (517557, 1312), (517558, 2793), (517559, 4071)]

theorem l517113 : P.leaf 18 517113 = 596 := by decide +kernel

theorem l517114 : P.leaf 18 517114 = 1744 := by decide +kernel

theorem l517115 : P.leaf 18 517115 = 2000 := by decide +kernel

theorem l517116 : P.leaf 18 517116 = 816 := by decide +kernel

theorem l517117 : P.leaf 18 517117 = 1246 := by decide +kernel

theorem l517118 : P.leaf 18 517118 = 3736 := by decide +kernel

theorem l517119 : P.leaf 18 517119 = 5394 := by decide +kernel

theorem l517461 : P.leaf 18 517461 = 554 := by decide +kernel

theorem l517462 : P.leaf 18 517462 = 541 := by decide +kernel

theorem l517463 : P.leaf 18 517463 = 1539 := by decide +kernel

theorem l517465 : P.leaf 18 517465 = 130 := by decide +kernel

theorem l517469 : P.leaf 18 517469 = 689 := by decide +kernel

theorem l517470 : P.leaf 18 517470 = 705 := by decide +kernel

theorem l517471 : P.leaf 18 517471 = 1539 := by decide +kernel

theorem l517477 : P.leaf 18 517477 = 23 := by decide +kernel

theorem l517479 : P.leaf 18 517479 = 829 := by decide +kernel

theorem l517486 : P.leaf 18 517486 = 806 := by decide +kernel

theorem l517487 : P.leaf 18 517487 = 988 := by decide +kernel

theorem l517495 : P.leaf 18 517495 = 2570 := by decide +kernel

theorem l517497 : P.leaf 18 517497 = 266 := by decide +kernel

theorem l517501 : P.leaf 18 517501 = 941 := by decide +kernel

theorem l517502 : P.leaf 18 517502 = 1823 := by decide +kernel

theorem l517503 : P.leaf 18 517503 = 2612 := by decide +kernel

theorem l517525 : P.leaf 18 517525 = 1088 := by decide +kernel

theorem l517526 : P.leaf 18 517526 = 1010 := by decide +kernel

theorem l517527 : P.leaf 18 517527 = 2432 := by decide +kernel

theorem l517530 : P.leaf 18 517530 = 822 := by decide +kernel

theorem l517531 : P.leaf 18 517531 = 1660 := by decide +kernel

theorem l517533 : P.leaf 18 517533 = 1484 := by decide +kernel

theorem l517534 : P.leaf 18 517534 = 1812 := by decide +kernel

theorem l517535 : P.leaf 18 517535 = 3580 := by decide +kernel

theorem l517541 : P.leaf 18 517541 = 139 := by decide +kernel

theorem l517543 : P.leaf 18 517543 = 1153 := by decide +kernel

theorem l517546 : P.leaf 18 517546 = 918 := by decide +kernel

theorem l517547 : P.leaf 18 517547 = 1203 := by decide +kernel

theorem l517550 : P.leaf 18 517550 = 2085 := by decide +kernel

theorem l517551 : P.leaf 18 517551 = 2175 := by decide +kernel

theorem l517557 : P.leaf 18 517557 = 1312 := by decide +kernel

theorem l517558 : P.leaf 18 517558 = 2793 := by decide +kernel

theorem l517559 : P.leaf 18 517559 = 4071 := by decide +kernel

theorem segOK : checkSeg 20 perms 517113 517563 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1407072 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 517113 517563 1088 1407072 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l517113 (.cons l517114 (.cons l517115 (.cons l517116 (.cons l517117 (.cons l517118 (.cons l517119 (.cons l517461 (.cons l517462 (.cons l517463 (.cons l517465 (.cons l517469 (.cons l517470 (.cons l517471 (.cons l517477 (.cons l517479 (.cons l517486 (.cons l517487 (.cons l517495 (.cons l517497 (.cons l517501 (.cons l517502 (.cons l517503 (.cons l517525 (.cons l517526 (.cons l517527 (.cons l517530 (.cons l517531 (.cons l517533 (.cons l517534 (.cons l517535 (.cons l517541 (.cons l517543 (.cons l517546 (.cons l517547 (.cons l517550 (.cons l517551 (.cons l517557 (.cons l517558 (.cons l517559 (.nil))))))))))))))))))))))))))))))))))))))))))

end S124

end RACert.S0N3.C0
