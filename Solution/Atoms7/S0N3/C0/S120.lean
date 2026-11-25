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

namespace S120

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516575, 24), (516576, 24), (516577, 24), (516578, 24), (516579, 24), (516580, 24), (516581, 24), (516582, 24), (516583, 24), (516584, 24), (516585, 24), (516586, 24), (516587, 24), (516588, 24), (516589, 24), (516590, 24), (516591, 24), (516592, 24), (516593, 24), (516594, 24), (516595, 24), (516596, 24), (516597, 24), (516598, 24), (516599, 24), (516600, 24), (516601, 24), (516602, 24), (516603, 24), (516604, 24), (516605, 24), (516606, 24), (516607, 24), (516617, 24), (516619, 24), (516621, 24), (516623, 24), (516633, 24), (516634, 12), (516635, 24), (516637, 24), (516638, 24), (516639, 24), (516649, 12), (516651, 24), (516652, 24), (516653, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 418]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516575, 3921), (516576, 0), (516577, 47), (516578, 232), (516579, 527), (516580, 76), (516581, 104), (516582, 1287), (516583, 1427), (516586, 649), (516587, 722), (516590, 2026), (516591, 2118), (516592, 67), (516593, 305), (516594, 488), (516595, 1136), (516596, 288), (516597, 821), (516598, 2761), (516599, 3184), (516600, 127), (516601, 351), (516602, 1154), (516603, 1475), (516604, 737), (516605, 1104), (516606, 3492), (516607, 5394), (516617, 42), (516619, 40), (516623, 0), (516633, 40), (516634, 108), (516635, 216), (516637, 0), (516638, 0), (516639, 0), (516649, 90), (516651, 82)]

theorem l516575 : P.leaf 18 516575 = 3921 := by decide +kernel

theorem l516576 : P.leaf 18 516576 = 0 := by decide +kernel

theorem l516577 : P.leaf 18 516577 = 47 := by decide +kernel

theorem l516578 : P.leaf 18 516578 = 232 := by decide +kernel

theorem l516579 : P.leaf 18 516579 = 527 := by decide +kernel

theorem l516580 : P.leaf 18 516580 = 76 := by decide +kernel

theorem l516581 : P.leaf 18 516581 = 104 := by decide +kernel

theorem l516582 : P.leaf 18 516582 = 1287 := by decide +kernel

theorem l516583 : P.leaf 18 516583 = 1427 := by decide +kernel

theorem l516586 : P.leaf 18 516586 = 649 := by decide +kernel

theorem l516587 : P.leaf 18 516587 = 722 := by decide +kernel

theorem l516590 : P.leaf 18 516590 = 2026 := by decide +kernel

theorem l516591 : P.leaf 18 516591 = 2118 := by decide +kernel

theorem l516592 : P.leaf 18 516592 = 67 := by decide +kernel

theorem l516593 : P.leaf 18 516593 = 305 := by decide +kernel

theorem l516594 : P.leaf 18 516594 = 488 := by decide +kernel

theorem l516595 : P.leaf 18 516595 = 1136 := by decide +kernel

theorem l516596 : P.leaf 18 516596 = 288 := by decide +kernel

theorem l516597 : P.leaf 18 516597 = 821 := by decide +kernel

theorem l516598 : P.leaf 18 516598 = 2761 := by decide +kernel

theorem l516599 : P.leaf 18 516599 = 3184 := by decide +kernel

theorem l516600 : P.leaf 18 516600 = 127 := by decide +kernel

theorem l516601 : P.leaf 18 516601 = 351 := by decide +kernel

theorem l516602 : P.leaf 18 516602 = 1154 := by decide +kernel

theorem l516603 : P.leaf 18 516603 = 1475 := by decide +kernel

theorem l516604 : P.leaf 18 516604 = 737 := by decide +kernel

theorem l516605 : P.leaf 18 516605 = 1104 := by decide +kernel

theorem l516606 : P.leaf 18 516606 = 3492 := by decide +kernel

theorem l516607 : P.leaf 18 516607 = 5394 := by decide +kernel

theorem l516617 : P.leaf 18 516617 = 42 := by decide +kernel

theorem l516619 : P.leaf 18 516619 = 40 := by decide +kernel

theorem l516623 : P.leaf 18 516623 = 0 := by decide +kernel

theorem l516633 : P.leaf 18 516633 = 40 := by decide +kernel

theorem l516634 : P.leaf 18 516634 = 108 := by decide +kernel

theorem l516635 : P.leaf 18 516635 = 216 := by decide +kernel

theorem l516637 : P.leaf 18 516637 = 0 := by decide +kernel

theorem l516638 : P.leaf 18 516638 = 0 := by decide +kernel

theorem l516639 : P.leaf 18 516639 = 0 := by decide +kernel

theorem l516649 : P.leaf 18 516649 = 90 := by decide +kernel

theorem l516651 : P.leaf 18 516651 = 82 := by decide +kernel

theorem segOK : checkSeg 20 perms 516575 516654 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 876936 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516575 516654 1104 876936 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l516575 (.cons l516576 (.cons l516577 (.cons l516578 (.cons l516579 (.cons l516580 (.cons l516581 (.cons l516582 (.cons l516583 (.cons l516586 (.cons l516587 (.cons l516590 (.cons l516591 (.cons l516592 (.cons l516593 (.cons l516594 (.cons l516595 (.cons l516596 (.cons l516597 (.cons l516598 (.cons l516599 (.cons l516600 (.cons l516601 (.cons l516602 (.cons l516603 (.cons l516604 (.cons l516605 (.cons l516606 (.cons l516607 (.cons l516617 (.cons l516619 (.cons l516623 (.cons l516633 (.cons l516634 (.cons l516635 (.cons l516637 (.cons l516638 (.cons l516639 (.cons l516649 (.cons l516651 (.nil))))))))))))))))))))))))))))))))))))))))))

end S120

end RACert.S0N3.C0
