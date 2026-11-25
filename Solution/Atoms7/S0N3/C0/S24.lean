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

namespace S24

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(95230, 48), (95231, 48), (95573, 48), (95574, 24), (95575, 48), (95577, 24), (95578, 48), (95579, 48), (95581, 48), (95582, 48), (95583, 48), (95589, 24), (95591, 48), (95593, 48), (95594, 48), (95595, 48), (95597, 48), (95598, 48), (95599, 48), (95607, 24), (95609, 48), (95610, 48), (95611, 48), (95613, 48), (95614, 48), (95615, 48), (95637, 24), (95638, 48), (95639, 48), (95642, 48), (95643, 48), (95645, 48), (95646, 48), (95647, 48), (95653, 48), (95655, 48), (95658, 16), (95659, 48), (95661, 48), (95662, 48), (95663, 48), (95669, 48), (95670, 48), (95671, 48), (95675, 48), (95677, 48), (95678, 48), (95679, 48), (95702, 48), (95703, 48), (95706, 48), (95707, 48), (95709, 24), (95710, 48), (95711, 48), (95717, 48), (95719, 48), (95721, 48), (95723, 48), (95725, 48), (95727, 48), (95733, 48), (95734, 48), (95735, 48), (95737, 48), (95738, 48), (95739, 48), (95741, 48), (95742, 48), (95743, 48), (95834, 24), (95835, 48), (95838, 48), (95839, 48), (95849, 8), (95851, 48), (95855, 24), (95867, 24), (95869, 48), (95870, 48), (95871, 48), (95894, 24), (95895, 48), (95903, 24), (95925, 48), (95926, 48), (95927, 48), (95933, 48), (95934, 48), (95935, 48), (95989, 48), (95990, 24), (95991, 48), (95993, 24), (95995, 48), (95999, 24), (96094, 24), (96095, 48), (96111, 48), (96127, 24), (96150, 48), (96151, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 684, 684, 684, 439, 438, 440, 684, 684, 684, 432, 684, 418, 438, 440, 418, 684, 684, 684, 439, 438, 440, 684, 684, 684, 0, 427, 0, 0, 0, 0, 0, 0, 432, 0, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 432, 0, 418, 0, 418, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 438, 440, 574, 574, 502, 440, 663, 440, 684, 684, 684, 1350, 581, 574, 581, 427, 581, 581, 581, 581, 1224, 427, 1224, 1224, 1224, 1224, 684, 684, 684, 684, 427, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(95230, 288), (95231, 440), (95637, 7), (95639, 32), (95642, 12), (95643, 92), (95645, 50), (95646, 21), (95647, 118), (95655, 48), (95658, 95), (95659, 258), (95662, 133), (95663, 292), (95669, 33), (95670, 44), (95671, 204), (95675, 350), (95677, 132), (95678, 250), (95679, 462), (95702, 51), (95703, 186), (95706, 62), (95707, 180), (95709, 105), (95710, 187), (95711, 284), (95719, 216), (95723, 540), (95727, 684), (95733, 162), (95734, 292), (95735, 544), (95738, 326), (95739, 684), (95741, 287), (95742, 539), (95743, 964), (96151, 88)]

theorem l95230 : P.leaf 18 95230 = 288 := by decide +kernel

theorem l95231 : P.leaf 18 95231 = 440 := by decide +kernel

theorem l95637 : P.leaf 18 95637 = 7 := by decide +kernel

theorem l95639 : P.leaf 18 95639 = 32 := by decide +kernel

theorem l95642 : P.leaf 18 95642 = 12 := by decide +kernel

theorem l95643 : P.leaf 18 95643 = 92 := by decide +kernel

theorem l95645 : P.leaf 18 95645 = 50 := by decide +kernel

theorem l95646 : P.leaf 18 95646 = 21 := by decide +kernel

theorem l95647 : P.leaf 18 95647 = 118 := by decide +kernel

theorem l95655 : P.leaf 18 95655 = 48 := by decide +kernel

theorem l95658 : P.leaf 18 95658 = 95 := by decide +kernel

theorem l95659 : P.leaf 18 95659 = 258 := by decide +kernel

theorem l95662 : P.leaf 18 95662 = 133 := by decide +kernel

theorem l95663 : P.leaf 18 95663 = 292 := by decide +kernel

theorem l95669 : P.leaf 18 95669 = 33 := by decide +kernel

theorem l95670 : P.leaf 18 95670 = 44 := by decide +kernel

theorem l95671 : P.leaf 18 95671 = 204 := by decide +kernel

theorem l95675 : P.leaf 18 95675 = 350 := by decide +kernel

theorem l95677 : P.leaf 18 95677 = 132 := by decide +kernel

theorem l95678 : P.leaf 18 95678 = 250 := by decide +kernel

theorem l95679 : P.leaf 18 95679 = 462 := by decide +kernel

theorem l95702 : P.leaf 18 95702 = 51 := by decide +kernel

theorem l95703 : P.leaf 18 95703 = 186 := by decide +kernel

theorem l95706 : P.leaf 18 95706 = 62 := by decide +kernel

theorem l95707 : P.leaf 18 95707 = 180 := by decide +kernel

theorem l95709 : P.leaf 18 95709 = 105 := by decide +kernel

theorem l95710 : P.leaf 18 95710 = 187 := by decide +kernel

theorem l95711 : P.leaf 18 95711 = 284 := by decide +kernel

theorem l95719 : P.leaf 18 95719 = 216 := by decide +kernel

theorem l95723 : P.leaf 18 95723 = 540 := by decide +kernel

theorem l95727 : P.leaf 18 95727 = 684 := by decide +kernel

theorem l95733 : P.leaf 18 95733 = 162 := by decide +kernel

theorem l95734 : P.leaf 18 95734 = 292 := by decide +kernel

theorem l95735 : P.leaf 18 95735 = 544 := by decide +kernel

theorem l95738 : P.leaf 18 95738 = 326 := by decide +kernel

theorem l95739 : P.leaf 18 95739 = 684 := by decide +kernel

theorem l95741 : P.leaf 18 95741 = 287 := by decide +kernel

theorem l95742 : P.leaf 18 95742 = 539 := by decide +kernel

theorem l95743 : P.leaf 18 95743 = 964 := by decide +kernel

theorem l96151 : P.leaf 18 96151 = 88 := by decide +kernel

theorem segOK : checkSeg 20 perms 95230 96158 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 461888 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 95230 96158 4440 461888 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l95230 (.cons l95231 (.cons l95637 (.cons l95639 (.cons l95642 (.cons l95643 (.cons l95645 (.cons l95646 (.cons l95647 (.cons l95655 (.cons l95658 (.cons l95659 (.cons l95662 (.cons l95663 (.cons l95669 (.cons l95670 (.cons l95671 (.cons l95675 (.cons l95677 (.cons l95678 (.cons l95679 (.cons l95702 (.cons l95703 (.cons l95706 (.cons l95707 (.cons l95709 (.cons l95710 (.cons l95711 (.cons l95719 (.cons l95723 (.cons l95727 (.cons l95733 (.cons l95734 (.cons l95735 (.cons l95738 (.cons l95739 (.cons l95741 (.cons l95742 (.cons l95743 (.cons l96151 (.nil))))))))))))))))))))))))))))))))))))))))))

end S24

end RACert.S0N3.C0
