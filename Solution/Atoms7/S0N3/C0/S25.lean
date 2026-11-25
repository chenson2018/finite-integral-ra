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

namespace S25

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(96158, 48), (96159, 48), (96167, 48), (96175, 48), (96181, 24), (96182, 48), (96183, 48), (96189, 48), (96190, 48), (96191, 48), (96214, 48), (96215, 48), (96219, 48), (96222, 48), (96223, 48), (96235, 16), (96239, 48), (96246, 48), (96247, 48), (96253, 24), (96254, 48), (96255, 48), (96662, 8), (96663, 48), (96671, 24), (96695, 24), (96702, 48), (96703, 48), (96758, 24), (96759, 48), (96767, 24), (97183, 48), (97215, 24), (97239, 16), (97247, 48), (97278, 24), (97279, 48), (98303, 8), (98304, 4), (98305, 24), (98306, 24), (98307, 24), (98309, 24), (98310, 12), (98311, 24), (98313, 12), (98315, 24), (98319, 12), (98321, 24), (98322, 12), (98323, 24), (98324, 24), (98325, 24), (98326, 24), (98327, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 427, 628, 0, 628, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 517, 517, 538, 517, 517, 0, 517, 517, 420, 0, 0, 420, 420, 538, 538]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(96158, 82), (96159, 372), (96167, 212), (96175, 652), (96181, 142), (96182, 130), (96183, 532), (96189, 476), (96190, 648), (96191, 1112), (96214, 162), (96215, 360), (96219, 360), (96222, 614), (96223, 604), (96235, 1000), (96239, 1240), (96246, 572), (96247, 936), (96253, 926), (96254, 1118), (96255, 1816), (96671, 112), (96702, 137), (96703, 494), (96758, 214), (96759, 582), (96767, 2104), (97183, 688), (97215, 1300), (97239, 576), (97247, 1192), (97278, 1300), (97279, 2076), (98303, 3336), (98304, 10), (98305, 4), (98313, 2), (98322, 5), (98323, 16)]

theorem l96158 : P.leaf 18 96158 = 82 := by decide +kernel

theorem l96159 : P.leaf 18 96159 = 372 := by decide +kernel

theorem l96167 : P.leaf 18 96167 = 212 := by decide +kernel

theorem l96175 : P.leaf 18 96175 = 652 := by decide +kernel

theorem l96181 : P.leaf 18 96181 = 142 := by decide +kernel

theorem l96182 : P.leaf 18 96182 = 130 := by decide +kernel

theorem l96183 : P.leaf 18 96183 = 532 := by decide +kernel

theorem l96189 : P.leaf 18 96189 = 476 := by decide +kernel

theorem l96190 : P.leaf 18 96190 = 648 := by decide +kernel

theorem l96191 : P.leaf 18 96191 = 1112 := by decide +kernel

theorem l96214 : P.leaf 18 96214 = 162 := by decide +kernel

theorem l96215 : P.leaf 18 96215 = 360 := by decide +kernel

theorem l96219 : P.leaf 18 96219 = 360 := by decide +kernel

theorem l96222 : P.leaf 18 96222 = 614 := by decide +kernel

theorem l96223 : P.leaf 18 96223 = 604 := by decide +kernel

theorem l96235 : P.leaf 18 96235 = 1000 := by decide +kernel

theorem l96239 : P.leaf 18 96239 = 1240 := by decide +kernel

theorem l96246 : P.leaf 18 96246 = 572 := by decide +kernel

theorem l96247 : P.leaf 18 96247 = 936 := by decide +kernel

theorem l96253 : P.leaf 18 96253 = 926 := by decide +kernel

theorem l96254 : P.leaf 18 96254 = 1118 := by decide +kernel

theorem l96255 : P.leaf 18 96255 = 1816 := by decide +kernel

theorem l96671 : P.leaf 18 96671 = 112 := by decide +kernel

theorem l96702 : P.leaf 18 96702 = 137 := by decide +kernel

theorem l96703 : P.leaf 18 96703 = 494 := by decide +kernel

theorem l96758 : P.leaf 18 96758 = 214 := by decide +kernel

theorem l96759 : P.leaf 18 96759 = 582 := by decide +kernel

theorem l96767 : P.leaf 18 96767 = 2104 := by decide +kernel

theorem l97183 : P.leaf 18 97183 = 688 := by decide +kernel

theorem l97215 : P.leaf 18 97215 = 1300 := by decide +kernel

theorem l97239 : P.leaf 18 97239 = 576 := by decide +kernel

theorem l97247 : P.leaf 18 97247 = 1192 := by decide +kernel

theorem l97278 : P.leaf 18 97278 = 1300 := by decide +kernel

theorem l97279 : P.leaf 18 97279 = 2076 := by decide +kernel

theorem l98303 : P.leaf 18 98303 = 3336 := by decide +kernel

theorem l98304 : P.leaf 18 98304 = 10 := by decide +kernel

theorem l98305 : P.leaf 18 98305 = 4 := by decide +kernel

theorem l98313 : P.leaf 18 98313 = 2 := by decide +kernel

theorem l98322 : P.leaf 18 98322 = 5 := by decide +kernel

theorem l98323 : P.leaf 18 98323 = 16 := by decide +kernel

theorem segOK : checkSeg 20 perms 96158 98328 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1022876 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 96158 98328 1828 1022876 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l96158 (.cons l96159 (.cons l96167 (.cons l96175 (.cons l96181 (.cons l96182 (.cons l96183 (.cons l96189 (.cons l96190 (.cons l96191 (.cons l96214 (.cons l96215 (.cons l96219 (.cons l96222 (.cons l96223 (.cons l96235 (.cons l96239 (.cons l96246 (.cons l96247 (.cons l96253 (.cons l96254 (.cons l96255 (.cons l96671 (.cons l96702 (.cons l96703 (.cons l96758 (.cons l96759 (.cons l96767 (.cons l97183 (.cons l97215 (.cons l97239 (.cons l97247 (.cons l97278 (.cons l97279 (.cons l98303 (.cons l98304 (.cons l98305 (.cons l98313 (.cons l98322 (.cons l98323 (.nil))))))))))))))))))))))))))))))))))))))))))

end S25

end RACert.S0N3.C0
