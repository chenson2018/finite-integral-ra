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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 96158 98328 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1022876 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 96158 98328 1828 1022876 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S25

end RACert.S0N3.C0
