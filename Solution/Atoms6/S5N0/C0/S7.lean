/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S7

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(3824, 60), (3825, 60), (3826, 60), (3827, 60), (3828, 120), (3829, 120), (3830, 120), (3831, 120), (3836, 60), (3837, 60), (3838, 60), (3839, 60), (4064, 20), (4065, 20), (4066, 60), (4067, 60), (4070, 60), (4071, 60), (4078, 20), (4079, 20), (4080, 20), (4081, 20), (4082, 60), (4083, 60), (4086, 60), (4087, 60), (4094, 20), (4095, 20), (7104, 10), (7105, 30), (7107, 30), (7111, 10), (7112, 20), (7113, 60), (7115, 60), (7119, 20), (7128, 10), (7129, 30), (7131, 30), (7135, 10)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(3824, 3034), (3825, 6067), (3826, 3445), (3827, 6940), (3828, 3440), (3829, 6723), (3830, 4111), (3831, 8015), (3836, 4044), (3837, 7667), (3838, 4984), (3839, 9403), (4064, 21774), (4065, 65356), (4066, 25093), (4067, 75690), (4070, 29508), (4071, 89382), (4078, 35276), (4079, 107238), (4080, 22323), (4081, 68244), (4082, 25683), (4083, 78714), (4086, 30150), (4087, 92550), (4094, 35984), (4095, 110558), (7104, 837), (7105, 1037), (7107, 1370), (7111, 1883), (7112, 931), (7113, 1135), (7115, 1494), (7119, 2035), (7128, 1025), (7129, 1233), (7131, 1618), (7135, 2187)]

theorem leavesOK : P.checkLeavesR 20 qm live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 3824 7136 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 41985100 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 3824 7136 1920 41985100 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S7

end RACert.S5N0.C0
