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

theorem l3824 : P.leaf 20 3824 = 3034 := by decide +kernel

theorem l3825 : P.leaf 20 3825 = 6067 := by decide +kernel

theorem l3826 : P.leaf 20 3826 = 3445 := by decide +kernel

theorem l3827 : P.leaf 20 3827 = 6940 := by decide +kernel

theorem l3828 : P.leaf 20 3828 = 3440 := by decide +kernel

theorem l3829 : P.leaf 20 3829 = 6723 := by decide +kernel

theorem l3830 : P.leaf 20 3830 = 4111 := by decide +kernel

theorem l3831 : P.leaf 20 3831 = 8015 := by decide +kernel

theorem l3836 : P.leaf 20 3836 = 4044 := by decide +kernel

theorem l3837 : P.leaf 20 3837 = 7667 := by decide +kernel

theorem l3838 : P.leaf 20 3838 = 4984 := by decide +kernel

theorem l3839 : P.leaf 20 3839 = 9403 := by decide +kernel

theorem l4064 : P.leaf 20 4064 = 21774 := by decide +kernel

theorem l4065 : P.leaf 20 4065 = 65356 := by decide +kernel

theorem l4066 : P.leaf 20 4066 = 25093 := by decide +kernel

theorem l4067 : P.leaf 20 4067 = 75690 := by decide +kernel

theorem l4070 : P.leaf 20 4070 = 29508 := by decide +kernel

theorem l4071 : P.leaf 20 4071 = 89382 := by decide +kernel

theorem l4078 : P.leaf 20 4078 = 35276 := by decide +kernel

theorem l4079 : P.leaf 20 4079 = 107238 := by decide +kernel

theorem l4080 : P.leaf 20 4080 = 22323 := by decide +kernel

theorem l4081 : P.leaf 20 4081 = 68244 := by decide +kernel

theorem l4082 : P.leaf 20 4082 = 25683 := by decide +kernel

theorem l4083 : P.leaf 20 4083 = 78714 := by decide +kernel

theorem l4086 : P.leaf 20 4086 = 30150 := by decide +kernel

theorem l4087 : P.leaf 20 4087 = 92550 := by decide +kernel

theorem l4094 : P.leaf 20 4094 = 35984 := by decide +kernel

theorem l4095 : P.leaf 20 4095 = 110558 := by decide +kernel

theorem l7104 : P.leaf 20 7104 = 837 := by decide +kernel

theorem l7105 : P.leaf 20 7105 = 1037 := by decide +kernel

theorem l7107 : P.leaf 20 7107 = 1370 := by decide +kernel

theorem l7111 : P.leaf 20 7111 = 1883 := by decide +kernel

theorem l7112 : P.leaf 20 7112 = 931 := by decide +kernel

theorem l7113 : P.leaf 20 7113 = 1135 := by decide +kernel

theorem l7115 : P.leaf 20 7115 = 1494 := by decide +kernel

theorem l7119 : P.leaf 20 7119 = 2035 := by decide +kernel

theorem l7128 : P.leaf 20 7128 = 1025 := by decide +kernel

theorem l7129 : P.leaf 20 7129 = 1233 := by decide +kernel

theorem l7131 : P.leaf 20 7131 = 1618 := by decide +kernel

theorem l7135 : P.leaf 20 7135 = 2187 := by decide +kernel

theorem segOK : checkSeg 15 perms 3824 7136 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 41985100 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 3824 7136 1920 41985100 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l3824 (.cons l3825 (.cons l3826 (.cons l3827 (.cons l3828 (.cons l3829 (.cons l3830 (.cons l3831 (.cons l3836 (.cons l3837 (.cons l3838 (.cons l3839 (.cons l4064 (.cons l4065 (.cons l4066 (.cons l4067 (.cons l4070 (.cons l4071 (.cons l4078 (.cons l4079 (.cons l4080 (.cons l4081 (.cons l4082 (.cons l4083 (.cons l4086 (.cons l4087 (.cons l4094 (.cons l4095 (.cons l7104 (.cons l7105 (.cons l7107 (.cons l7111 (.cons l7112 (.cons l7113 (.cons l7115 (.cons l7119 (.cons l7128 (.cons l7129 (.cons l7131 (.cons l7135 (.nil))))))))))))))))))))))))))))))))))))))))))

end S7

end RACert.S5N0.C0
