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

namespace S6

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(3729, 10), (3731, 30), (3735, 30), (3743, 10), (3744, 60), (3745, 60), (3746, 120), (3747, 120), (3750, 60), (3751, 60), (3752, 60), (3753, 60), (3754, 120), (3755, 120), (3758, 60), (3759, 60), (3760, 60), (3761, 60), (3762, 120), (3763, 120), (3766, 60), (3767, 60), (3768, 60), (3769, 60), (3770, 120), (3771, 120), (3774, 60), (3775, 60), (3808, 60), (3809, 60), (3810, 60), (3811, 60), (3812, 120), (3813, 120), (3814, 120), (3815, 120), (3820, 60), (3821, 60), (3822, 60), (3823, 60)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(3729, 373), (3731, 424), (3735, 537), (3743, 793), (3744, 394), (3745, 619), (3746, 403), (3747, 627), (3750, 411), (3751, 635), (3752, 445), (3753, 700), (3754, 469), (3755, 736), (3758, 513), (3759, 799), (3760, 504), (3761, 877), (3762, 517), (3763, 895), (3766, 529), (3767, 913), (3768, 576), (3769, 1009), (3770, 612), (3771, 1074), (3774, 664), (3775, 1178), (3808, 2620), (3809, 5113), (3810, 2993), (3811, 5876), (3812, 2980), (3813, 5723), (3814, 3591), (3815, 6889), (3820, 3526), (3821, 6603), (3822, 4384), (3823, 8197)]

theorem l3729 : P.leaf 20 3729 = 373 := by decide +kernel

theorem l3731 : P.leaf 20 3731 = 424 := by decide +kernel

theorem l3735 : P.leaf 20 3735 = 537 := by decide +kernel

theorem l3743 : P.leaf 20 3743 = 793 := by decide +kernel

theorem l3744 : P.leaf 20 3744 = 394 := by decide +kernel

theorem l3745 : P.leaf 20 3745 = 619 := by decide +kernel

theorem l3746 : P.leaf 20 3746 = 403 := by decide +kernel

theorem l3747 : P.leaf 20 3747 = 627 := by decide +kernel

theorem l3750 : P.leaf 20 3750 = 411 := by decide +kernel

theorem l3751 : P.leaf 20 3751 = 635 := by decide +kernel

theorem l3752 : P.leaf 20 3752 = 445 := by decide +kernel

theorem l3753 : P.leaf 20 3753 = 700 := by decide +kernel

theorem l3754 : P.leaf 20 3754 = 469 := by decide +kernel

theorem l3755 : P.leaf 20 3755 = 736 := by decide +kernel

theorem l3758 : P.leaf 20 3758 = 513 := by decide +kernel

theorem l3759 : P.leaf 20 3759 = 799 := by decide +kernel

theorem l3760 : P.leaf 20 3760 = 504 := by decide +kernel

theorem l3761 : P.leaf 20 3761 = 877 := by decide +kernel

theorem l3762 : P.leaf 20 3762 = 517 := by decide +kernel

theorem l3763 : P.leaf 20 3763 = 895 := by decide +kernel

theorem l3766 : P.leaf 20 3766 = 529 := by decide +kernel

theorem l3767 : P.leaf 20 3767 = 913 := by decide +kernel

theorem l3768 : P.leaf 20 3768 = 576 := by decide +kernel

theorem l3769 : P.leaf 20 3769 = 1009 := by decide +kernel

theorem l3770 : P.leaf 20 3770 = 612 := by decide +kernel

theorem l3771 : P.leaf 20 3771 = 1074 := by decide +kernel

theorem l3774 : P.leaf 20 3774 = 664 := by decide +kernel

theorem l3775 : P.leaf 20 3775 = 1178 := by decide +kernel

theorem l3808 : P.leaf 20 3808 = 2620 := by decide +kernel

theorem l3809 : P.leaf 20 3809 = 5113 := by decide +kernel

theorem l3810 : P.leaf 20 3810 = 2993 := by decide +kernel

theorem l3811 : P.leaf 20 3811 = 5876 := by decide +kernel

theorem l3812 : P.leaf 20 3812 = 2980 := by decide +kernel

theorem l3813 : P.leaf 20 3813 = 5723 := by decide +kernel

theorem l3814 : P.leaf 20 3814 = 3591 := by decide +kernel

theorem l3815 : P.leaf 20 3815 = 6889 := by decide +kernel

theorem l3820 : P.leaf 20 3820 = 3526 := by decide +kernel

theorem l3821 : P.leaf 20 3821 = 6603 := by decide +kernel

theorem l3822 : P.leaf 20 3822 = 4384 := by decide +kernel

theorem l3823 : P.leaf 20 3823 = 8197 := by decide +kernel

theorem segOK : checkSeg 15 perms 3729 3824 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 5987090 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 3729 3824 2960 5987090 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l3729 (.cons l3731 (.cons l3735 (.cons l3743 (.cons l3744 (.cons l3745 (.cons l3746 (.cons l3747 (.cons l3750 (.cons l3751 (.cons l3752 (.cons l3753 (.cons l3754 (.cons l3755 (.cons l3758 (.cons l3759 (.cons l3760 (.cons l3761 (.cons l3762 (.cons l3763 (.cons l3766 (.cons l3767 (.cons l3768 (.cons l3769 (.cons l3770 (.cons l3771 (.cons l3774 (.cons l3775 (.cons l3808 (.cons l3809 (.cons l3810 (.cons l3811 (.cons l3812 (.cons l3813 (.cons l3814 (.cons l3815 (.cons l3820 (.cons l3821 (.cons l3822 (.cons l3823 (.nil))))))))))))))))))))))))))))))))))))))))))

end S6

end RACert.S5N0.C0
