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

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 3729 3824 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 5987090 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 3729 3824 2960 5987090 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S6

end RACert.S5N0.C0
