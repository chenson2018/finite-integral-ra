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

namespace S5

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(3030, 60), (3031, 60), (3032, 60), (3033, 60), (3034, 120), (3035, 120), (3038, 60), (3039, 60), (3040, 60), (3041, 60), (3042, 120), (3043, 120), (3046, 60), (3047, 60), (3048, 60), (3049, 60), (3050, 120), (3051, 120), (3054, 60), (3055, 60), (3056, 60), (3057, 60), (3058, 120), (3059, 120), (3062, 60), (3063, 60), (3064, 60), (3065, 60), (3066, 120), (3067, 120), (3070, 60), (3071, 60), (3712, 10), (3713, 20), (3714, 30), (3715, 60), (3718, 30), (3719, 60), (3726, 10), (3727, 20)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(3030, 156), (3031, 264), (3032, 128), (3033, 169), (3034, 148), (3035, 229), (3038, 188), (3039, 301), (3040, 448), (3041, 748), (3042, 508), (3043, 884), (3046, 592), (3047, 1084), (3048, 491), (3049, 903), (3050, 574), (3051, 1100), (3054, 692), (3055, 1380), (3056, 448), (3057, 748), (3058, 508), (3059, 884), (3062, 592), (3063, 1084), (3064, 491), (3065, 903), (3066, 574), (3067, 1100), (3070, 692), (3071, 1380), (3712, 190), (3713, 136), (3714, 218), (3715, 154), (3718, 277), (3719, 189), (3726, 412), (3727, 271)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 3030 3729 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 1663590 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 3030 3729 2760 1663590 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S5

end RACert.S5N0.C0
