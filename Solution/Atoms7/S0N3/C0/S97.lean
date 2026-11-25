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

namespace S97

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(430396, 24), (430397, 48), (430399, 24), (430401, 16), (430402, 16), (430403, 48), (430405, 48), (430406, 48), (430407, 48), (430409, 48), (430410, 48), (430411, 48), (430413, 48), (430414, 48), (430415, 48), (430419, 48), (430420, 48), (430421, 48), (430422, 48), (430423, 48), (430424, 24), (430425, 48), (430426, 48), (430427, 48), (430428, 48), (430429, 48), (430430, 48), (430431, 48), (430435, 48), (430437, 48), (430438, 48), (430439, 48), (430440, 24), (430441, 48), (430442, 48), (430443, 48), (430444, 48), (430445, 48), (430446, 48), (430447, 48), (430451, 48), (430452, 48), (430453, 48), (430454, 48), (430455, 48), (430456, 48), (430457, 48), (430458, 48), (430459, 48), (430460, 48), (430461, 48), (430462, 48), (430463, 48), (430531, 24), (430535, 48), (430543, 24), (430545, 48), (430546, 48), (430547, 48), (430549, 48), (430550, 48), (430551, 48), (430553, 48), (430554, 48), (430555, 48), (430556, 24), (430557, 48), (430558, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 439, 0, 587, 518, 0, 0, 439, 0, 587, 518, 0, 0, 587, 573, 0, 573, 0, 0, 587, 0, 587, 573, 0, 573, 0, 587, 518, 0, 0, 518, 439, 0, 587, 518, 518, 0, 0, 587, 0, 0, 0, 0, 0, 587, 0, 587, 0, 0, 0, 0, 0, 0, 0, 0, 573, 0, 0, 573, 0, 0, 573, 0, 573, 0, 573]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(430396, 65), (430397, 65), (430399, 190), (430402, 0), (430406, 0), (430407, 4), (430410, 0), (430414, 0), (430415, 16), (430421, 2), (430423, 26), (430424, 0), (430426, 0), (430429, 26), (430431, 92), (430438, 5), (430439, 26), (430442, 0), (430446, 26), (430447, 92), (430452, 4), (430453, 13), (430454, 39), (430455, 105), (430456, 0), (430458, 0), (430460, 142), (430461, 142), (430462, 142), (430463, 304), (430531, 9), (430535, 10), (430543, 42), (430545, 8), (430547, 139), (430549, 26), (430551, 222), (430553, 45), (430555, 222), (430557, 175)]

theorem l430396 : P.leaf 18 430396 = 65 := by decide +kernel

theorem l430397 : P.leaf 18 430397 = 65 := by decide +kernel

theorem l430399 : P.leaf 18 430399 = 190 := by decide +kernel

theorem l430402 : P.leaf 18 430402 = 0 := by decide +kernel

theorem l430406 : P.leaf 18 430406 = 0 := by decide +kernel

theorem l430407 : P.leaf 18 430407 = 4 := by decide +kernel

theorem l430410 : P.leaf 18 430410 = 0 := by decide +kernel

theorem l430414 : P.leaf 18 430414 = 0 := by decide +kernel

theorem l430415 : P.leaf 18 430415 = 16 := by decide +kernel

theorem l430421 : P.leaf 18 430421 = 2 := by decide +kernel

theorem l430423 : P.leaf 18 430423 = 26 := by decide +kernel

theorem l430424 : P.leaf 18 430424 = 0 := by decide +kernel

theorem l430426 : P.leaf 18 430426 = 0 := by decide +kernel

theorem l430429 : P.leaf 18 430429 = 26 := by decide +kernel

theorem l430431 : P.leaf 18 430431 = 92 := by decide +kernel

theorem l430438 : P.leaf 18 430438 = 5 := by decide +kernel

theorem l430439 : P.leaf 18 430439 = 26 := by decide +kernel

theorem l430442 : P.leaf 18 430442 = 0 := by decide +kernel

theorem l430446 : P.leaf 18 430446 = 26 := by decide +kernel

theorem l430447 : P.leaf 18 430447 = 92 := by decide +kernel

theorem l430452 : P.leaf 18 430452 = 4 := by decide +kernel

theorem l430453 : P.leaf 18 430453 = 13 := by decide +kernel

theorem l430454 : P.leaf 18 430454 = 39 := by decide +kernel

theorem l430455 : P.leaf 18 430455 = 105 := by decide +kernel

theorem l430456 : P.leaf 18 430456 = 0 := by decide +kernel

theorem l430458 : P.leaf 18 430458 = 0 := by decide +kernel

theorem l430460 : P.leaf 18 430460 = 142 := by decide +kernel

theorem l430461 : P.leaf 18 430461 = 142 := by decide +kernel

theorem l430462 : P.leaf 18 430462 = 142 := by decide +kernel

theorem l430463 : P.leaf 18 430463 = 304 := by decide +kernel

theorem l430531 : P.leaf 18 430531 = 9 := by decide +kernel

theorem l430535 : P.leaf 18 430535 = 10 := by decide +kernel

theorem l430543 : P.leaf 18 430543 = 42 := by decide +kernel

theorem l430545 : P.leaf 18 430545 = 8 := by decide +kernel

theorem l430547 : P.leaf 18 430547 = 139 := by decide +kernel

theorem l430549 : P.leaf 18 430549 = 26 := by decide +kernel

theorem l430551 : P.leaf 18 430551 = 222 := by decide +kernel

theorem l430553 : P.leaf 18 430553 = 45 := by decide +kernel

theorem l430555 : P.leaf 18 430555 = 222 := by decide +kernel

theorem l430557 : P.leaf 18 430557 = 175 := by decide +kernel

theorem segOK : checkSeg 20 perms 430396 430559 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 109008 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 430396 430559 3032 109008 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l430396 (.cons l430397 (.cons l430399 (.cons l430402 (.cons l430406 (.cons l430407 (.cons l430410 (.cons l430414 (.cons l430415 (.cons l430421 (.cons l430423 (.cons l430424 (.cons l430426 (.cons l430429 (.cons l430431 (.cons l430438 (.cons l430439 (.cons l430442 (.cons l430446 (.cons l430447 (.cons l430452 (.cons l430453 (.cons l430454 (.cons l430455 (.cons l430456 (.cons l430458 (.cons l430460 (.cons l430461 (.cons l430462 (.cons l430463 (.cons l430531 (.cons l430535 (.cons l430543 (.cons l430545 (.cons l430547 (.cons l430549 (.cons l430551 (.cons l430553 (.cons l430555 (.cons l430557 (.nil))))))))))))))))))))))))))))))))))))))))))

end S97

end RACert.S0N3.C0
