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

namespace S67

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(238395, 12), (238396, 12), (238397, 24), (238399, 12), (238401, 24), (238403, 12), (238405, 24), (238407, 12), (238409, 24), (238411, 12), (238413, 24), (238415, 12), (238417, 24), (238418, 24), (238419, 24), (238421, 24), (238422, 24), (238423, 24), (238425, 24), (238426, 24), (238427, 24), (238429, 24), (238430, 24), (238431, 24), (238449, 24), (238451, 12), (238452, 12), (238453, 24), (238455, 12), (238456, 6), (238457, 24), (238459, 12), (238460, 12), (238461, 24), (238463, 12), (238465, 24), (238467, 12), (238469, 24), (238471, 12), (238473, 24), (238475, 12), (238477, 24), (238479, 12), (238481, 24), (238482, 24), (238483, 24), (238485, 24), (238486, 24), (238487, 24), (238489, 24), (238490, 24), (238491, 24), (238493, 24), (238494, 24), (238495, 24), (238513, 24), (238515, 12), (238516, 6), (238517, 24), (238519, 12), (238521, 24), (238523, 12), (238524, 12), (238525, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 419, 538, 418, 0, 418, 538, 418, 0, 419, 426, 538, 0, 424, 0, 419, 424, 538, 0, 424, 0, 419, 538, 0, 0, 0, 0, 419, 538, 0, 0, 0, 0, 0, 418, 0, 418, 0, 418, 0, 0, 0, 0, 0, 424, 0, 0, 424, 0, 0, 424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(238395, 136), (238396, 20), (238397, 24), (238399, 144), (238407, 190), (238415, 331), (238421, 35), (238423, 247), (238429, 53), (238431, 363), (238452, 20), (238453, 40), (238455, 541), (238456, 96), (238460, 40), (238461, 60), (238463, 590), (238465, 3), (238467, 20), (238471, 195), (238475, 88), (238479, 488), (238481, 8), (238482, 0), (238483, 20), (238485, 83), (238487, 204), (238489, 24), (238491, 88), (238493, 176), (238495, 560), (238513, 20), (238515, 32), (238516, 52), (238517, 164), (238519, 428), (238521, 72), (238523, 144), (238524, 216), (238525, 240)]

theorem l238395 : P.leaf 18 238395 = 136 := by decide +kernel

theorem l238396 : P.leaf 18 238396 = 20 := by decide +kernel

theorem l238397 : P.leaf 18 238397 = 24 := by decide +kernel

theorem l238399 : P.leaf 18 238399 = 144 := by decide +kernel

theorem l238407 : P.leaf 18 238407 = 190 := by decide +kernel

theorem l238415 : P.leaf 18 238415 = 331 := by decide +kernel

theorem l238421 : P.leaf 18 238421 = 35 := by decide +kernel

theorem l238423 : P.leaf 18 238423 = 247 := by decide +kernel

theorem l238429 : P.leaf 18 238429 = 53 := by decide +kernel

theorem l238431 : P.leaf 18 238431 = 363 := by decide +kernel

theorem l238452 : P.leaf 18 238452 = 20 := by decide +kernel

theorem l238453 : P.leaf 18 238453 = 40 := by decide +kernel

theorem l238455 : P.leaf 18 238455 = 541 := by decide +kernel

theorem l238456 : P.leaf 18 238456 = 96 := by decide +kernel

theorem l238460 : P.leaf 18 238460 = 40 := by decide +kernel

theorem l238461 : P.leaf 18 238461 = 60 := by decide +kernel

theorem l238463 : P.leaf 18 238463 = 590 := by decide +kernel

theorem l238465 : P.leaf 18 238465 = 3 := by decide +kernel

theorem l238467 : P.leaf 18 238467 = 20 := by decide +kernel

theorem l238471 : P.leaf 18 238471 = 195 := by decide +kernel

theorem l238475 : P.leaf 18 238475 = 88 := by decide +kernel

theorem l238479 : P.leaf 18 238479 = 488 := by decide +kernel

theorem l238481 : P.leaf 18 238481 = 8 := by decide +kernel

theorem l238482 : P.leaf 18 238482 = 0 := by decide +kernel

theorem l238483 : P.leaf 18 238483 = 20 := by decide +kernel

theorem l238485 : P.leaf 18 238485 = 83 := by decide +kernel

theorem l238487 : P.leaf 18 238487 = 204 := by decide +kernel

theorem l238489 : P.leaf 18 238489 = 24 := by decide +kernel

theorem l238491 : P.leaf 18 238491 = 88 := by decide +kernel

theorem l238493 : P.leaf 18 238493 = 176 := by decide +kernel

theorem l238495 : P.leaf 18 238495 = 560 := by decide +kernel

theorem l238513 : P.leaf 18 238513 = 20 := by decide +kernel

theorem l238515 : P.leaf 18 238515 = 32 := by decide +kernel

theorem l238516 : P.leaf 18 238516 = 52 := by decide +kernel

theorem l238517 : P.leaf 18 238517 = 164 := by decide +kernel

theorem l238519 : P.leaf 18 238519 = 428 := by decide +kernel

theorem l238521 : P.leaf 18 238521 = 72 := by decide +kernel

theorem l238523 : P.leaf 18 238523 = 144 := by decide +kernel

theorem l238524 : P.leaf 18 238524 = 216 := by decide +kernel

theorem l238525 : P.leaf 18 238525 = 240 := by decide +kernel

theorem segOK : checkSeg 20 perms 238395 238527 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 103980 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 238395 238527 1248 103980 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l238395 (.cons l238396 (.cons l238397 (.cons l238399 (.cons l238407 (.cons l238415 (.cons l238421 (.cons l238423 (.cons l238429 (.cons l238431 (.cons l238452 (.cons l238453 (.cons l238455 (.cons l238456 (.cons l238460 (.cons l238461 (.cons l238463 (.cons l238465 (.cons l238467 (.cons l238471 (.cons l238475 (.cons l238479 (.cons l238481 (.cons l238482 (.cons l238483 (.cons l238485 (.cons l238487 (.cons l238489 (.cons l238491 (.cons l238493 (.cons l238495 (.cons l238513 (.cons l238515 (.cons l238516 (.cons l238517 (.cons l238519 (.cons l238521 (.cons l238523 (.cons l238524 (.cons l238525 (.nil))))))))))))))))))))))))))))))))))))))))))

end S67

end RACert.S0N3.C0
