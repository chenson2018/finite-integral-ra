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

namespace S118

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516459, 24), (516460, 24), (516461, 24), (516462, 24), (516463, 24), (516464, 24), (516465, 24), (516466, 24), (516467, 24), (516468, 24), (516469, 24), (516470, 24), (516471, 24), (516472, 24), (516473, 24), (516474, 24), (516475, 24), (516476, 24), (516477, 24), (516478, 24), (516479, 24), (516482, 8), (516483, 24), (516485, 24), (516486, 24), (516487, 24), (516489, 24), (516490, 24), (516491, 24), (516493, 24), (516494, 24), (516495, 24), (516499, 24), (516500, 12), (516501, 24), (516502, 24), (516503, 24), (516505, 24), (516506, 24), (516507, 24), (516508, 24), (516509, 24), (516510, 24), (516511, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516459, 117), (516462, 494), (516463, 626), (516464, 0), (516465, 60), (516466, 171), (516467, 275), (516468, 44), (516469, 185), (516470, 598), (516471, 728), (516472, 0), (516473, 0), (516474, 222), (516475, 418), (516476, 171), (516477, 216), (516478, 1057), (516479, 1301), (516482, 2), (516483, 10), (516485, 22), (516486, 24), (516487, 26), (516490, 9), (516491, 20), (516494, 36), (516495, 36), (516499, 106), (516500, 39), (516501, 117), (516502, 285), (516503, 390), (516505, 85), (516506, 222), (516507, 300), (516508, 216), (516509, 234), (516510, 595), (516511, 705)]

theorem l516459 : P.leaf 18 516459 = 117 := by decide +kernel

theorem l516462 : P.leaf 18 516462 = 494 := by decide +kernel

theorem l516463 : P.leaf 18 516463 = 626 := by decide +kernel

theorem l516464 : P.leaf 18 516464 = 0 := by decide +kernel

theorem l516465 : P.leaf 18 516465 = 60 := by decide +kernel

theorem l516466 : P.leaf 18 516466 = 171 := by decide +kernel

theorem l516467 : P.leaf 18 516467 = 275 := by decide +kernel

theorem l516468 : P.leaf 18 516468 = 44 := by decide +kernel

theorem l516469 : P.leaf 18 516469 = 185 := by decide +kernel

theorem l516470 : P.leaf 18 516470 = 598 := by decide +kernel

theorem l516471 : P.leaf 18 516471 = 728 := by decide +kernel

theorem l516472 : P.leaf 18 516472 = 0 := by decide +kernel

theorem l516473 : P.leaf 18 516473 = 0 := by decide +kernel

theorem l516474 : P.leaf 18 516474 = 222 := by decide +kernel

theorem l516475 : P.leaf 18 516475 = 418 := by decide +kernel

theorem l516476 : P.leaf 18 516476 = 171 := by decide +kernel

theorem l516477 : P.leaf 18 516477 = 216 := by decide +kernel

theorem l516478 : P.leaf 18 516478 = 1057 := by decide +kernel

theorem l516479 : P.leaf 18 516479 = 1301 := by decide +kernel

theorem l516482 : P.leaf 18 516482 = 2 := by decide +kernel

theorem l516483 : P.leaf 18 516483 = 10 := by decide +kernel

theorem l516485 : P.leaf 18 516485 = 22 := by decide +kernel

theorem l516486 : P.leaf 18 516486 = 24 := by decide +kernel

theorem l516487 : P.leaf 18 516487 = 26 := by decide +kernel

theorem l516490 : P.leaf 18 516490 = 9 := by decide +kernel

theorem l516491 : P.leaf 18 516491 = 20 := by decide +kernel

theorem l516494 : P.leaf 18 516494 = 36 := by decide +kernel

theorem l516495 : P.leaf 18 516495 = 36 := by decide +kernel

theorem l516499 : P.leaf 18 516499 = 106 := by decide +kernel

theorem l516500 : P.leaf 18 516500 = 39 := by decide +kernel

theorem l516501 : P.leaf 18 516501 = 117 := by decide +kernel

theorem l516502 : P.leaf 18 516502 = 285 := by decide +kernel

theorem l516503 : P.leaf 18 516503 = 390 := by decide +kernel

theorem l516505 : P.leaf 18 516505 = 85 := by decide +kernel

theorem l516506 : P.leaf 18 516506 = 222 := by decide +kernel

theorem l516507 : P.leaf 18 516507 = 300 := by decide +kernel

theorem l516508 : P.leaf 18 516508 = 216 := by decide +kernel

theorem l516509 : P.leaf 18 516509 = 234 := by decide +kernel

theorem l516510 : P.leaf 18 516510 = 595 := by decide +kernel

theorem l516511 : P.leaf 18 516511 = 705 := by decide +kernel

theorem segOK : checkSeg 20 perms 516459 516515 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 243388 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516459 516515 1028 243388 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l516459 (.cons l516462 (.cons l516463 (.cons l516464 (.cons l516465 (.cons l516466 (.cons l516467 (.cons l516468 (.cons l516469 (.cons l516470 (.cons l516471 (.cons l516472 (.cons l516473 (.cons l516474 (.cons l516475 (.cons l516476 (.cons l516477 (.cons l516478 (.cons l516479 (.cons l516482 (.cons l516483 (.cons l516485 (.cons l516486 (.cons l516487 (.cons l516490 (.cons l516491 (.cons l516494 (.cons l516495 (.cons l516499 (.cons l516500 (.cons l516501 (.cons l516502 (.cons l516503 (.cons l516505 (.cons l516506 (.cons l516507 (.cons l516508 (.cons l516509 (.cons l516510 (.cons l516511 (.nil))))))))))))))))))))))))))))))))))))))))))

end S118

end RACert.S0N3.C0
