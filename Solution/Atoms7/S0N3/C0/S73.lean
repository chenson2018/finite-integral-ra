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

namespace S73

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(239495, 24), (239499, 24), (239503, 24), (239507, 24), (239511, 24), (239515, 24), (239519, 24), (239523, 24), (239527, 24), (239531, 24), (239535, 24), (239539, 24), (239541, 12), (239542, 12), (239543, 24), (239547, 24), (239549, 24), (239550, 24), (239551, 24), (239555, 24), (239559, 24), (239563, 24), (239567, 24), (239571, 24), (239575, 24), (239579, 24), (239583, 24), (239587, 24), (239591, 24), (239595, 24), (239599, 24), (239603, 24), (239607, 24), (239611, 24), (239613, 12), (239614, 12), (239615, 24), (240643, 6), (240647, 12), (240651, 12), (240655, 12), (240659, 24), (240663, 24), (240667, 24), (240671, 24), (240691, 12), (240695, 12), (240699, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 517, 440, 517, 440, 0, 440, 0, 440, 0, 440]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(239495, 668), (239499, 154), (239503, 992), (239507, 60), (239511, 831), (239515, 168), (239519, 1236), (239523, 60), (239527, 878), (239531, 168), (239535, 1292), (239539, 132), (239541, 736), (239542, 628), (239543, 2024), (239547, 336), (239549, 812), (239550, 812), (239551, 2296), (239555, 74), (239559, 990), (239563, 172), (239567, 1282), (239571, 80), (239575, 1284), (239579, 204), (239583, 1614), (239587, 80), (239591, 1298), (239595, 204), (239599, 1628), (239603, 176), (239607, 2296), (239611, 400), (239613, 892), (239614, 956), (239615, 2896), (240663, 30), (240671, 40), (240695, 248)]

theorem l239495 : P.leaf 18 239495 = 668 := by decide +kernel

theorem l239499 : P.leaf 18 239499 = 154 := by decide +kernel

theorem l239503 : P.leaf 18 239503 = 992 := by decide +kernel

theorem l239507 : P.leaf 18 239507 = 60 := by decide +kernel

theorem l239511 : P.leaf 18 239511 = 831 := by decide +kernel

theorem l239515 : P.leaf 18 239515 = 168 := by decide +kernel

theorem l239519 : P.leaf 18 239519 = 1236 := by decide +kernel

theorem l239523 : P.leaf 18 239523 = 60 := by decide +kernel

theorem l239527 : P.leaf 18 239527 = 878 := by decide +kernel

theorem l239531 : P.leaf 18 239531 = 168 := by decide +kernel

theorem l239535 : P.leaf 18 239535 = 1292 := by decide +kernel

theorem l239539 : P.leaf 18 239539 = 132 := by decide +kernel

theorem l239541 : P.leaf 18 239541 = 736 := by decide +kernel

theorem l239542 : P.leaf 18 239542 = 628 := by decide +kernel

theorem l239543 : P.leaf 18 239543 = 2024 := by decide +kernel

theorem l239547 : P.leaf 18 239547 = 336 := by decide +kernel

theorem l239549 : P.leaf 18 239549 = 812 := by decide +kernel

theorem l239550 : P.leaf 18 239550 = 812 := by decide +kernel

theorem l239551 : P.leaf 18 239551 = 2296 := by decide +kernel

theorem l239555 : P.leaf 18 239555 = 74 := by decide +kernel

theorem l239559 : P.leaf 18 239559 = 990 := by decide +kernel

theorem l239563 : P.leaf 18 239563 = 172 := by decide +kernel

theorem l239567 : P.leaf 18 239567 = 1282 := by decide +kernel

theorem l239571 : P.leaf 18 239571 = 80 := by decide +kernel

theorem l239575 : P.leaf 18 239575 = 1284 := by decide +kernel

theorem l239579 : P.leaf 18 239579 = 204 := by decide +kernel

theorem l239583 : P.leaf 18 239583 = 1614 := by decide +kernel

theorem l239587 : P.leaf 18 239587 = 80 := by decide +kernel

theorem l239591 : P.leaf 18 239591 = 1298 := by decide +kernel

theorem l239595 : P.leaf 18 239595 = 204 := by decide +kernel

theorem l239599 : P.leaf 18 239599 = 1628 := by decide +kernel

theorem l239603 : P.leaf 18 239603 = 176 := by decide +kernel

theorem l239607 : P.leaf 18 239607 = 2296 := by decide +kernel

theorem l239611 : P.leaf 18 239611 = 400 := by decide +kernel

theorem l239613 : P.leaf 18 239613 = 892 := by decide +kernel

theorem l239614 : P.leaf 18 239614 = 956 := by decide +kernel

theorem l239615 : P.leaf 18 239615 = 2896 := by decide +kernel

theorem l240663 : P.leaf 18 240663 = 30 := by decide +kernel

theorem l240671 : P.leaf 18 240671 = 40 := by decide +kernel

theorem l240695 : P.leaf 18 240695 = 248 := by decide +kernel

theorem segOK : checkSeg 20 perms 239495 240703 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 705528 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 239495 240703 1014 705528 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l239495 (.cons l239499 (.cons l239503 (.cons l239507 (.cons l239511 (.cons l239515 (.cons l239519 (.cons l239523 (.cons l239527 (.cons l239531 (.cons l239535 (.cons l239539 (.cons l239541 (.cons l239542 (.cons l239543 (.cons l239547 (.cons l239549 (.cons l239550 (.cons l239551 (.cons l239555 (.cons l239559 (.cons l239563 (.cons l239567 (.cons l239571 (.cons l239575 (.cons l239579 (.cons l239583 (.cons l239587 (.cons l239591 (.cons l239595 (.cons l239599 (.cons l239603 (.cons l239607 (.cons l239611 (.cons l239613 (.cons l239614 (.cons l239615 (.cons l240663 (.cons l240671 (.cons l240695 (.nil))))))))))))))))))))))))))))))))))))))))))

end S73

end RACert.S0N3.C0
