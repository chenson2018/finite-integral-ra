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

namespace S127

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(520476, 48), (520477, 48), (520478, 48), (520479, 48), (520485, 24), (520487, 48), (520488, 48), (520489, 48), (520490, 48), (520491, 48), (520492, 48), (520493, 48), (520494, 48), (520495, 48), (520503, 24), (520504, 48), (520505, 48), (520506, 48), (520507, 48), (520508, 48), (520509, 48), (520510, 48), (520511, 48), (520513, 48), (520514, 48), (520515, 48), (520517, 48), (520518, 48), (520519, 48), (520521, 48), (520522, 48), (520523, 48), (520525, 48), (520526, 48), (520527, 48), (520529, 48), (520530, 48), (520531, 48), (520532, 48), (520533, 48), (520534, 48), (520535, 48), (520536, 24), (520537, 48), (520538, 48), (520539, 48), (520540, 48), (520541, 48), (520542, 48), (520543, 48), (520544, 48), (520545, 48), (520546, 48), (520547, 48), (520548, 48), (520549, 48), (520550, 48), (520551, 48), (520552, 48), (520553, 48), (520554, 48), (520555, 48), (520556, 48), (520557, 48), (520558, 48), (520559, 48), (520560, 48), (520561, 48), (520562, 48), (520563, 48), (520564, 48), (520565, 48), (520566, 48), (520567, 48), (520568, 48), (520569, 48), (520570, 48), (520571, 48), (520572, 48), (520573, 48), (520574, 48), (520575, 48), (520578, 16), (520579, 48), (520581, 48), (520582, 48), (520583, 48), (520585, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 502, 0, 502, 439, 650, 650, 502, 502, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 439, 650, 650, 502, 0, 0, 439, 650, 650, 502, 0, 0, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 502, 439, 650, 650, 502, 502, 0, 0, 502, 439, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 0, 0, 502, 0, 0, 502]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(520476, 99), (520477, 129), (520478, 153), (520479, 202), (520487, 126), (520494, 161), (520495, 174), (520503, 263), (520508, 128), (520509, 154), (520510, 250), (520511, 276), (520518, 108), (520519, 168), (520526, 120), (520527, 168), (520532, 223), (520533, 506), (520534, 549), (520535, 1086), (520540, 486), (520541, 670), (520542, 732), (520543, 1387), (520550, 546), (520551, 685), (520558, 694), (520559, 838), (520564, 324), (520565, 641), (520566, 987), (520567, 1304), (520572, 712), (520573, 791), (520574, 1215), (520575, 1716), (520578, 8), (520579, 40), (520582, 97), (520583, 130)]

theorem l520476 : P.leaf 18 520476 = 99 := by decide +kernel

theorem l520477 : P.leaf 18 520477 = 129 := by decide +kernel

theorem l520478 : P.leaf 18 520478 = 153 := by decide +kernel

theorem l520479 : P.leaf 18 520479 = 202 := by decide +kernel

theorem l520487 : P.leaf 18 520487 = 126 := by decide +kernel

theorem l520494 : P.leaf 18 520494 = 161 := by decide +kernel

theorem l520495 : P.leaf 18 520495 = 174 := by decide +kernel

theorem l520503 : P.leaf 18 520503 = 263 := by decide +kernel

theorem l520508 : P.leaf 18 520508 = 128 := by decide +kernel

theorem l520509 : P.leaf 18 520509 = 154 := by decide +kernel

theorem l520510 : P.leaf 18 520510 = 250 := by decide +kernel

theorem l520511 : P.leaf 18 520511 = 276 := by decide +kernel

theorem l520518 : P.leaf 18 520518 = 108 := by decide +kernel

theorem l520519 : P.leaf 18 520519 = 168 := by decide +kernel

theorem l520526 : P.leaf 18 520526 = 120 := by decide +kernel

theorem l520527 : P.leaf 18 520527 = 168 := by decide +kernel

theorem l520532 : P.leaf 18 520532 = 223 := by decide +kernel

theorem l520533 : P.leaf 18 520533 = 506 := by decide +kernel

theorem l520534 : P.leaf 18 520534 = 549 := by decide +kernel

theorem l520535 : P.leaf 18 520535 = 1086 := by decide +kernel

theorem l520540 : P.leaf 18 520540 = 486 := by decide +kernel

theorem l520541 : P.leaf 18 520541 = 670 := by decide +kernel

theorem l520542 : P.leaf 18 520542 = 732 := by decide +kernel

theorem l520543 : P.leaf 18 520543 = 1387 := by decide +kernel

theorem l520550 : P.leaf 18 520550 = 546 := by decide +kernel

theorem l520551 : P.leaf 18 520551 = 685 := by decide +kernel

theorem l520558 : P.leaf 18 520558 = 694 := by decide +kernel

theorem l520559 : P.leaf 18 520559 = 838 := by decide +kernel

theorem l520564 : P.leaf 18 520564 = 324 := by decide +kernel

theorem l520565 : P.leaf 18 520565 = 641 := by decide +kernel

theorem l520566 : P.leaf 18 520566 = 987 := by decide +kernel

theorem l520567 : P.leaf 18 520567 = 1304 := by decide +kernel

theorem l520572 : P.leaf 18 520572 = 712 := by decide +kernel

theorem l520573 : P.leaf 18 520573 = 791 := by decide +kernel

theorem l520574 : P.leaf 18 520574 = 1215 := by decide +kernel

theorem l520575 : P.leaf 18 520575 = 1716 := by decide +kernel

theorem l520578 : P.leaf 18 520578 = 8 := by decide +kernel

theorem l520579 : P.leaf 18 520579 = 40 := by decide +kernel

theorem l520582 : P.leaf 18 520582 = 97 := by decide +kernel

theorem l520583 : P.leaf 18 520583 = 130 := by decide +kernel

theorem segOK : checkSeg 20 perms 520476 520586 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 907640 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 520476 520586 4120 907640 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l520476 (.cons l520477 (.cons l520478 (.cons l520479 (.cons l520487 (.cons l520494 (.cons l520495 (.cons l520503 (.cons l520508 (.cons l520509 (.cons l520510 (.cons l520511 (.cons l520518 (.cons l520519 (.cons l520526 (.cons l520527 (.cons l520532 (.cons l520533 (.cons l520534 (.cons l520535 (.cons l520540 (.cons l520541 (.cons l520542 (.cons l520543 (.cons l520550 (.cons l520551 (.cons l520558 (.cons l520559 (.cons l520564 (.cons l520565 (.cons l520566 (.cons l520567 (.cons l520572 (.cons l520573 (.cons l520574 (.cons l520575 (.cons l520578 (.cons l520579 (.cons l520582 (.cons l520583 (.nil))))))))))))))))))))))))))))))))))))))))))

end S127

end RACert.S0N3.C0
