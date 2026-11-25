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

namespace S132

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(521215, 48), (521557, 48), (521558, 24), (521559, 48), (521561, 24), (521562, 48), (521563, 48), (521565, 48), (521566, 48), (521567, 48), (521573, 24), (521575, 48), (521577, 48), (521578, 48), (521579, 48), (521581, 48), (521582, 48), (521583, 48), (521591, 24), (521593, 48), (521594, 48), (521595, 48), (521597, 48), (521598, 48), (521599, 48), (521621, 24), (521622, 48), (521623, 48), (521626, 48), (521627, 48), (521629, 48), (521630, 48), (521631, 48), (521637, 48), (521639, 48), (521642, 16), (521643, 48), (521645, 48), (521646, 48), (521647, 48), (521653, 48), (521654, 48), (521655, 48), (521659, 48), (521661, 48), (521662, 48), (521663, 48), (521686, 48), (521687, 48), (521690, 48), (521691, 48), (521693, 24), (521694, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 650, 650, 650, 0, 0, 0, 502, 0, 439, 650, 650, 502, 0, 0, 0, 650, 650, 650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(521215, 12972), (521557, 2027), (521558, 1608), (521559, 3956), (521565, 2681), (521566, 2185), (521567, 5001), (521575, 2955), (521582, 2930), (521583, 3577), (521591, 6455), (521597, 3673), (521598, 5121), (521599, 8782), (521621, 2472), (521622, 1724), (521623, 4239), (521626, 1835), (521627, 3909), (521629, 3898), (521630, 3442), (521631, 8007), (521639, 2710), (521642, 2230), (521643, 2940), (521646, 4364), (521647, 5498), (521653, 3454), (521654, 4618), (521655, 7099), (521659, 6145), (521661, 5357), (521662, 7813), (521663, 13454), (521686, 4016), (521687, 6829), (521690, 2494), (521691, 4797), (521693, 5347), (521694, 5325)]

theorem l521215 : P.leaf 18 521215 = 12972 := by decide +kernel

theorem l521557 : P.leaf 18 521557 = 2027 := by decide +kernel

theorem l521558 : P.leaf 18 521558 = 1608 := by decide +kernel

theorem l521559 : P.leaf 18 521559 = 3956 := by decide +kernel

theorem l521565 : P.leaf 18 521565 = 2681 := by decide +kernel

theorem l521566 : P.leaf 18 521566 = 2185 := by decide +kernel

theorem l521567 : P.leaf 18 521567 = 5001 := by decide +kernel

theorem l521575 : P.leaf 18 521575 = 2955 := by decide +kernel

theorem l521582 : P.leaf 18 521582 = 2930 := by decide +kernel

theorem l521583 : P.leaf 18 521583 = 3577 := by decide +kernel

theorem l521591 : P.leaf 18 521591 = 6455 := by decide +kernel

theorem l521597 : P.leaf 18 521597 = 3673 := by decide +kernel

theorem l521598 : P.leaf 18 521598 = 5121 := by decide +kernel

theorem l521599 : P.leaf 18 521599 = 8782 := by decide +kernel

theorem l521621 : P.leaf 18 521621 = 2472 := by decide +kernel

theorem l521622 : P.leaf 18 521622 = 1724 := by decide +kernel

theorem l521623 : P.leaf 18 521623 = 4239 := by decide +kernel

theorem l521626 : P.leaf 18 521626 = 1835 := by decide +kernel

theorem l521627 : P.leaf 18 521627 = 3909 := by decide +kernel

theorem l521629 : P.leaf 18 521629 = 3898 := by decide +kernel

theorem l521630 : P.leaf 18 521630 = 3442 := by decide +kernel

theorem l521631 : P.leaf 18 521631 = 8007 := by decide +kernel

theorem l521639 : P.leaf 18 521639 = 2710 := by decide +kernel

theorem l521642 : P.leaf 18 521642 = 2230 := by decide +kernel

theorem l521643 : P.leaf 18 521643 = 2940 := by decide +kernel

theorem l521646 : P.leaf 18 521646 = 4364 := by decide +kernel

theorem l521647 : P.leaf 18 521647 = 5498 := by decide +kernel

theorem l521653 : P.leaf 18 521653 = 3454 := by decide +kernel

theorem l521654 : P.leaf 18 521654 = 4618 := by decide +kernel

theorem l521655 : P.leaf 18 521655 = 7099 := by decide +kernel

theorem l521659 : P.leaf 18 521659 = 6145 := by decide +kernel

theorem l521661 : P.leaf 18 521661 = 5357 := by decide +kernel

theorem l521662 : P.leaf 18 521662 = 7813 := by decide +kernel

theorem l521663 : P.leaf 18 521663 = 13454 := by decide +kernel

theorem l521686 : P.leaf 18 521686 = 4016 := by decide +kernel

theorem l521687 : P.leaf 18 521687 = 6829 := by decide +kernel

theorem l521690 : P.leaf 18 521690 = 2494 := by decide +kernel

theorem l521691 : P.leaf 18 521691 = 4797 := by decide +kernel

theorem l521693 : P.leaf 18 521693 = 5347 := by decide +kernel

theorem l521694 : P.leaf 18 521694 = 5325 := by decide +kernel

theorem segOK : checkSeg 20 perms 521215 521695 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 8568544 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 521215 521695 2368 8568544 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l521215 (.cons l521557 (.cons l521558 (.cons l521559 (.cons l521565 (.cons l521566 (.cons l521567 (.cons l521575 (.cons l521582 (.cons l521583 (.cons l521591 (.cons l521597 (.cons l521598 (.cons l521599 (.cons l521621 (.cons l521622 (.cons l521623 (.cons l521626 (.cons l521627 (.cons l521629 (.cons l521630 (.cons l521631 (.cons l521639 (.cons l521642 (.cons l521643 (.cons l521646 (.cons l521647 (.cons l521653 (.cons l521654 (.cons l521655 (.cons l521659 (.cons l521661 (.cons l521662 (.cons l521663 (.cons l521686 (.cons l521687 (.cons l521690 (.cons l521691 (.cons l521693 (.cons l521694 (.nil))))))))))))))))))))))))))))))))))))))))))

end S132

end RACert.S0N3.C0
