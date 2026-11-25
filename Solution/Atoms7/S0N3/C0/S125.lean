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

namespace S125

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(517563, 24), (517565, 24), (517566, 24), (517567, 24), (517590, 24), (517591, 24), (517594, 24), (517595, 24), (517597, 12), (517598, 24), (517599, 24), (517605, 24), (517607, 24), (517609, 24), (517611, 24), (517613, 24), (517615, 24), (517621, 24), (517622, 24), (517623, 24), (517625, 24), (517626, 24), (517627, 24), (517629, 24), (517630, 24), (517631, 24), (517722, 12), (517723, 24), (517726, 24), (517727, 24), (517737, 4), (517739, 24), (517743, 12), (517755, 12), (517757, 24), (517758, 24), (517759, 24), (517782, 12), (517783, 24), (517791, 12), (517813, 24), (517814, 24), (517815, 24), (517821, 24), (517822, 24), (517823, 24), (517877, 24), (517878, 12), (517879, 24), (517881, 12), (517883, 24), (517887, 12), (517982, 12), (517983, 24), (517999, 24), (518015, 12), (518038, 24), (518039, 24), (518046, 24), (518047, 24), (518055, 24), (518063, 24), (518069, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 440, 1224, 1224, 0, 440, 0, 440, 1224, 1224, 1224, 0, 0, 0, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(517563, 2780), (517565, 1851), (517566, 4506), (517567, 6296), (517590, 2074), (517591, 3556), (517594, 973), (517595, 1886), (517597, 2027), (517598, 2733), (517599, 5042), (517605, 192), (517607, 1996), (517611, 1358), (517615, 2814), (517621, 1748), (517622, 4416), (517623, 5445), (517625, 885), (517626, 2277), (517627, 2812), (517629, 2237), (517630, 5796), (517631, 7914), (517737, 752), (517743, 516), (517782, 68), (517783, 466), (517791, 906), (517982, 904), (517983, 1823), (517999, 1076), (518015, 2612), (518038, 1434), (518039, 2824), (518046, 2212), (518047, 4285), (518055, 1326), (518063, 2367), (518069, 1592)]

theorem l517563 : P.leaf 18 517563 = 2780 := by decide +kernel

theorem l517565 : P.leaf 18 517565 = 1851 := by decide +kernel

theorem l517566 : P.leaf 18 517566 = 4506 := by decide +kernel

theorem l517567 : P.leaf 18 517567 = 6296 := by decide +kernel

theorem l517590 : P.leaf 18 517590 = 2074 := by decide +kernel

theorem l517591 : P.leaf 18 517591 = 3556 := by decide +kernel

theorem l517594 : P.leaf 18 517594 = 973 := by decide +kernel

theorem l517595 : P.leaf 18 517595 = 1886 := by decide +kernel

theorem l517597 : P.leaf 18 517597 = 2027 := by decide +kernel

theorem l517598 : P.leaf 18 517598 = 2733 := by decide +kernel

theorem l517599 : P.leaf 18 517599 = 5042 := by decide +kernel

theorem l517605 : P.leaf 18 517605 = 192 := by decide +kernel

theorem l517607 : P.leaf 18 517607 = 1996 := by decide +kernel

theorem l517611 : P.leaf 18 517611 = 1358 := by decide +kernel

theorem l517615 : P.leaf 18 517615 = 2814 := by decide +kernel

theorem l517621 : P.leaf 18 517621 = 1748 := by decide +kernel

theorem l517622 : P.leaf 18 517622 = 4416 := by decide +kernel

theorem l517623 : P.leaf 18 517623 = 5445 := by decide +kernel

theorem l517625 : P.leaf 18 517625 = 885 := by decide +kernel

theorem l517626 : P.leaf 18 517626 = 2277 := by decide +kernel

theorem l517627 : P.leaf 18 517627 = 2812 := by decide +kernel

theorem l517629 : P.leaf 18 517629 = 2237 := by decide +kernel

theorem l517630 : P.leaf 18 517630 = 5796 := by decide +kernel

theorem l517631 : P.leaf 18 517631 = 7914 := by decide +kernel

theorem l517737 : P.leaf 18 517737 = 752 := by decide +kernel

theorem l517743 : P.leaf 18 517743 = 516 := by decide +kernel

theorem l517782 : P.leaf 18 517782 = 68 := by decide +kernel

theorem l517783 : P.leaf 18 517783 = 466 := by decide +kernel

theorem l517791 : P.leaf 18 517791 = 906 := by decide +kernel

theorem l517982 : P.leaf 18 517982 = 904 := by decide +kernel

theorem l517983 : P.leaf 18 517983 = 1823 := by decide +kernel

theorem l517999 : P.leaf 18 517999 = 1076 := by decide +kernel

theorem l518015 : P.leaf 18 518015 = 2612 := by decide +kernel

theorem l518038 : P.leaf 18 518038 = 1434 := by decide +kernel

theorem l518039 : P.leaf 18 518039 = 2824 := by decide +kernel

theorem l518046 : P.leaf 18 518046 = 2212 := by decide +kernel

theorem l518047 : P.leaf 18 518047 = 4285 := by decide +kernel

theorem l518055 : P.leaf 18 518055 = 1326 := by decide +kernel

theorem l518063 : P.leaf 18 518063 = 2367 := by decide +kernel

theorem l518069 : P.leaf 18 518069 = 1592 := by decide +kernel

theorem segOK : checkSeg 20 perms 517563 518070 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2252108 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 517563 518070 1348 2252108 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l517563 (.cons l517565 (.cons l517566 (.cons l517567 (.cons l517590 (.cons l517591 (.cons l517594 (.cons l517595 (.cons l517597 (.cons l517598 (.cons l517599 (.cons l517605 (.cons l517607 (.cons l517611 (.cons l517615 (.cons l517621 (.cons l517622 (.cons l517623 (.cons l517625 (.cons l517626 (.cons l517627 (.cons l517629 (.cons l517630 (.cons l517631 (.cons l517737 (.cons l517743 (.cons l517782 (.cons l517783 (.cons l517791 (.cons l517982 (.cons l517983 (.cons l517999 (.cons l518015 (.cons l518038 (.cons l518039 (.cons l518046 (.cons l518047 (.cons l518055 (.cons l518063 (.cons l518069 (.nil))))))))))))))))))))))))))))))))))))))))))

end S125

end RACert.S0N3.C0
