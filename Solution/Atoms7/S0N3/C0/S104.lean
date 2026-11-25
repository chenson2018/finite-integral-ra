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

namespace S104

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439257, 48), (439258, 48), (439259, 48), (439261, 48), (439262, 48), (439263, 48), (439269, 48), (439270, 48), (439271, 48), (439273, 48), (439274, 48), (439275, 48), (439277, 48), (439278, 48), (439279, 48), (439285, 48), (439286, 48), (439287, 48), (439289, 48), (439290, 48), (439291, 48), (439292, 24), (439293, 48), (439294, 48), (439295, 48), (439637, 48), (439638, 24), (439639, 48), (439641, 48), (439642, 48), (439643, 48), (439645, 48), (439646, 48), (439647, 48), (439653, 24), (439655, 48), (439657, 48), (439658, 24), (439659, 48), (439661, 48), (439662, 48), (439663, 48), (439671, 24), (439673, 48), (439674, 48), (439675, 48), (439677, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 0, 0, 0, 0, 502, 0, 439, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439257, 618), (439258, 211), (439259, 1273), (439261, 1215), (439262, 851), (439263, 2619), (439270, 695), (439271, 1571), (439274, 636), (439275, 1482), (439278, 1255), (439279, 2851), (439285, 1274), (439286, 992), (439287, 2270), (439289, 1146), (439290, 904), (439291, 2192), (439292, 780), (439293, 2112), (439294, 1736), (439295, 4734), (439637, 181), (439638, 32), (439639, 520), (439641, 16), (439643, 51), (439645, 415), (439646, 110), (439647, 792), (439655, 606), (439658, 24), (439659, 195), (439662, 412), (439663, 936), (439671, 1519), (439673, 138), (439674, 72), (439675, 445), (439677, 1217)]

theorem l439257 : P.leaf 18 439257 = 618 := by decide +kernel

theorem l439258 : P.leaf 18 439258 = 211 := by decide +kernel

theorem l439259 : P.leaf 18 439259 = 1273 := by decide +kernel

theorem l439261 : P.leaf 18 439261 = 1215 := by decide +kernel

theorem l439262 : P.leaf 18 439262 = 851 := by decide +kernel

theorem l439263 : P.leaf 18 439263 = 2619 := by decide +kernel

theorem l439270 : P.leaf 18 439270 = 695 := by decide +kernel

theorem l439271 : P.leaf 18 439271 = 1571 := by decide +kernel

theorem l439274 : P.leaf 18 439274 = 636 := by decide +kernel

theorem l439275 : P.leaf 18 439275 = 1482 := by decide +kernel

theorem l439278 : P.leaf 18 439278 = 1255 := by decide +kernel

theorem l439279 : P.leaf 18 439279 = 2851 := by decide +kernel

theorem l439285 : P.leaf 18 439285 = 1274 := by decide +kernel

theorem l439286 : P.leaf 18 439286 = 992 := by decide +kernel

theorem l439287 : P.leaf 18 439287 = 2270 := by decide +kernel

theorem l439289 : P.leaf 18 439289 = 1146 := by decide +kernel

theorem l439290 : P.leaf 18 439290 = 904 := by decide +kernel

theorem l439291 : P.leaf 18 439291 = 2192 := by decide +kernel

theorem l439292 : P.leaf 18 439292 = 780 := by decide +kernel

theorem l439293 : P.leaf 18 439293 = 2112 := by decide +kernel

theorem l439294 : P.leaf 18 439294 = 1736 := by decide +kernel

theorem l439295 : P.leaf 18 439295 = 4734 := by decide +kernel

theorem l439637 : P.leaf 18 439637 = 181 := by decide +kernel

theorem l439638 : P.leaf 18 439638 = 32 := by decide +kernel

theorem l439639 : P.leaf 18 439639 = 520 := by decide +kernel

theorem l439641 : P.leaf 18 439641 = 16 := by decide +kernel

theorem l439643 : P.leaf 18 439643 = 51 := by decide +kernel

theorem l439645 : P.leaf 18 439645 = 415 := by decide +kernel

theorem l439646 : P.leaf 18 439646 = 110 := by decide +kernel

theorem l439647 : P.leaf 18 439647 = 792 := by decide +kernel

theorem l439655 : P.leaf 18 439655 = 606 := by decide +kernel

theorem l439658 : P.leaf 18 439658 = 24 := by decide +kernel

theorem l439659 : P.leaf 18 439659 = 195 := by decide +kernel

theorem l439662 : P.leaf 18 439662 = 412 := by decide +kernel

theorem l439663 : P.leaf 18 439663 = 936 := by decide +kernel

theorem l439671 : P.leaf 18 439671 = 1519 := by decide +kernel

theorem l439673 : P.leaf 18 439673 = 138 := by decide +kernel

theorem l439674 : P.leaf 18 439674 = 72 := by decide +kernel

theorem l439675 : P.leaf 18 439675 = 445 := by decide +kernel

theorem l439677 : P.leaf 18 439677 = 1217 := by decide +kernel

theorem segOK : checkSeg 20 perms 439257 439678 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1916184 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439257 439678 2136 1916184 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l439257 (.cons l439258 (.cons l439259 (.cons l439261 (.cons l439262 (.cons l439263 (.cons l439270 (.cons l439271 (.cons l439274 (.cons l439275 (.cons l439278 (.cons l439279 (.cons l439285 (.cons l439286 (.cons l439287 (.cons l439289 (.cons l439290 (.cons l439291 (.cons l439292 (.cons l439293 (.cons l439294 (.cons l439295 (.cons l439637 (.cons l439638 (.cons l439639 (.cons l439641 (.cons l439643 (.cons l439645 (.cons l439646 (.cons l439647 (.cons l439655 (.cons l439658 (.cons l439659 (.cons l439662 (.cons l439663 (.cons l439671 (.cons l439673 (.cons l439674 (.cons l439675 (.cons l439677 (.nil))))))))))))))))))))))))))))))))))))))))))

end S104

end RACert.S0N3.C0
