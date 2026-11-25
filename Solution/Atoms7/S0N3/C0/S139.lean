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

namespace S139

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1046263, 24), (1046271, 6), (1046367, 24), (1046383, 24), (1046399, 12), (1046487, 8), (1046491, 8), (1046495, 24), (1046525, 12), (1046527, 12), (1048575, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1046263, 14757), (1046271, 30862), (1046367, 24211), (1046383, 25834), (1046399, 51860), (1046487, 17261), (1046491, 17261), (1046495, 34111), (1046525, 32277), (1046527, 62327), (1048575, 105498)]

theorem l1046263 : P.leaf 18 1046263 = 14757 := by decide +kernel

theorem l1046271 : P.leaf 18 1046271 = 30862 := by decide +kernel

theorem l1046367 : P.leaf 18 1046367 = 24211 := by decide +kernel

theorem l1046383 : P.leaf 18 1046383 = 25834 := by decide +kernel

theorem l1046399 : P.leaf 18 1046399 = 51860 := by decide +kernel

theorem l1046487 : P.leaf 18 1046487 = 17261 := by decide +kernel

theorem l1046491 : P.leaf 18 1046491 = 17261 := by decide +kernel

theorem l1046495 : P.leaf 18 1046495 = 34111 := by decide +kernel

theorem l1046525 : P.leaf 18 1046525 = 32277 := by decide +kernel

theorem l1046527 : P.leaf 18 1046527 = 62327 := by decide +kernel

theorem l1048575 : P.leaf 18 1048575 = 105498 := by decide +kernel

theorem segOK : checkSeg 20 perms 1046263 1048576 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4698326 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1046263 1048576 155 4698326 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1046263 (.cons l1046271 (.cons l1046367 (.cons l1046383 (.cons l1046399 (.cons l1046487 (.cons l1046491 (.cons l1046495 (.cons l1046525 (.cons l1046527 (.cons l1048575 (.nil)))))))))))))

end S139

end RACert.S0N3.C0
