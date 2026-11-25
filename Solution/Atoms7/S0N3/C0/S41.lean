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

namespace S41

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(113362, 48), (113363, 48), (113364, 48), (113365, 48), (113366, 48), (113367, 48), (113368, 48), (113369, 48), (113370, 48), (113371, 48), (113372, 48), (113373, 48), (113374, 48), (113375, 48), (113376, 48), (113377, 48), (113378, 48), (113379, 48), (113380, 48), (113381, 48), (113382, 48), (113383, 48), (113384, 48), (113385, 48), (113386, 48), (113387, 48), (113388, 48), (113389, 48), (113390, 48), (113391, 48), (113392, 48), (113393, 48), (113394, 48), (113395, 48), (113396, 48), (113397, 48), (113398, 48), (113399, 48), (113400, 48), (113401, 48), (113402, 48), (113403, 48), (113404, 48), (113405, 48), (113406, 48), (113407, 48), (113484, 24), (113485, 48), (113486, 48), (113487, 48), (113501, 48), (113502, 24), (113503, 48), (113517, 24), (113519, 48), (113535, 24), (113600, 48), (113601, 48), (113602, 48), (113603, 48), (113604, 48), (113605, 48), (113606, 48), (113607, 48), (113608, 48), (113609, 48), (113610, 48), (113611, 48), (113612, 48), (113613, 48), (113614, 48), (113615, 48), (113616, 48), (113617, 48), (113618, 48), (113619, 48), (113620, 48), (113621, 48), (113622, 48), (113623, 48), (113624, 48), (113625, 48), (113626, 48), (113627, 48), (113628, 48), (113629, 48), (113630, 48), (113631, 48), (113632, 48), (113633, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 432, 0, 0, 0, 424, 439, 424, 0, 424, 0, 424, 0, 426, 432, 0, 0, 418, 418, 0, 0, 426, 439, 0, 0, 418, 418, 0, 0, 426, 0, 0, 0, 432, 0, 0, 0, 426, 439, 0, 0, 0, 0, 0, 0, 418, 418, 424, 671, 671, 424, 671, 418, 671, 671, 426, 432, 0, 0, 418, 418, 424, 0, 418, 418, 424, 0, 418, 418, 424, 0, 426, 439, 0, 0, 424, 0, 424, 0, 424, 439, 424, 0, 424, 0, 424, 0, 426, 432]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(113362, 11), (113363, 21), (113365, 52), (113366, 24), (113367, 108), (113371, 66), (113373, 93), (113375, 144), (113378, 32), (113379, 40), (113382, 104), (113383, 200), (113386, 52), (113387, 120), (113390, 186), (113391, 340), (113393, 0), (113394, 66), (113395, 86), (113397, 180), (113398, 196), (113399, 404), (113402, 100), (113403, 244), (113404, 60), (113405, 247), (113406, 273), (113407, 604), (113602, 0), (113603, 4), (113607, 36), (113611, 16), (113615, 60), (113618, 22), (113619, 28), (113621, 90), (113623, 180), (113627, 88), (113629, 129), (113631, 228)]

theorem l113362 : P.leaf 18 113362 = 11 := by decide +kernel

theorem l113363 : P.leaf 18 113363 = 21 := by decide +kernel

theorem l113365 : P.leaf 18 113365 = 52 := by decide +kernel

theorem l113366 : P.leaf 18 113366 = 24 := by decide +kernel

theorem l113367 : P.leaf 18 113367 = 108 := by decide +kernel

theorem l113371 : P.leaf 18 113371 = 66 := by decide +kernel

theorem l113373 : P.leaf 18 113373 = 93 := by decide +kernel

theorem l113375 : P.leaf 18 113375 = 144 := by decide +kernel

theorem l113378 : P.leaf 18 113378 = 32 := by decide +kernel

theorem l113379 : P.leaf 18 113379 = 40 := by decide +kernel

theorem l113382 : P.leaf 18 113382 = 104 := by decide +kernel

theorem l113383 : P.leaf 18 113383 = 200 := by decide +kernel

theorem l113386 : P.leaf 18 113386 = 52 := by decide +kernel

theorem l113387 : P.leaf 18 113387 = 120 := by decide +kernel

theorem l113390 : P.leaf 18 113390 = 186 := by decide +kernel

theorem l113391 : P.leaf 18 113391 = 340 := by decide +kernel

theorem l113393 : P.leaf 18 113393 = 0 := by decide +kernel

theorem l113394 : P.leaf 18 113394 = 66 := by decide +kernel

theorem l113395 : P.leaf 18 113395 = 86 := by decide +kernel

theorem l113397 : P.leaf 18 113397 = 180 := by decide +kernel

theorem l113398 : P.leaf 18 113398 = 196 := by decide +kernel

theorem l113399 : P.leaf 18 113399 = 404 := by decide +kernel

theorem l113402 : P.leaf 18 113402 = 100 := by decide +kernel

theorem l113403 : P.leaf 18 113403 = 244 := by decide +kernel

theorem l113404 : P.leaf 18 113404 = 60 := by decide +kernel

theorem l113405 : P.leaf 18 113405 = 247 := by decide +kernel

theorem l113406 : P.leaf 18 113406 = 273 := by decide +kernel

theorem l113407 : P.leaf 18 113407 = 604 := by decide +kernel

theorem l113602 : P.leaf 18 113602 = 0 := by decide +kernel

theorem l113603 : P.leaf 18 113603 = 4 := by decide +kernel

theorem l113607 : P.leaf 18 113607 = 36 := by decide +kernel

theorem l113611 : P.leaf 18 113611 = 16 := by decide +kernel

theorem l113615 : P.leaf 18 113615 = 60 := by decide +kernel

theorem l113618 : P.leaf 18 113618 = 22 := by decide +kernel

theorem l113619 : P.leaf 18 113619 = 28 := by decide +kernel

theorem l113621 : P.leaf 18 113621 = 90 := by decide +kernel

theorem l113623 : P.leaf 18 113623 = 180 := by decide +kernel

theorem l113627 : P.leaf 18 113627 = 88 := by decide +kernel

theorem l113629 : P.leaf 18 113629 = 129 := by decide +kernel

theorem l113631 : P.leaf 18 113631 = 228 := by decide +kernel

theorem segOK : checkSeg 20 perms 113362 113634 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 236832 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 113362 113634 4224 236832 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l113362 (.cons l113363 (.cons l113365 (.cons l113366 (.cons l113367 (.cons l113371 (.cons l113373 (.cons l113375 (.cons l113378 (.cons l113379 (.cons l113382 (.cons l113383 (.cons l113386 (.cons l113387 (.cons l113390 (.cons l113391 (.cons l113393 (.cons l113394 (.cons l113395 (.cons l113397 (.cons l113398 (.cons l113399 (.cons l113402 (.cons l113403 (.cons l113404 (.cons l113405 (.cons l113406 (.cons l113407 (.cons l113602 (.cons l113603 (.cons l113607 (.cons l113611 (.cons l113615 (.cons l113618 (.cons l113619 (.cons l113621 (.cons l113623 (.cons l113627 (.cons l113629 (.cons l113631 (.nil))))))))))))))))))))))))))))))))))))))))))

end S41

end RACert.S0N3.C0
