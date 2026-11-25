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

namespace S30

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(103315, 48), (103316, 48), (103317, 48), (103318, 48), (103319, 48), (103320, 48), (103321, 48), (103322, 48), (103323, 48), (103324, 48), (103325, 48), (103326, 48), (103327, 48), (103328, 48), (103329, 48), (103330, 48), (103331, 48), (103332, 48), (103333, 48), (103334, 48), (103335, 48), (103336, 48), (103337, 48), (103338, 48), (103339, 48), (103340, 48), (103341, 48), (103342, 48), (103343, 48), (103344, 48), (103345, 48), (103346, 48), (103347, 48), (103348, 48), (103349, 48), (103350, 48), (103351, 48), (103352, 48), (103353, 48), (103354, 48), (103355, 48), (103356, 48), (103357, 48), (103358, 48), (103359, 48), (103360, 48), (103361, 48), (103362, 48), (103363, 48), (103364, 48), (103365, 48), (103366, 48), (103367, 48), (103368, 48), (103369, 48), (103370, 48), (103371, 48), (103372, 48), (103373, 48), (103374, 48), (103375, 48), (103376, 48), (103377, 48), (103378, 48), (103379, 48), (103380, 48), (103381, 48), (103382, 48), (103383, 48), (103384, 48), (103385, 48), (103386, 48), (103387, 48), (103388, 48), (103389, 48), (103390, 48), (103391, 48), (103392, 48), (103393, 48), (103394, 48), (103395, 48), (103396, 48), (103397, 48), (103398, 48), (103399, 48), (103400, 48), (103401, 48), (103402, 48), (103403, 48), (103404, 48), (103405, 48), (103406, 48), (103407, 48), (103408, 48), (103409, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 420, 628, 424, 0, 424, 439, 424, 0, 424, 628, 424, 0, 426, 420, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 420, 439, 0, 0, 420, 628, 0, 0, 426, 439, 0, 0, 628, 628, 0, 0, 420, 432, 0, 0, 418, 418, 424, 0, 418, 418, 424, 0, 418, 418, 424, 0, 420, 439, 0, 0, 420, 0, 424, 0, 424, 439, 424, 0, 424, 0, 424, 0, 420, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 420, 439]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(103315, 0), (103319, 12), (103323, 24), (103327, 64), (103330, 4), (103331, 0), (103334, 6), (103335, 12), (103338, 20), (103339, 24), (103342, 48), (103343, 64), (103346, 12), (103347, 0), (103350, 24), (103351, 58), (103354, 28), (103355, 68), (103358, 72), (103359, 176), (103362, 0), (103363, 2), (103367, 7), (103371, 7), (103375, 28), (103378, 6), (103379, 16), (103381, 30), (103383, 76), (103387, 44), (103389, 60), (103391, 112), (103394, 12), (103395, 8), (103398, 24), (103399, 28), (103402, 24), (103403, 28), (103406, 96), (103407, 112)]

theorem l103315 : P.leaf 18 103315 = 0 := by decide +kernel

theorem l103319 : P.leaf 18 103319 = 12 := by decide +kernel

theorem l103323 : P.leaf 18 103323 = 24 := by decide +kernel

theorem l103327 : P.leaf 18 103327 = 64 := by decide +kernel

theorem l103330 : P.leaf 18 103330 = 4 := by decide +kernel

theorem l103331 : P.leaf 18 103331 = 0 := by decide +kernel

theorem l103334 : P.leaf 18 103334 = 6 := by decide +kernel

theorem l103335 : P.leaf 18 103335 = 12 := by decide +kernel

theorem l103338 : P.leaf 18 103338 = 20 := by decide +kernel

theorem l103339 : P.leaf 18 103339 = 24 := by decide +kernel

theorem l103342 : P.leaf 18 103342 = 48 := by decide +kernel

theorem l103343 : P.leaf 18 103343 = 64 := by decide +kernel

theorem l103346 : P.leaf 18 103346 = 12 := by decide +kernel

theorem l103347 : P.leaf 18 103347 = 0 := by decide +kernel

theorem l103350 : P.leaf 18 103350 = 24 := by decide +kernel

theorem l103351 : P.leaf 18 103351 = 58 := by decide +kernel

theorem l103354 : P.leaf 18 103354 = 28 := by decide +kernel

theorem l103355 : P.leaf 18 103355 = 68 := by decide +kernel

theorem l103358 : P.leaf 18 103358 = 72 := by decide +kernel

theorem l103359 : P.leaf 18 103359 = 176 := by decide +kernel

theorem l103362 : P.leaf 18 103362 = 0 := by decide +kernel

theorem l103363 : P.leaf 18 103363 = 2 := by decide +kernel

theorem l103367 : P.leaf 18 103367 = 7 := by decide +kernel

theorem l103371 : P.leaf 18 103371 = 7 := by decide +kernel

theorem l103375 : P.leaf 18 103375 = 28 := by decide +kernel

theorem l103378 : P.leaf 18 103378 = 6 := by decide +kernel

theorem l103379 : P.leaf 18 103379 = 16 := by decide +kernel

theorem l103381 : P.leaf 18 103381 = 30 := by decide +kernel

theorem l103383 : P.leaf 18 103383 = 76 := by decide +kernel

theorem l103387 : P.leaf 18 103387 = 44 := by decide +kernel

theorem l103389 : P.leaf 18 103389 = 60 := by decide +kernel

theorem l103391 : P.leaf 18 103391 = 112 := by decide +kernel

theorem l103394 : P.leaf 18 103394 = 12 := by decide +kernel

theorem l103395 : P.leaf 18 103395 = 8 := by decide +kernel

theorem l103398 : P.leaf 18 103398 = 24 := by decide +kernel

theorem l103399 : P.leaf 18 103399 = 28 := by decide +kernel

theorem l103402 : P.leaf 18 103402 = 24 := by decide +kernel

theorem l103403 : P.leaf 18 103403 = 28 := by decide +kernel

theorem l103406 : P.leaf 18 103406 = 96 := by decide +kernel

theorem l103407 : P.leaf 18 103407 = 112 := by decide +kernel

theorem segOK : checkSeg 20 perms 103315 103410 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 68928 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 103315 103410 4560 68928 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l103315 (.cons l103319 (.cons l103323 (.cons l103327 (.cons l103330 (.cons l103331 (.cons l103334 (.cons l103335 (.cons l103338 (.cons l103339 (.cons l103342 (.cons l103343 (.cons l103346 (.cons l103347 (.cons l103350 (.cons l103351 (.cons l103354 (.cons l103355 (.cons l103358 (.cons l103359 (.cons l103362 (.cons l103363 (.cons l103367 (.cons l103371 (.cons l103375 (.cons l103378 (.cons l103379 (.cons l103381 (.cons l103383 (.cons l103387 (.cons l103389 (.cons l103391 (.cons l103394 (.cons l103395 (.cons l103398 (.cons l103399 (.cons l103402 (.cons l103403 (.cons l103406 (.cons l103407 (.nil))))))))))))))))))))))))))))))))))))))))))

end S30

end RACert.S0N3.C0
