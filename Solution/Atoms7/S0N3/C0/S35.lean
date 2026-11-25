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

namespace S35

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(105387, 48), (105388, 48), (105389, 48), (105390, 48), (105391, 48), (105392, 48), (105393, 48), (105394, 48), (105395, 48), (105396, 48), (105397, 48), (105398, 48), (105399, 48), (105400, 48), (105401, 48), (105402, 48), (105403, 48), (105404, 48), (105405, 48), (105406, 48), (105407, 48), (105408, 48), (105409, 48), (105410, 48), (105411, 48), (105412, 48), (105413, 48), (105414, 48), (105415, 48), (105416, 48), (105417, 48), (105418, 48), (105419, 48), (105420, 48), (105421, 48), (105422, 48), (105423, 48), (105424, 48), (105425, 48), (105426, 48), (105427, 48), (105428, 48), (105429, 48), (105430, 48), (105431, 48), (105432, 48), (105433, 48), (105434, 48), (105435, 48), (105436, 48), (105437, 48), (105438, 48), (105439, 48), (105440, 48), (105441, 48), (105442, 48), (105443, 48), (105444, 48), (105445, 48), (105446, 48), (105447, 48), (105448, 48), (105449, 48), (105450, 48), (105451, 48), (105452, 48), (105453, 48), (105454, 48), (105455, 48), (105456, 48), (105457, 48), (105458, 48), (105459, 48), (105460, 48), (105461, 48), (105462, 48), (105463, 48), (105464, 48), (105465, 48), (105466, 48), (105467, 48), (105468, 48), (105469, 48), (105470, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 418, 0, 0, 420, 439, 434, 434, 420, 0, 434, 434, 426, 439, 0, 0, 0, 0, 0, 0, 420, 432, 0, 0, 418, 418, 424, 0, 418, 418, 424, 0, 418, 418, 424, 0, 420, 439, 0, 0, 420, 0, 424, 0, 424, 439, 424, 0, 424, 0, 424, 0, 420, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 420, 439, 0, 0, 420, 0, 0, 0, 426, 439, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(105387, 48), (105390, 64), (105391, 88), (105397, 44), (105402, 56), (105403, 144), (105404, 48), (105405, 124), (105406, 224), (105407, 384), (105410, 0), (105411, 4), (105415, 16), (105419, 16), (105423, 48), (105426, 12), (105427, 28), (105429, 54), (105431, 144), (105435, 88), (105437, 93), (105439, 192), (105442, 24), (105443, 16), (105446, 48), (105447, 64), (105450, 48), (105451, 64), (105454, 168), (105455, 192), (105458, 64), (105459, 86), (105461, 136), (105462, 256), (105463, 400), (105466, 136), (105467, 252), (105468, 80), (105469, 204), (105470, 364)]

theorem l105387 : P.leaf 18 105387 = 48 := by decide +kernel

theorem l105390 : P.leaf 18 105390 = 64 := by decide +kernel

theorem l105391 : P.leaf 18 105391 = 88 := by decide +kernel

theorem l105397 : P.leaf 18 105397 = 44 := by decide +kernel

theorem l105402 : P.leaf 18 105402 = 56 := by decide +kernel

theorem l105403 : P.leaf 18 105403 = 144 := by decide +kernel

theorem l105404 : P.leaf 18 105404 = 48 := by decide +kernel

theorem l105405 : P.leaf 18 105405 = 124 := by decide +kernel

theorem l105406 : P.leaf 18 105406 = 224 := by decide +kernel

theorem l105407 : P.leaf 18 105407 = 384 := by decide +kernel

theorem l105410 : P.leaf 18 105410 = 0 := by decide +kernel

theorem l105411 : P.leaf 18 105411 = 4 := by decide +kernel

theorem l105415 : P.leaf 18 105415 = 16 := by decide +kernel

theorem l105419 : P.leaf 18 105419 = 16 := by decide +kernel

theorem l105423 : P.leaf 18 105423 = 48 := by decide +kernel

theorem l105426 : P.leaf 18 105426 = 12 := by decide +kernel

theorem l105427 : P.leaf 18 105427 = 28 := by decide +kernel

theorem l105429 : P.leaf 18 105429 = 54 := by decide +kernel

theorem l105431 : P.leaf 18 105431 = 144 := by decide +kernel

theorem l105435 : P.leaf 18 105435 = 88 := by decide +kernel

theorem l105437 : P.leaf 18 105437 = 93 := by decide +kernel

theorem l105439 : P.leaf 18 105439 = 192 := by decide +kernel

theorem l105442 : P.leaf 18 105442 = 24 := by decide +kernel

theorem l105443 : P.leaf 18 105443 = 16 := by decide +kernel

theorem l105446 : P.leaf 18 105446 = 48 := by decide +kernel

theorem l105447 : P.leaf 18 105447 = 64 := by decide +kernel

theorem l105450 : P.leaf 18 105450 = 48 := by decide +kernel

theorem l105451 : P.leaf 18 105451 = 64 := by decide +kernel

theorem l105454 : P.leaf 18 105454 = 168 := by decide +kernel

theorem l105455 : P.leaf 18 105455 = 192 := by decide +kernel

theorem l105458 : P.leaf 18 105458 = 64 := by decide +kernel

theorem l105459 : P.leaf 18 105459 = 86 := by decide +kernel

theorem l105461 : P.leaf 18 105461 = 136 := by decide +kernel

theorem l105462 : P.leaf 18 105462 = 256 := by decide +kernel

theorem l105463 : P.leaf 18 105463 = 400 := by decide +kernel

theorem l105466 : P.leaf 18 105466 = 136 := by decide +kernel

theorem l105467 : P.leaf 18 105467 = 252 := by decide +kernel

theorem l105468 : P.leaf 18 105468 = 80 := by decide +kernel

theorem l105469 : P.leaf 18 105469 = 204 := by decide +kernel

theorem l105470 : P.leaf 18 105470 = 364 := by decide +kernel

theorem segOK : checkSeg 20 perms 105387 105471 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 217008 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 105387 105471 4032 217008 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l105387 (.cons l105390 (.cons l105391 (.cons l105397 (.cons l105402 (.cons l105403 (.cons l105404 (.cons l105405 (.cons l105406 (.cons l105407 (.cons l105410 (.cons l105411 (.cons l105415 (.cons l105419 (.cons l105423 (.cons l105426 (.cons l105427 (.cons l105429 (.cons l105431 (.cons l105435 (.cons l105437 (.cons l105439 (.cons l105442 (.cons l105443 (.cons l105446 (.cons l105447 (.cons l105450 (.cons l105451 (.cons l105454 (.cons l105455 (.cons l105458 (.cons l105459 (.cons l105461 (.cons l105462 (.cons l105463 (.cons l105466 (.cons l105467 (.cons l105468 (.cons l105469 (.cons l105470 (.nil))))))))))))))))))))))))))))))))))))))))))

end S35

end RACert.S0N3.C0
