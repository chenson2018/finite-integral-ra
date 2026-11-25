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

namespace S117

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516408, 24), (516409, 24), (516410, 24), (516411, 24), (516412, 24), (516413, 24), (516414, 24), (516415, 24), (516417, 24), (516418, 24), (516419, 24), (516421, 24), (516422, 24), (516423, 24), (516425, 24), (516426, 24), (516427, 24), (516429, 24), (516430, 24), (516431, 24), (516433, 24), (516434, 24), (516435, 24), (516436, 24), (516437, 24), (516438, 24), (516439, 24), (516440, 12), (516441, 24), (516442, 24), (516443, 24), (516444, 24), (516445, 24), (516446, 24), (516447, 24), (516448, 24), (516449, 24), (516450, 24), (516451, 24), (516452, 24), (516453, 24), (516454, 24), (516455, 24), (516456, 24), (516457, 24), (516458, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 419, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 419, 0, 0, 0, 0, 0, 0, 418, 418, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516408, 0), (516409, 0), (516410, 0), (516411, 0), (516412, 65), (516413, 82), (516414, 198), (516415, 216), (516418, 3), (516419, 6), (516421, 6), (516422, 23), (516423, 30), (516426, 0), (516427, 0), (516430, 27), (516431, 32), (516433, 18), (516434, 16), (516435, 82), (516436, 33), (516437, 154), (516438, 189), (516439, 405), (516440, 0), (516441, 0), (516442, 0), (516443, 0), (516444, 90), (516445, 192), (516446, 264), (516447, 435), (516448, 22), (516450, 49), (516451, 65), (516452, 16), (516453, 10), (516454, 242), (516455, 270), (516458, 54)]

theorem l516408 : P.leaf 18 516408 = 0 := by decide +kernel

theorem l516409 : P.leaf 18 516409 = 0 := by decide +kernel

theorem l516410 : P.leaf 18 516410 = 0 := by decide +kernel

theorem l516411 : P.leaf 18 516411 = 0 := by decide +kernel

theorem l516412 : P.leaf 18 516412 = 65 := by decide +kernel

theorem l516413 : P.leaf 18 516413 = 82 := by decide +kernel

theorem l516414 : P.leaf 18 516414 = 198 := by decide +kernel

theorem l516415 : P.leaf 18 516415 = 216 := by decide +kernel

theorem l516418 : P.leaf 18 516418 = 3 := by decide +kernel

theorem l516419 : P.leaf 18 516419 = 6 := by decide +kernel

theorem l516421 : P.leaf 18 516421 = 6 := by decide +kernel

theorem l516422 : P.leaf 18 516422 = 23 := by decide +kernel

theorem l516423 : P.leaf 18 516423 = 30 := by decide +kernel

theorem l516426 : P.leaf 18 516426 = 0 := by decide +kernel

theorem l516427 : P.leaf 18 516427 = 0 := by decide +kernel

theorem l516430 : P.leaf 18 516430 = 27 := by decide +kernel

theorem l516431 : P.leaf 18 516431 = 32 := by decide +kernel

theorem l516433 : P.leaf 18 516433 = 18 := by decide +kernel

theorem l516434 : P.leaf 18 516434 = 16 := by decide +kernel

theorem l516435 : P.leaf 18 516435 = 82 := by decide +kernel

theorem l516436 : P.leaf 18 516436 = 33 := by decide +kernel

theorem l516437 : P.leaf 18 516437 = 154 := by decide +kernel

theorem l516438 : P.leaf 18 516438 = 189 := by decide +kernel

theorem l516439 : P.leaf 18 516439 = 405 := by decide +kernel

theorem l516440 : P.leaf 18 516440 = 0 := by decide +kernel

theorem l516441 : P.leaf 18 516441 = 0 := by decide +kernel

theorem l516442 : P.leaf 18 516442 = 0 := by decide +kernel

theorem l516443 : P.leaf 18 516443 = 0 := by decide +kernel

theorem l516444 : P.leaf 18 516444 = 90 := by decide +kernel

theorem l516445 : P.leaf 18 516445 = 192 := by decide +kernel

theorem l516446 : P.leaf 18 516446 = 264 := by decide +kernel

theorem l516447 : P.leaf 18 516447 = 435 := by decide +kernel

theorem l516448 : P.leaf 18 516448 = 22 := by decide +kernel

theorem l516450 : P.leaf 18 516450 = 49 := by decide +kernel

theorem l516451 : P.leaf 18 516451 = 65 := by decide +kernel

theorem l516452 : P.leaf 18 516452 = 16 := by decide +kernel

theorem l516453 : P.leaf 18 516453 = 10 := by decide +kernel

theorem l516454 : P.leaf 18 516454 = 242 := by decide +kernel

theorem l516455 : P.leaf 18 516455 = 270 := by decide +kernel

theorem l516458 : P.leaf 18 516458 = 54 := by decide +kernel

theorem segOK : checkSeg 20 perms 516408 516459 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 79056 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516408 516459 1092 79056 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l516408 (.cons l516409 (.cons l516410 (.cons l516411 (.cons l516412 (.cons l516413 (.cons l516414 (.cons l516415 (.cons l516418 (.cons l516419 (.cons l516421 (.cons l516422 (.cons l516423 (.cons l516426 (.cons l516427 (.cons l516430 (.cons l516431 (.cons l516433 (.cons l516434 (.cons l516435 (.cons l516436 (.cons l516437 (.cons l516438 (.cons l516439 (.cons l516440 (.cons l516441 (.cons l516442 (.cons l516443 (.cons l516444 (.cons l516445 (.cons l516446 (.cons l516447 (.cons l516448 (.cons l516450 (.cons l516451 (.cons l516452 (.cons l516453 (.cons l516454 (.cons l516455 (.cons l516458 (.nil))))))))))))))))))))))))))))))))))))))))))

end S117

end RACert.S0N3.C0
