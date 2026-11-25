/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S11

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(16352, 10), (16353, 20), (16355, 10), (16356, 30), (16357, 60), (16359, 30), (16364, 30), (16365, 60), (16367, 30), (16380, 10), (16381, 20), (16383, 10), (32736, 1), (32737, 5), (32739, 10), (32743, 10), (32751, 5), (32767, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(16352, 103056), (16353, 176980), (16355, 294204), (16356, 122590), (16357, 216910), (16359, 371712), (16364, 146034), (16365, 266467), (16367, 470720), (16380, 174396), (16381, 328776), (16383, 600576), (32736, 165399), (32737, 223381), (32739, 308796), (32743, 440192), (32751, 655360), (32767, 1048576)]

theorem l16352 : P.leaf 20 16352 = 103056 := by decide +kernel

theorem l16353 : P.leaf 20 16353 = 176980 := by decide +kernel

theorem l16355 : P.leaf 20 16355 = 294204 := by decide +kernel

theorem l16356 : P.leaf 20 16356 = 122590 := by decide +kernel

theorem l16357 : P.leaf 20 16357 = 216910 := by decide +kernel

theorem l16359 : P.leaf 20 16359 = 371712 := by decide +kernel

theorem l16364 : P.leaf 20 16364 = 146034 := by decide +kernel

theorem l16365 : P.leaf 20 16365 = 266467 := by decide +kernel

theorem l16367 : P.leaf 20 16367 = 470720 := by decide +kernel

theorem l16380 : P.leaf 20 16380 = 174396 := by decide +kernel

theorem l16381 : P.leaf 20 16381 = 328776 := by decide +kernel

theorem l16383 : P.leaf 20 16383 = 600576 := by decide +kernel

theorem l32736 : P.leaf 20 32736 = 165399 := by decide +kernel

theorem l32737 : P.leaf 20 32737 = 223381 := by decide +kernel

theorem l32739 : P.leaf 20 32739 = 308796 := by decide +kernel

theorem l32743 : P.leaf 20 32743 = 440192 := by decide +kernel

theorem l32751 : P.leaf 20 32751 = 655360 := by decide +kernel

theorem l32767 : P.leaf 20 32767 = 1048576 := by decide +kernel

theorem segOK : checkSeg 15 perms 16352 32768 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 97269300 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 16352 32768 352 97269300 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l16352 (.cons l16353 (.cons l16355 (.cons l16356 (.cons l16357 (.cons l16359 (.cons l16364 (.cons l16365 (.cons l16367 (.cons l16380 (.cons l16381 (.cons l16383 (.cons l32736 (.cons l32737 (.cons l32739 (.cons l32743 (.cons l32751 (.cons l32767 (.nil))))))))))))))))))))

end S11

end RACert.S5N0.C0
