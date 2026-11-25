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

namespace S27

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(99207, 24), (99211, 24), (99215, 24), (99221, 24), (99222, 24), (99223, 24), (99225, 24), (99226, 24), (99227, 24), (99229, 24), (99230, 24), (99231, 24), (99237, 24), (99238, 24), (99239, 24), (99241, 24), (99242, 24), (99243, 24), (99245, 24), (99246, 24), (99247, 24), (99252, 12), (99253, 24), (99254, 24), (99255, 24), (99257, 24), (99258, 24), (99259, 24), (99260, 24), (99261, 24), (99262, 24), (99263, 24), (99267, 8), (99271, 24), (99275, 24), (99279, 24), (99285, 24), (99286, 24), (99287, 24), (99289, 24), (99290, 24), (99291, 24), (99293, 24), (99294, 24), (99295, 24), (99301, 24), (99302, 24), (99303, 24), (99305, 24), (99306, 24), (99307, 24), (99309, 24), (99310, 24), (99311, 24), (99317, 24), (99318, 24), (99319, 24), (99321, 24), (99322, 24), (99323, 24), (99324, 12), (99325, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 532, 424, 0, 419, 424, 0, 532, 424, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 420, 532, 0, 0, 419, 0, 0, 532, 532, 0, 0, 0, 0, 0, 0, 0, 424, 0, 419, 424, 0, 0, 424, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 419, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(99207, 4), (99211, 12), (99215, 16), (99223, 8), (99227, 24), (99231, 32), (99238, 4), (99239, 8), (99242, 20), (99243, 24), (99246, 24), (99247, 32), (99254, 20), (99255, 32), (99258, 20), (99259, 60), (99262, 32), (99263, 80), (99267, 8), (99271, 14), (99275, 14), (99279, 40), (99285, 18), (99287, 76), (99291, 28), (99293, 24), (99295, 80), (99302, 24), (99303, 28), (99306, 24), (99307, 28), (99310, 72), (99311, 80), (99317, 28), (99318, 100), (99319, 166), (99322, 28), (99323, 70), (99324, 16), (99325, 32)]

theorem l99207 : P.leaf 18 99207 = 4 := by decide +kernel

theorem l99211 : P.leaf 18 99211 = 12 := by decide +kernel

theorem l99215 : P.leaf 18 99215 = 16 := by decide +kernel

theorem l99223 : P.leaf 18 99223 = 8 := by decide +kernel

theorem l99227 : P.leaf 18 99227 = 24 := by decide +kernel

theorem l99231 : P.leaf 18 99231 = 32 := by decide +kernel

theorem l99238 : P.leaf 18 99238 = 4 := by decide +kernel

theorem l99239 : P.leaf 18 99239 = 8 := by decide +kernel

theorem l99242 : P.leaf 18 99242 = 20 := by decide +kernel

theorem l99243 : P.leaf 18 99243 = 24 := by decide +kernel

theorem l99246 : P.leaf 18 99246 = 24 := by decide +kernel

theorem l99247 : P.leaf 18 99247 = 32 := by decide +kernel

theorem l99254 : P.leaf 18 99254 = 20 := by decide +kernel

theorem l99255 : P.leaf 18 99255 = 32 := by decide +kernel

theorem l99258 : P.leaf 18 99258 = 20 := by decide +kernel

theorem l99259 : P.leaf 18 99259 = 60 := by decide +kernel

theorem l99262 : P.leaf 18 99262 = 32 := by decide +kernel

theorem l99263 : P.leaf 18 99263 = 80 := by decide +kernel

theorem l99267 : P.leaf 18 99267 = 8 := by decide +kernel

theorem l99271 : P.leaf 18 99271 = 14 := by decide +kernel

theorem l99275 : P.leaf 18 99275 = 14 := by decide +kernel

theorem l99279 : P.leaf 18 99279 = 40 := by decide +kernel

theorem l99285 : P.leaf 18 99285 = 18 := by decide +kernel

theorem l99287 : P.leaf 18 99287 = 76 := by decide +kernel

theorem l99291 : P.leaf 18 99291 = 28 := by decide +kernel

theorem l99293 : P.leaf 18 99293 = 24 := by decide +kernel

theorem l99295 : P.leaf 18 99295 = 80 := by decide +kernel

theorem l99302 : P.leaf 18 99302 = 24 := by decide +kernel

theorem l99303 : P.leaf 18 99303 = 28 := by decide +kernel

theorem l99306 : P.leaf 18 99306 = 24 := by decide +kernel

theorem l99307 : P.leaf 18 99307 = 28 := by decide +kernel

theorem l99310 : P.leaf 18 99310 = 72 := by decide +kernel

theorem l99311 : P.leaf 18 99311 = 80 := by decide +kernel

theorem l99317 : P.leaf 18 99317 = 28 := by decide +kernel

theorem l99318 : P.leaf 18 99318 = 100 := by decide +kernel

theorem l99319 : P.leaf 18 99319 = 166 := by decide +kernel

theorem l99322 : P.leaf 18 99322 = 28 := by decide +kernel

theorem l99323 : P.leaf 18 99323 = 70 := by decide +kernel

theorem l99324 : P.leaf 18 99324 = 16 := by decide +kernel

theorem l99325 : P.leaf 18 99325 = 32 := by decide +kernel

theorem segOK : checkSeg 20 perms 99207 99326 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 34480 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 99207 99326 1448 34480 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l99207 (.cons l99211 (.cons l99215 (.cons l99223 (.cons l99227 (.cons l99231 (.cons l99238 (.cons l99239 (.cons l99242 (.cons l99243 (.cons l99246 (.cons l99247 (.cons l99254 (.cons l99255 (.cons l99258 (.cons l99259 (.cons l99262 (.cons l99263 (.cons l99267 (.cons l99271 (.cons l99275 (.cons l99279 (.cons l99285 (.cons l99287 (.cons l99291 (.cons l99293 (.cons l99295 (.cons l99302 (.cons l99303 (.cons l99306 (.cons l99307 (.cons l99310 (.cons l99311 (.cons l99317 (.cons l99318 (.cons l99319 (.cons l99322 (.cons l99323 (.cons l99324 (.cons l99325 (.nil))))))))))))))))))))))))))))))))))))))))))

end S27

end RACert.S0N3.C0
