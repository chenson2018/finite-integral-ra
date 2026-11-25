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

namespace S96

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(261563, 48), (261567, 48), (261599, 24), (261615, 24), (261619, 48), (261623, 48), (261627, 48), (261631, 48), (261939, 12), (261943, 24), (261947, 24), (261951, 24), (262007, 24), (262011, 12), (262015, 24), (262071, 12), (262079, 24), (262143, 12), (430080, 2), (430081, 24), (430083, 12), (430085, 24), (430087, 24), (430095, 6), (430097, 12), (430098, 12), (430099, 24), (430100, 48), (430101, 48), (430102, 48), (430103, 48), (430108, 24), (430109, 24), (430110, 24), (430111, 24), (430131, 6), (430132, 24), (430133, 48), (430135, 24), (430140, 12), (430141, 24), (430143, 12), (430160, 24), (430161, 48), (430162, 48), (430163, 48), (430165, 24), (430166, 48), (430167, 48), (430170, 24), (430171, 48), (430175, 24), (430192, 24), (430193, 48), (430195, 24), (430196, 24), (430197, 48), (430199, 24), (430200, 24), (430201, 48), (430203, 24), (430204, 24), (430205, 48), (430207, 24), (430320, 6), (430321, 24), (430323, 12), (430325, 24), (430327, 24), (430335, 6), (430341, 48), (430342, 48), (430343, 48), (430349, 48), (430351, 24), (430357, 48), (430358, 24), (430359, 48), (430362, 24), (430363, 48), (430364, 48), (430365, 48), (430366, 48), (430367, 48), (430391, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 440, 0, 440, 0, 0, 440, 0, 0, 0, 0, 418, 434, 434, 1218, 1218, 1218, 434, 434, 434, 573, 1218, 573, 1218, 573, 1218, 573, 1218, 434, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 587, 684, 587, 1218, 573, 1218, 620, 587, 1218, 0, 587, 587, 0, 0, 0, 0, 587, 587, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 431, 0, 0, 0, 0, 431, 0, 0, 0, 573, 0, 573, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(261563, 3794), (261567, 9174), (261599, 10716), (261615, 10572), (261619, 1376), (261623, 8597), (261627, 4993), (261631, 16160), (261943, 952), (261951, 1712), (262007, 5140), (262015, 7520), (262071, 7500), (262079, 12604), (262143, 22468), (430192, 0), (430196, 8), (430197, 13), (430199, 68), (430200, 0), (430204, 139), (430205, 111), (430207, 230), (430320, 17), (430321, 46), (430323, 434), (430325, 36), (430327, 300), (430335, 1194), (430341, 0), (430343, 0), (430349, 0), (430351, 12), (430357, 0), (430359, 0), (430362, 0), (430363, 0), (430365, 9), (430367, 48), (430391, 0)]

theorem l261563 : P.leaf 18 261563 = 3794 := by decide +kernel

theorem l261567 : P.leaf 18 261567 = 9174 := by decide +kernel

theorem l261599 : P.leaf 18 261599 = 10716 := by decide +kernel

theorem l261615 : P.leaf 18 261615 = 10572 := by decide +kernel

theorem l261619 : P.leaf 18 261619 = 1376 := by decide +kernel

theorem l261623 : P.leaf 18 261623 = 8597 := by decide +kernel

theorem l261627 : P.leaf 18 261627 = 4993 := by decide +kernel

theorem l261631 : P.leaf 18 261631 = 16160 := by decide +kernel

theorem l261943 : P.leaf 18 261943 = 952 := by decide +kernel

theorem l261951 : P.leaf 18 261951 = 1712 := by decide +kernel

theorem l262007 : P.leaf 18 262007 = 5140 := by decide +kernel

theorem l262015 : P.leaf 18 262015 = 7520 := by decide +kernel

theorem l262071 : P.leaf 18 262071 = 7500 := by decide +kernel

theorem l262079 : P.leaf 18 262079 = 12604 := by decide +kernel

theorem l262143 : P.leaf 18 262143 = 22468 := by decide +kernel

theorem l430192 : P.leaf 18 430192 = 0 := by decide +kernel

theorem l430196 : P.leaf 18 430196 = 8 := by decide +kernel

theorem l430197 : P.leaf 18 430197 = 13 := by decide +kernel

theorem l430199 : P.leaf 18 430199 = 68 := by decide +kernel

theorem l430200 : P.leaf 18 430200 = 0 := by decide +kernel

theorem l430204 : P.leaf 18 430204 = 139 := by decide +kernel

theorem l430205 : P.leaf 18 430205 = 111 := by decide +kernel

theorem l430207 : P.leaf 18 430207 = 230 := by decide +kernel

theorem l430320 : P.leaf 18 430320 = 17 := by decide +kernel

theorem l430321 : P.leaf 18 430321 = 46 := by decide +kernel

theorem l430323 : P.leaf 18 430323 = 434 := by decide +kernel

theorem l430325 : P.leaf 18 430325 = 36 := by decide +kernel

theorem l430327 : P.leaf 18 430327 = 300 := by decide +kernel

theorem l430335 : P.leaf 18 430335 = 1194 := by decide +kernel

theorem l430341 : P.leaf 18 430341 = 0 := by decide +kernel

theorem l430343 : P.leaf 18 430343 = 0 := by decide +kernel

theorem l430349 : P.leaf 18 430349 = 0 := by decide +kernel

theorem l430351 : P.leaf 18 430351 = 12 := by decide +kernel

theorem l430357 : P.leaf 18 430357 = 0 := by decide +kernel

theorem l430359 : P.leaf 18 430359 = 0 := by decide +kernel

theorem l430362 : P.leaf 18 430362 = 0 := by decide +kernel

theorem l430363 : P.leaf 18 430363 = 0 := by decide +kernel

theorem l430365 : P.leaf 18 430365 = 9 := by decide +kernel

theorem l430367 : P.leaf 18 430367 = 48 := by decide +kernel

theorem l430391 : P.leaf 18 430391 = 0 := by decide +kernel

theorem segOK : checkSeg 20 perms 261563 430396 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 3698610 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 261563 430396 2594 3698610 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l261563 (.cons l261567 (.cons l261599 (.cons l261615 (.cons l261619 (.cons l261623 (.cons l261627 (.cons l261631 (.cons l261943 (.cons l261951 (.cons l262007 (.cons l262015 (.cons l262071 (.cons l262079 (.cons l262143 (.cons l430192 (.cons l430196 (.cons l430197 (.cons l430199 (.cons l430200 (.cons l430204 (.cons l430205 (.cons l430207 (.cons l430320 (.cons l430321 (.cons l430323 (.cons l430325 (.cons l430327 (.cons l430335 (.cons l430341 (.cons l430343 (.cons l430349 (.cons l430351 (.cons l430357 (.cons l430359 (.cons l430362 (.cons l430363 (.cons l430365 (.cons l430367 (.cons l430391 (.nil))))))))))))))))))))))))))))))))))))))))))

end S96

end RACert.S0N3.C0
