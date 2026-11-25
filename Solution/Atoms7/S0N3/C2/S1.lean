/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C2.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C2

open RACert RACert.Problem

namespace S1

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(95, 8), (112, 4), (113, 8), (115, 4), (116, 8), (117, 8), (118, 8), (119, 8), (124, 4), (125, 8), (127, 4), (192, 2), (193, 4), (195, 2), (196, 4), (197, 4), (198, 4), (199, 4), (204, 2), (205, 4), (207, 2), (208, 4), (209, 4), (210, 4), (211, 4), (212, 4), (213, 4), (214, 4), (215, 4), (216, 4), (217, 4), (218, 4), (219, 4), (220, 4), (221, 4), (222, 4), (223, 4), (240, 2), (241, 4), (243, 2), (244, 4), (245, 4), (246, 4), (247, 4), (252, 2), (253, 4), (255, 2), (320, 2), (321, 4), (323, 2), (324, 4), (325, 4), (326, 4), (327, 4), (332, 2), (333, 4), (335, 2), (336, 4), (337, 4), (338, 4), (339, 4), (340, 4), (341, 4), (342, 4), (343, 4), (344, 4), (345, 4), (346, 4), (347, 4), (348, 4), (349, 4), (350, 4), (351, 4), (368, 2)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 417, 0, 0, 420, 0, 0, 0, 420, 0, 0, 501, 601, 613, 502, 601, 502, 614, 502, 602, 0, 417, 601, 502, 613, 503, 601, 0, 0, 417, 602, 502, 0, 602, 602, 0, 0, 417, 602, 0, 433, 602, 0, 0, 0, 0, 0, 417, 0, 0, 433, 0, 0, 0, 0, 0, 0, 417, 0, 0, 0, 420, 0, 0, 0, 417, 0, 0, 0, 420, 0, 0, 0, 417]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(95, 330), (113, 0), (115, 64), (117, 0), (118, 64), (119, 680), (125, 1078), (127, 3624), (207, 40), (214, 0), (215, 0), (219, 160), (222, 360), (223, 1432), (243, 640), (246, 576), (247, 3360), (252, 1077), (253, 2862), (255, 18864), (321, 0), (323, 16), (325, 0), (326, 3), (327, 72), (332, 624), (333, 23), (335, 458), (337, 0), (338, 1), (339, 112), (341, 0), (342, 273), (343, 434), (345, 84), (346, 11), (347, 456), (349, 238), (350, 1854), (351, 2131)]

theorem l95 : P.leaf 16 95 = 330 := by decide +kernel

theorem l113 : P.leaf 16 113 = 0 := by decide +kernel

theorem l115 : P.leaf 16 115 = 64 := by decide +kernel

theorem l117 : P.leaf 16 117 = 0 := by decide +kernel

theorem l118 : P.leaf 16 118 = 64 := by decide +kernel

theorem l119 : P.leaf 16 119 = 680 := by decide +kernel

theorem l125 : P.leaf 16 125 = 1078 := by decide +kernel

theorem l127 : P.leaf 16 127 = 3624 := by decide +kernel

theorem l207 : P.leaf 16 207 = 40 := by decide +kernel

theorem l214 : P.leaf 16 214 = 0 := by decide +kernel

theorem l215 : P.leaf 16 215 = 0 := by decide +kernel

theorem l219 : P.leaf 16 219 = 160 := by decide +kernel

theorem l222 : P.leaf 16 222 = 360 := by decide +kernel

theorem l223 : P.leaf 16 223 = 1432 := by decide +kernel

theorem l243 : P.leaf 16 243 = 640 := by decide +kernel

theorem l246 : P.leaf 16 246 = 576 := by decide +kernel

theorem l247 : P.leaf 16 247 = 3360 := by decide +kernel

theorem l252 : P.leaf 16 252 = 1077 := by decide +kernel

theorem l253 : P.leaf 16 253 = 2862 := by decide +kernel

theorem l255 : P.leaf 16 255 = 18864 := by decide +kernel

theorem l321 : P.leaf 16 321 = 0 := by decide +kernel

theorem l323 : P.leaf 16 323 = 16 := by decide +kernel

theorem l325 : P.leaf 16 325 = 0 := by decide +kernel

theorem l326 : P.leaf 16 326 = 3 := by decide +kernel

theorem l327 : P.leaf 16 327 = 72 := by decide +kernel

theorem l332 : P.leaf 16 332 = 624 := by decide +kernel

theorem l333 : P.leaf 16 333 = 23 := by decide +kernel

theorem l335 : P.leaf 16 335 = 458 := by decide +kernel

theorem l337 : P.leaf 16 337 = 0 := by decide +kernel

theorem l338 : P.leaf 16 338 = 1 := by decide +kernel

theorem l339 : P.leaf 16 339 = 112 := by decide +kernel

theorem l341 : P.leaf 16 341 = 0 := by decide +kernel

theorem l342 : P.leaf 16 342 = 273 := by decide +kernel

theorem l343 : P.leaf 16 343 = 434 := by decide +kernel

theorem l345 : P.leaf 16 345 = 84 := by decide +kernel

theorem l346 : P.leaf 16 346 = 11 := by decide +kernel

theorem l347 : P.leaf 16 347 = 456 := by decide +kernel

theorem l349 : P.leaf 16 349 = 238 := by decide +kernel

theorem l350 : P.leaf 16 350 = 1854 := by decide +kernel

theorem l351 : P.leaf 16 351 = 2131 := by decide +kernel

theorem segOK : checkSeg 10 perms 95 369 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 133174 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 16) 95 369 298 133174 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l95 (.cons l113 (.cons l115 (.cons l117 (.cons l118 (.cons l119 (.cons l125 (.cons l127 (.cons l207 (.cons l214 (.cons l215 (.cons l219 (.cons l222 (.cons l223 (.cons l243 (.cons l246 (.cons l247 (.cons l252 (.cons l253 (.cons l255 (.cons l321 (.cons l323 (.cons l325 (.cons l326 (.cons l327 (.cons l332 (.cons l333 (.cons l335 (.cons l337 (.cons l338 (.cons l339 (.cons l341 (.cons l342 (.cons l343 (.cons l345 (.cons l346 (.cons l347 (.cons l349 (.cons l350 (.cons l351 (.nil))))))))))))))))))))))))))))))))))))))))))

end S1

end RACert.S0N3.C2
