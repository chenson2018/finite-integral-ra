/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C5.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

namespace S2

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(334, 24), (335, 24), (339, 24), (340, 24), (341, 24), (342, 24), (343, 24), (344, 12), (345, 24), (346, 24), (347, 24), (348, 24), (349, 24), (350, 24), (351, 24), (355, 24), (357, 24), (358, 24), (359, 24), (360, 12), (361, 24), (362, 24), (363, 24), (364, 24), (365, 24), (366, 24), (367, 24), (371, 24), (372, 24), (373, 24), (374, 24), (375, 24), (376, 24), (377, 24), (378, 24), (379, 24), (380, 24), (381, 24), (382, 24), (383, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(334, 223), (335, 354), (339, 165), (340, 169), (341, 378), (342, 325), (343, 607), (344, 190), (345, 250), (346, 264), (347, 366), (348, 358), (349, 731), (350, 557), (351, 1118), (355, 180), (357, 261), (358, 374), (359, 498), (360, 189), (361, 299), (362, 288), (363, 454), (364, 440), (365, 531), (366, 690), (367, 927), (371, 305), (372, 368), (373, 548), (374, 618), (375, 774), (376, 348), (377, 487), (378, 461), (379, 669), (380, 702), (381, 896), (382, 1001), (383, 1354)]

theorem l334 : P.leaf 16 334 = 223 := by decide +kernel

theorem l335 : P.leaf 16 335 = 354 := by decide +kernel

theorem l339 : P.leaf 16 339 = 165 := by decide +kernel

theorem l340 : P.leaf 16 340 = 169 := by decide +kernel

theorem l341 : P.leaf 16 341 = 378 := by decide +kernel

theorem l342 : P.leaf 16 342 = 325 := by decide +kernel

theorem l343 : P.leaf 16 343 = 607 := by decide +kernel

theorem l344 : P.leaf 16 344 = 190 := by decide +kernel

theorem l345 : P.leaf 16 345 = 250 := by decide +kernel

theorem l346 : P.leaf 16 346 = 264 := by decide +kernel

theorem l347 : P.leaf 16 347 = 366 := by decide +kernel

theorem l348 : P.leaf 16 348 = 358 := by decide +kernel

theorem l349 : P.leaf 16 349 = 731 := by decide +kernel

theorem l350 : P.leaf 16 350 = 557 := by decide +kernel

theorem l351 : P.leaf 16 351 = 1118 := by decide +kernel

theorem l355 : P.leaf 16 355 = 180 := by decide +kernel

theorem l357 : P.leaf 16 357 = 261 := by decide +kernel

theorem l358 : P.leaf 16 358 = 374 := by decide +kernel

theorem l359 : P.leaf 16 359 = 498 := by decide +kernel

theorem l360 : P.leaf 16 360 = 189 := by decide +kernel

theorem l361 : P.leaf 16 361 = 299 := by decide +kernel

theorem l362 : P.leaf 16 362 = 288 := by decide +kernel

theorem l363 : P.leaf 16 363 = 454 := by decide +kernel

theorem l364 : P.leaf 16 364 = 440 := by decide +kernel

theorem l365 : P.leaf 16 365 = 531 := by decide +kernel

theorem l366 : P.leaf 16 366 = 690 := by decide +kernel

theorem l367 : P.leaf 16 367 = 927 := by decide +kernel

theorem l371 : P.leaf 16 371 = 305 := by decide +kernel

theorem l372 : P.leaf 16 372 = 368 := by decide +kernel

theorem l373 : P.leaf 16 373 = 548 := by decide +kernel

theorem l374 : P.leaf 16 374 = 618 := by decide +kernel

theorem l375 : P.leaf 16 375 = 774 := by decide +kernel

theorem l376 : P.leaf 16 376 = 348 := by decide +kernel

theorem l377 : P.leaf 16 377 = 487 := by decide +kernel

theorem l378 : P.leaf 16 378 = 461 := by decide +kernel

theorem l379 : P.leaf 16 379 = 669 := by decide +kernel

theorem l380 : P.leaf 16 380 = 702 := by decide +kernel

theorem l381 : P.leaf 16 381 = 896 := by decide +kernel

theorem l382 : P.leaf 16 382 = 1001 := by decide +kernel

theorem l383 : P.leaf 16 383 = 1354 := by decide +kernel

theorem segOK : checkSeg 12 perms 334 451 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 468660 = true := by decide +kernel

theorem total : OrbitSeg 12 perms (P.leaf 16) 334 451 936 468660 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l334 (.cons l335 (.cons l339 (.cons l340 (.cons l341 (.cons l342 (.cons l343 (.cons l344 (.cons l345 (.cons l346 (.cons l347 (.cons l348 (.cons l349 (.cons l350 (.cons l351 (.cons l355 (.cons l357 (.cons l358 (.cons l359 (.cons l360 (.cons l361 (.cons l362 (.cons l363 (.cons l364 (.cons l365 (.cons l366 (.cons l367 (.cons l371 (.cons l372 (.cons l373 (.cons l374 (.cons l375 (.cons l376 (.cons l377 (.cons l378 (.cons l379 (.cons l380 (.cons l381 (.cons l382 (.cons l383 (.nil))))))))))))))))))))))))))))))))))))))))))

end S2

end RACert.S0N3.C5
