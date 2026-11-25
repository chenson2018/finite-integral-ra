/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (3, 1), (4, 4), (5, 8), (7, 4), (12, 4), (13, 4), (14, 4), (15, 4), (24, 2), (25, 4), (27, 2), (28, 4), (29, 8), (31, 4), (60, 1), (61, 2), (63, 1), (64, 2), (65, 2), (66, 2), (67, 2), (68, 8), (69, 8), (70, 8), (71, 8), (76, 4), (77, 4), (78, 4), (79, 4), (84, 4), (85, 4), (86, 4), (87, 4), (88, 4), (89, 4), (90, 4), (91, 4), (92, 8), (93, 8), (94, 8), (95, 8), (124, 2), (125, 2), (126, 2), (127, 2), (192, 1), (193, 2), (195, 1), (196, 4), (197, 8), (199, 4), (204, 4), (205, 4), (206, 4), (207, 4), (216, 2), (217, 4), (219, 2), (220, 4), (221, 8), (223, 4), (252, 1), (253, 2), (255, 1), (256, 2), (257, 2), (258, 2), (259, 2), (260, 8), (261, 8), (262, 8), (263, 8), (268, 4), (269, 4), (270, 4), (271, 4), (276, 4), (277, 4), (278, 4), (279, 4), (280, 4), (281, 4), (282, 4), (283, 4), (284, 8), (285, 8), (286, 8), (287, 8), (316, 2), (317, 2), (318, 2), (319, 2), (320, 2), (321, 2), (322, 2), (323, 2), (324, 8), (325, 8), (326, 8), (327, 8), (332, 4), (333, 4), (334, 4), (335, 4), (340, 4), (341, 4), (342, 4), (343, 4), (344, 4), (345, 4), (346, 4), (347, 4), (348, 8), (349, 8), (350, 8), (351, 8), (380, 2), (381, 2), (382, 2), (383, 2), (384, 2), (385, 2), (386, 2), (387, 2), (388, 8), (389, 8), (390, 8), (391, 8), (396, 4)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 622, 580, 601, 627, 601, 627, 0, 531, 531, 433, 628, 628, 433, 1217, 0, 0, 0, 0, 0, 1315, 622, 581, 581, 602, 627, 602, 627, 434, 1301, 434, 581, 1315, 532, 532, 532, 434, 628, 434, 628, 434, 1218, 434, 1315, 0, 0, 0, 0, 623, 581, 602, 627, 602, 627, 0, 532, 532, 434, 628, 628, 434, 1218, 0, 433, 0, 433, 0, 433, 622, 433, 580, 433, 634, 433, 634, 433, 1301, 433, 580, 433, 531, 433, 531, 433, 635, 433, 635, 433, 1217, 433, 1315, 0, 0, 0, 0, 1315, 622, 622, 622, 0, 0, 0, 0, 1301, 1301, 1315, 1315, 0, 0, 0, 0, 1301, 1301, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1316, 622, 622, 622, 602]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 241), (1, 65), (3, 71), (4, 2), (24, 164), (63, 1318), (64, 21), (65, 12), (66, 51), (67, 12), (192, 323), (193, 96), (195, 162), (196, 21), (216, 203), (255, 4096), (257, 12), (259, 12), (320, 30), (321, 54), (322, 76), (323, 54), (332, 9), (333, 300), (334, 12), (335, 800), (344, 0), (345, 43), (346, 450), (347, 1228), (350, 983), (351, 2676), (380, 1761), (381, 4665), (382, 3839), (383, 9441), (384, 4), (385, 24), (386, 0), (387, 0)]

theorem l0 : P.leaf 17 0 = 241 := by decide +kernel

theorem l1 : P.leaf 17 1 = 65 := by decide +kernel

theorem l3 : P.leaf 17 3 = 71 := by decide +kernel

theorem l4 : P.leaf 17 4 = 2 := by decide +kernel

theorem l24 : P.leaf 17 24 = 164 := by decide +kernel

theorem l63 : P.leaf 17 63 = 1318 := by decide +kernel

theorem l64 : P.leaf 17 64 = 21 := by decide +kernel

theorem l65 : P.leaf 17 65 = 12 := by decide +kernel

theorem l66 : P.leaf 17 66 = 51 := by decide +kernel

theorem l67 : P.leaf 17 67 = 12 := by decide +kernel

theorem l192 : P.leaf 17 192 = 323 := by decide +kernel

theorem l193 : P.leaf 17 193 = 96 := by decide +kernel

theorem l195 : P.leaf 17 195 = 162 := by decide +kernel

theorem l196 : P.leaf 17 196 = 21 := by decide +kernel

theorem l216 : P.leaf 17 216 = 203 := by decide +kernel

theorem l255 : P.leaf 17 255 = 4096 := by decide +kernel

theorem l257 : P.leaf 17 257 = 12 := by decide +kernel

theorem l259 : P.leaf 17 259 = 12 := by decide +kernel

theorem l320 : P.leaf 17 320 = 30 := by decide +kernel

theorem l321 : P.leaf 17 321 = 54 := by decide +kernel

theorem l322 : P.leaf 17 322 = 76 := by decide +kernel

theorem l323 : P.leaf 17 323 = 54 := by decide +kernel

theorem l332 : P.leaf 17 332 = 9 := by decide +kernel

theorem l333 : P.leaf 17 333 = 300 := by decide +kernel

theorem l334 : P.leaf 17 334 = 12 := by decide +kernel

theorem l335 : P.leaf 17 335 = 800 := by decide +kernel

theorem l344 : P.leaf 17 344 = 0 := by decide +kernel

theorem l345 : P.leaf 17 345 = 43 := by decide +kernel

theorem l346 : P.leaf 17 346 = 450 := by decide +kernel

theorem l347 : P.leaf 17 347 = 1228 := by decide +kernel

theorem l350 : P.leaf 17 350 = 983 := by decide +kernel

theorem l351 : P.leaf 17 351 = 2676 := by decide +kernel

theorem l380 : P.leaf 17 380 = 1761 := by decide +kernel

theorem l381 : P.leaf 17 381 = 4665 := by decide +kernel

theorem l382 : P.leaf 17 382 = 3839 := by decide +kernel

theorem l383 : P.leaf 17 383 = 9441 := by decide +kernel

theorem l384 : P.leaf 17 384 = 4 := by decide +kernel

theorem l385 : P.leaf 17 385 = 24 := by decide +kernel

theorem l386 : P.leaf 17 386 = 0 := by decide +kernel

theorem l387 : P.leaf 17 387 = 0 := by decide +kernel

theorem segOK : checkSeg 11 perms 0 397 seg = true := by decide +kernel

theorem evOK : P.checkEv 17 seg ev live 0 88135 = true := by decide +kernel

theorem total : OrbitSeg 11 perms (P.leaf 17) 0 397 556 88135 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l4 (.cons l24 (.cons l63 (.cons l64 (.cons l65 (.cons l66 (.cons l67 (.cons l192 (.cons l193 (.cons l195 (.cons l196 (.cons l216 (.cons l255 (.cons l257 (.cons l259 (.cons l320 (.cons l321 (.cons l322 (.cons l323 (.cons l332 (.cons l333 (.cons l334 (.cons l335 (.cons l344 (.cons l345 (.cons l346 (.cons l347 (.cons l350 (.cons l351 (.cons l380 (.cons l381 (.cons l382 (.cons l383 (.cons l384 (.cons l385 (.cons l386 (.cons l387 (.nil))))))))))))))))))))))))))))))))))))))))))

end S0

end RACert.S0N3.C1
