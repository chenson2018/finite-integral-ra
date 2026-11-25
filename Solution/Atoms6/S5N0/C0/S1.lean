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

namespace S1

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(229, 60), (231, 30), (236, 30), (237, 60), (239, 30), (252, 10), (253, 20), (255, 10), (352, 20), (353, 20), (354, 60), (355, 60), (358, 60), (359, 60), (366, 20), (367, 20), (368, 20), (369, 20), (370, 60), (371, 60), (374, 60), (375, 60), (382, 20), (383, 20), (384, 15), (385, 15), (386, 60), (387, 60), (390, 60), (391, 60), (396, 30), (397, 30), (398, 60), (399, 60), (414, 15), (415, 15), (416, 60), (417, 60), (418, 120), (419, 120), (422, 60), (423, 60), (424, 120), (425, 120), (426, 120), (427, 120), (428, 120), (429, 120), (430, 120), (431, 120), (440, 60), (441, 60), (442, 120), (443, 120), (446, 60), (447, 60), (480, 60), (481, 60), (482, 60), (483, 60), (484, 120), (485, 120), (486, 120), (487, 120), (492, 60), (493, 60), (494, 60), (495, 60), (496, 60), (497, 60), (498, 60), (499, 60), (500, 120), (501, 120), (502, 120), (503, 120), (508, 60), (509, 60), (510, 60), (511, 60), (960, 15), (961, 15), (962, 60), (963, 60), (966, 30), (967, 30), (970, 60), (971, 60), (974, 60), (975, 60), (990, 15), (991, 15), (992, 30), (993, 30), (994, 60), (995, 60), (998, 30), (999, 30), (1000, 60), (1001, 60), (1002, 120), (1003, 120), (1006, 60), (1007, 60), (1016, 30), (1017, 30), (1018, 60), (1019, 60), (1022, 30), (1023, 30), (2016, 5), (2017, 5), (2018, 20), (2019, 20), (2022, 30), (2023, 30), (2030, 20), (2031, 20), (2046, 5), (2047, 5), (2400, 5), (2401, 20), (2403, 30), (2407, 20), (2415, 5), (2416, 5)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(229, 81), (231, 175), (236, 114), (237, 93), (239, 211), (252, 132), (253, 105), (255, 247), (352, 513), (353, 1189), (354, 565), (355, 1355), (358, 629), (359, 1525), (366, 709), (367, 1697), (368, 513), (369, 1189), (370, 565), (371, 1355), (374, 629), (375, 1525), (382, 709), (383, 1697), (2016, 8408), (2017, 34926), (2018, 8456), (2019, 35783), (2022, 8504), (2023, 36646), (2030, 8552), (2031, 37513), (2046, 8600), (2047, 38383), (2400, 1259), (2401, 1741), (2403, 2577), (2407, 4097), (2415, 6753), (2416, 1259)]

theorem l229 : P.leaf 20 229 = 81 := by decide +kernel

theorem l231 : P.leaf 20 231 = 175 := by decide +kernel

theorem l236 : P.leaf 20 236 = 114 := by decide +kernel

theorem l237 : P.leaf 20 237 = 93 := by decide +kernel

theorem l239 : P.leaf 20 239 = 211 := by decide +kernel

theorem l252 : P.leaf 20 252 = 132 := by decide +kernel

theorem l253 : P.leaf 20 253 = 105 := by decide +kernel

theorem l255 : P.leaf 20 255 = 247 := by decide +kernel

theorem l352 : P.leaf 20 352 = 513 := by decide +kernel

theorem l353 : P.leaf 20 353 = 1189 := by decide +kernel

theorem l354 : P.leaf 20 354 = 565 := by decide +kernel

theorem l355 : P.leaf 20 355 = 1355 := by decide +kernel

theorem l358 : P.leaf 20 358 = 629 := by decide +kernel

theorem l359 : P.leaf 20 359 = 1525 := by decide +kernel

theorem l366 : P.leaf 20 366 = 709 := by decide +kernel

theorem l367 : P.leaf 20 367 = 1697 := by decide +kernel

theorem l368 : P.leaf 20 368 = 513 := by decide +kernel

theorem l369 : P.leaf 20 369 = 1189 := by decide +kernel

theorem l370 : P.leaf 20 370 = 565 := by decide +kernel

theorem l371 : P.leaf 20 371 = 1355 := by decide +kernel

theorem l374 : P.leaf 20 374 = 629 := by decide +kernel

theorem l375 : P.leaf 20 375 = 1525 := by decide +kernel

theorem l382 : P.leaf 20 382 = 709 := by decide +kernel

theorem l383 : P.leaf 20 383 = 1697 := by decide +kernel

theorem l2016 : P.leaf 20 2016 = 8408 := by decide +kernel

theorem l2017 : P.leaf 20 2017 = 34926 := by decide +kernel

theorem l2018 : P.leaf 20 2018 = 8456 := by decide +kernel

theorem l2019 : P.leaf 20 2019 = 35783 := by decide +kernel

theorem l2022 : P.leaf 20 2022 = 8504 := by decide +kernel

theorem l2023 : P.leaf 20 2023 = 36646 := by decide +kernel

theorem l2030 : P.leaf 20 2030 = 8552 := by decide +kernel

theorem l2031 : P.leaf 20 2031 = 37513 := by decide +kernel

theorem l2046 : P.leaf 20 2046 = 8600 := by decide +kernel

theorem l2047 : P.leaf 20 2047 = 38383 := by decide +kernel

theorem l2400 : P.leaf 20 2400 = 1259 := by decide +kernel

theorem l2401 : P.leaf 20 2401 = 1741 := by decide +kernel

theorem l2403 : P.leaf 20 2403 = 2577 := by decide +kernel

theorem l2407 : P.leaf 20 2407 = 4097 := by decide +kernel

theorem l2415 : P.leaf 20 2415 = 6753 := by decide +kernel

theorem l2416 : P.leaf 20 2416 = 1259 := by decide +kernel

theorem segOK : checkSeg 15 perms 229 2417 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 4537120 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 229 2417 6895 4537120 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l229 (.cons l231 (.cons l236 (.cons l237 (.cons l239 (.cons l252 (.cons l253 (.cons l255 (.cons l352 (.cons l353 (.cons l354 (.cons l355 (.cons l358 (.cons l359 (.cons l366 (.cons l367 (.cons l368 (.cons l369 (.cons l370 (.cons l371 (.cons l374 (.cons l375 (.cons l382 (.cons l383 (.cons l2016 (.cons l2017 (.cons l2018 (.cons l2019 (.cons l2022 (.cons l2023 (.cons l2030 (.cons l2031 (.cons l2046 (.cons l2047 (.cons l2400 (.cons l2401 (.cons l2403 (.cons l2407 (.cons l2415 (.cons l2416 (.nil))))))))))))))))))))))))))))))))))))))))))

end S1

end RACert.S5N0.C0
