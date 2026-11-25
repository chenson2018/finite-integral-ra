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

namespace S15

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(62846, 48), (62847, 48), (62960, 12), (62961, 48), (62963, 24), (62965, 48), (62967, 48), (62975, 12), (62976, 12), (62977, 48), (62979, 24), (62981, 24), (62982, 24), (62983, 48), (62991, 12), (62992, 48), (62993, 48), (62994, 48), (62995, 48), (62996, 48), (62997, 48), (62998, 48), (62999, 48), (63000, 48), (63001, 48), (63002, 48), (63003, 48), (63004, 48), (63005, 48), (63006, 48), (63007, 48), (63024, 24), (63025, 48), (63027, 24), (63028, 48), (63029, 48), (63030, 48), (63031, 48), (63036, 24), (63037, 48), (63039, 24), (63056, 24), (63057, 48), (63058, 48), (63059, 48), (63061, 24), (63062, 48), (63063, 48), (63066, 24), (63067, 48), (63071, 24), (63072, 24), (63073, 48), (63074, 48), (63075, 48), (63077, 48), (63078, 24), (63079, 48), (63081, 24), (63083, 48), (63087, 24), (63088, 48), (63089, 48), (63090, 48), (63091, 48), (63092, 48), (63093, 48), (63094, 48), (63095, 48), (63096, 48), (63097, 48), (63098, 48), (63099, 48), (63100, 48), (63101, 48), (63102, 48), (63103, 48), (63216, 12), (63217, 48), (63219, 24), (63221, 24), (63222, 24), (63223, 48), (63231, 12), (63232, 24), (63233, 48), (63235, 24), (63236, 48), (63237, 48), (63238, 48), (63239, 48), (63244, 24), (63245, 48), (63247, 24), (63248, 48), (63249, 48), (63250, 48), (63251, 48), (63252, 48), (63253, 48), (63254, 48), (63255, 48), (63256, 48), (63257, 48), (63258, 48), (63259, 48), (63260, 48), (63261, 48), (63262, 48), (63263, 48), (63280, 24), (63281, 48), (63283, 24), (63284, 48), (63285, 48), (63286, 48), (63287, 48), (63292, 24), (63293, 48), (63295, 24), (63296, 48), (63297, 48), (63298, 48), (63299, 48), (63300, 48), (63301, 48), (63302, 48), (63303, 48), (63304, 48), (63305, 48), (63306, 48), (63307, 48), (63308, 48), (63309, 48), (63310, 48), (63311, 48), (63312, 48), (63313, 48), (63314, 48), (63315, 48), (63316, 48), (63317, 48), (63318, 48), (63319, 48), (63320, 48), (63321, 48), (63322, 48), (63323, 48), (63324, 48), (63325, 48), (63326, 48), (63327, 48), (63328, 48), (63329, 48), (63330, 48), (63331, 48), (63332, 48), (63333, 48), (63334, 48), (63335, 48), (63336, 48), (63337, 48), (63338, 48), (63339, 48), (63340, 48), (63341, 48), (63342, 48), (63343, 48), (63344, 48), (63345, 48), (63346, 48), (63347, 48), (63348, 48), (63349, 48), (63350, 48), (63351, 48), (63352, 48), (63353, 48), (63354, 48), (63355, 48), (63356, 48), (63357, 48), (63358, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 439, 0, 432, 0, 0, 502, 432, 434, 418, 550, 434, 620, 550, 432, 438, 434, 432, 432, 550, 434, 424, 627, 424, 440, 424, 627, 424, 627, 602, 432, 434, 432, 432, 602, 434, 0, 0, 0, 550, 432, 438, 440, 432, 550, 0, 424, 440, 0, 502, 432, 438, 440, 418, 0, 0, 502, 440, 0, 650, 432, 438, 440, 432, 432, 0, 0, 438, 650, 438, 440, 0, 0, 0, 0, 0, 432, 0, 432, 0, 0, 0, 502, 432, 434, 418, 418, 424, 434, 418, 418, 627, 550, 432, 431, 434, 424, 432, 424, 434, 424, 439, 424, 440, 424, 627, 424, 627, 602, 432, 434, 432, 432, 431, 434, 0, 0, 0, 502, 432, 431, 440, 418, 418, 424, 0, 418, 418, 424, 440, 418, 418, 424, 0, 550, 432, 431, 440, 424, 432, 424, 0, 424, 439, 424, 440, 424, 0, 424, 0, 502, 432, 431, 440, 418, 418, 431, 0, 418, 418, 438, 440, 418, 418, 0, 0, 650, 432, 431, 440, 432, 432, 431, 0, 438, 439, 438, 440, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(62846, 330), (62847, 1034), (62960, 56), (62963, 240), (62967, 656), (62975, 2804), (63036, 32), (63037, 56), (63039, 148), (63063, 81), (63071, 210), (63078, 16), (63079, 63), (63087, 156), (63094, 40), (63095, 286), (63100, 88), (63101, 230), (63102, 220), (63103, 996), (63216, 56), (63219, 400), (63222, 100), (63223, 844), (63231, 5168), (63292, 72), (63293, 180), (63295, 252), (63303, 45), (63311, 176), (63319, 218), (63325, 512), (63327, 959), (63335, 218), (63342, 528), (63343, 970), (63351, 326), (63356, 320), (63357, 940), (63358, 940)]

theorem l62846 : P.leaf 18 62846 = 330 := by decide +kernel

theorem l62847 : P.leaf 18 62847 = 1034 := by decide +kernel

theorem l62960 : P.leaf 18 62960 = 56 := by decide +kernel

theorem l62963 : P.leaf 18 62963 = 240 := by decide +kernel

theorem l62967 : P.leaf 18 62967 = 656 := by decide +kernel

theorem l62975 : P.leaf 18 62975 = 2804 := by decide +kernel

theorem l63036 : P.leaf 18 63036 = 32 := by decide +kernel

theorem l63037 : P.leaf 18 63037 = 56 := by decide +kernel

theorem l63039 : P.leaf 18 63039 = 148 := by decide +kernel

theorem l63063 : P.leaf 18 63063 = 81 := by decide +kernel

theorem l63071 : P.leaf 18 63071 = 210 := by decide +kernel

theorem l63078 : P.leaf 18 63078 = 16 := by decide +kernel

theorem l63079 : P.leaf 18 63079 = 63 := by decide +kernel

theorem l63087 : P.leaf 18 63087 = 156 := by decide +kernel

theorem l63094 : P.leaf 18 63094 = 40 := by decide +kernel

theorem l63095 : P.leaf 18 63095 = 286 := by decide +kernel

theorem l63100 : P.leaf 18 63100 = 88 := by decide +kernel

theorem l63101 : P.leaf 18 63101 = 230 := by decide +kernel

theorem l63102 : P.leaf 18 63102 = 220 := by decide +kernel

theorem l63103 : P.leaf 18 63103 = 996 := by decide +kernel

theorem l63216 : P.leaf 18 63216 = 56 := by decide +kernel

theorem l63219 : P.leaf 18 63219 = 400 := by decide +kernel

theorem l63222 : P.leaf 18 63222 = 100 := by decide +kernel

theorem l63223 : P.leaf 18 63223 = 844 := by decide +kernel

theorem l63231 : P.leaf 18 63231 = 5168 := by decide +kernel

theorem l63292 : P.leaf 18 63292 = 72 := by decide +kernel

theorem l63293 : P.leaf 18 63293 = 180 := by decide +kernel

theorem l63295 : P.leaf 18 63295 = 252 := by decide +kernel

theorem l63303 : P.leaf 18 63303 = 45 := by decide +kernel

theorem l63311 : P.leaf 18 63311 = 176 := by decide +kernel

theorem l63319 : P.leaf 18 63319 = 218 := by decide +kernel

theorem l63325 : P.leaf 18 63325 = 512 := by decide +kernel

theorem l63327 : P.leaf 18 63327 = 959 := by decide +kernel

theorem l63335 : P.leaf 18 63335 = 218 := by decide +kernel

theorem l63342 : P.leaf 18 63342 = 528 := by decide +kernel

theorem l63343 : P.leaf 18 63343 = 970 := by decide +kernel

theorem l63351 : P.leaf 18 63351 = 326 := by decide +kernel

theorem l63356 : P.leaf 18 63356 = 320 := by decide +kernel

theorem l63357 : P.leaf 18 63357 = 940 := by decide +kernel

theorem l63358 : P.leaf 18 63358 = 940 := by decide +kernel

theorem segOK : checkSeg 20 perms 62846 63359 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 676320 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 62846 63359 7920 676320 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l62846 (.cons l62847 (.cons l62960 (.cons l62963 (.cons l62967 (.cons l62975 (.cons l63036 (.cons l63037 (.cons l63039 (.cons l63063 (.cons l63071 (.cons l63078 (.cons l63079 (.cons l63087 (.cons l63094 (.cons l63095 (.cons l63100 (.cons l63101 (.cons l63102 (.cons l63103 (.cons l63216 (.cons l63219 (.cons l63222 (.cons l63223 (.cons l63231 (.cons l63292 (.cons l63293 (.cons l63295 (.cons l63303 (.cons l63311 (.cons l63319 (.cons l63325 (.cons l63327 (.cons l63335 (.cons l63342 (.cons l63343 (.cons l63351 (.cons l63356 (.cons l63357 (.cons l63358 (.nil))))))))))))))))))))))))))))))))))))))))))

end S15

end RACert.S0N3.C0
