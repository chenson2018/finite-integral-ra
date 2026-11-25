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

namespace S14

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(61915, 48), (61916, 48), (61917, 48), (61918, 48), (61919, 48), (61936, 24), (61937, 48), (61939, 24), (61940, 48), (61941, 48), (61942, 48), (61943, 48), (61948, 24), (61949, 48), (61951, 24), (62208, 12), (62209, 24), (62211, 12), (62212, 24), (62213, 48), (62215, 24), (62220, 12), (62221, 24), (62223, 12), (62224, 24), (62225, 24), (62226, 24), (62227, 24), (62228, 48), (62229, 48), (62230, 48), (62231, 48), (62236, 24), (62237, 24), (62238, 24), (62239, 24), (62256, 12), (62257, 24), (62259, 12), (62260, 24), (62261, 48), (62263, 24), (62268, 12), (62269, 24), (62271, 12), (62272, 24), (62273, 48), (62275, 24), (62276, 24), (62277, 48), (62279, 24), (62280, 24), (62281, 48), (62283, 24), (62284, 24), (62285, 48), (62287, 24), (62288, 48), (62289, 48), (62290, 48), (62291, 48), (62292, 48), (62293, 48), (62294, 48), (62295, 48), (62296, 48), (62297, 48), (62298, 48), (62299, 48), (62300, 48), (62301, 48), (62302, 48), (62303, 48), (62320, 24), (62321, 48), (62323, 24), (62324, 24), (62325, 48), (62327, 24), (62328, 24), (62329, 48), (62331, 24), (62332, 24), (62333, 48), (62335, 24), (62400, 12), (62401, 24), (62403, 12), (62404, 24), (62405, 48), (62407, 24), (62412, 12), (62413, 24), (62415, 12), (62416, 24), (62417, 24), (62418, 24), (62419, 24), (62420, 48), (62421, 48), (62422, 48), (62423, 48), (62428, 24), (62429, 24), (62430, 24), (62431, 24), (62448, 12), (62449, 24), (62451, 12), (62452, 24), (62453, 48), (62455, 24), (62460, 12), (62461, 24), (62463, 12), (62720, 12), (62721, 48), (62723, 24), (62725, 48), (62727, 48), (62735, 12), (62736, 48), (62737, 48), (62738, 48), (62739, 48), (62740, 48), (62741, 48), (62742, 48), (62743, 48), (62744, 48), (62745, 48), (62746, 48), (62747, 48), (62748, 48), (62749, 48), (62750, 48), (62751, 48), (62768, 24), (62769, 48), (62771, 24), (62772, 48), (62773, 48), (62774, 48), (62775, 48), (62780, 24), (62781, 48), (62783, 24), (62800, 48), (62801, 48), (62802, 48), (62803, 48), (62804, 48), (62805, 48), (62806, 48), (62807, 48), (62808, 48), (62809, 48), (62810, 48), (62811, 48), (62812, 48), (62813, 48), (62814, 48), (62815, 48), (62832, 48), (62833, 48), (62834, 48), (62835, 48), (62836, 48), (62837, 48), (62838, 48), (62839, 48), (62840, 48), (62841, 48), (62842, 48), (62843, 48), (62844, 48), (62845, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 424, 0, 424, 0, 0, 439, 0, 0, 0, 431, 0, 0, 0, 0, 502, 432, 602, 418, 418, 602, 418, 418, 627, 550, 432, 431, 602, 424, 432, 424, 602, 424, 627, 424, 627, 602, 432, 602, 602, 432, 602, 627, 627, 627, 502, 432, 650, 418, 418, 0, 418, 418, 650, 418, 418, 0, 550, 432, 431, 650, 424, 432, 424, 0, 424, 439, 424, 650, 424, 684, 424, 0, 650, 432, 650, 683, 432, 0, 650, 439, 650, 683, 684, 0, 502, 432, 0, 418, 418, 0, 418, 418, 0, 550, 432, 431, 0, 424, 432, 424, 0, 424, 0, 424, 0, 0, 432, 0, 0, 432, 0, 0, 0, 0, 502, 434, 434, 432, 434, 614, 550, 434, 431, 434, 424, 432, 424, 434, 438, 439, 438, 440, 424, 627, 424, 627, 602, 434, 434, 432, 432, 431, 434, 0, 0, 0, 550, 439, 431, 440, 424, 432, 424, 0, 438, 439, 438, 440, 424, 0, 424, 0, 650, 439, 431, 440, 432, 432, 431, 0, 438, 439, 438, 440, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(61915, 122), (61917, 275), (61919, 617), (61936, 44), (61939, 204), (61940, 0), (61941, 84), (61943, 439), (61948, 392), (61949, 804), (61951, 3576), (62279, 18), (62287, 32), (62295, 82), (62303, 156), (62327, 118), (62335, 220), (62403, 24), (62407, 76), (62415, 364), (62419, 124), (62423, 386), (62429, 857), (62431, 1940), (62448, 72), (62451, 236), (62452, 0), (62455, 538), (62460, 708), (62461, 1558), (62463, 5320), (62780, 32), (62781, 80), (62783, 132), (62807, 149), (62813, 145), (62815, 328), (62839, 326), (62844, 104), (62845, 330)]

theorem l61915 : P.leaf 18 61915 = 122 := by decide +kernel

theorem l61917 : P.leaf 18 61917 = 275 := by decide +kernel

theorem l61919 : P.leaf 18 61919 = 617 := by decide +kernel

theorem l61936 : P.leaf 18 61936 = 44 := by decide +kernel

theorem l61939 : P.leaf 18 61939 = 204 := by decide +kernel

theorem l61940 : P.leaf 18 61940 = 0 := by decide +kernel

theorem l61941 : P.leaf 18 61941 = 84 := by decide +kernel

theorem l61943 : P.leaf 18 61943 = 439 := by decide +kernel

theorem l61948 : P.leaf 18 61948 = 392 := by decide +kernel

theorem l61949 : P.leaf 18 61949 = 804 := by decide +kernel

theorem l61951 : P.leaf 18 61951 = 3576 := by decide +kernel

theorem l62279 : P.leaf 18 62279 = 18 := by decide +kernel

theorem l62287 : P.leaf 18 62287 = 32 := by decide +kernel

theorem l62295 : P.leaf 18 62295 = 82 := by decide +kernel

theorem l62303 : P.leaf 18 62303 = 156 := by decide +kernel

theorem l62327 : P.leaf 18 62327 = 118 := by decide +kernel

theorem l62335 : P.leaf 18 62335 = 220 := by decide +kernel

theorem l62403 : P.leaf 18 62403 = 24 := by decide +kernel

theorem l62407 : P.leaf 18 62407 = 76 := by decide +kernel

theorem l62415 : P.leaf 18 62415 = 364 := by decide +kernel

theorem l62419 : P.leaf 18 62419 = 124 := by decide +kernel

theorem l62423 : P.leaf 18 62423 = 386 := by decide +kernel

theorem l62429 : P.leaf 18 62429 = 857 := by decide +kernel

theorem l62431 : P.leaf 18 62431 = 1940 := by decide +kernel

theorem l62448 : P.leaf 18 62448 = 72 := by decide +kernel

theorem l62451 : P.leaf 18 62451 = 236 := by decide +kernel

theorem l62452 : P.leaf 18 62452 = 0 := by decide +kernel

theorem l62455 : P.leaf 18 62455 = 538 := by decide +kernel

theorem l62460 : P.leaf 18 62460 = 708 := by decide +kernel

theorem l62461 : P.leaf 18 62461 = 1558 := by decide +kernel

theorem l62463 : P.leaf 18 62463 = 5320 := by decide +kernel

theorem l62780 : P.leaf 18 62780 = 32 := by decide +kernel

theorem l62781 : P.leaf 18 62781 = 80 := by decide +kernel

theorem l62783 : P.leaf 18 62783 = 132 := by decide +kernel

theorem l62807 : P.leaf 18 62807 = 149 := by decide +kernel

theorem l62813 : P.leaf 18 62813 = 145 := by decide +kernel

theorem l62815 : P.leaf 18 62815 = 328 := by decide +kernel

theorem l62839 : P.leaf 18 62839 = 326 := by decide +kernel

theorem l62844 : P.leaf 18 62844 = 104 := by decide +kernel

theorem l62845 : P.leaf 18 62845 = 330 := by decide +kernel

theorem segOK : checkSeg 20 perms 61915 62846 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 529848 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 61915 62846 6480 529848 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l61915 (.cons l61917 (.cons l61919 (.cons l61936 (.cons l61939 (.cons l61940 (.cons l61941 (.cons l61943 (.cons l61948 (.cons l61949 (.cons l61951 (.cons l62279 (.cons l62287 (.cons l62295 (.cons l62303 (.cons l62327 (.cons l62335 (.cons l62403 (.cons l62407 (.cons l62415 (.cons l62419 (.cons l62423 (.cons l62429 (.cons l62431 (.cons l62448 (.cons l62451 (.cons l62452 (.cons l62455 (.cons l62460 (.cons l62461 (.cons l62463 (.cons l62780 (.cons l62781 (.cons l62783 (.cons l62807 (.cons l62813 (.cons l62815 (.cons l62839 (.cons l62844 (.cons l62845 (.nil))))))))))))))))))))))))))))))))))))))))))

end S14

end RACert.S0N3.C0
