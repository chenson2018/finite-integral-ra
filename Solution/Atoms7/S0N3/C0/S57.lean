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

namespace S57

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(127971, 48), (127972, 48), (127973, 48), (127974, 48), (127975, 48), (127976, 48), (127977, 48), (127978, 48), (127979, 48), (127980, 48), (127981, 48), (127982, 48), (127983, 48), (127984, 48), (127985, 48), (127986, 48), (127987, 48), (127988, 48), (127989, 48), (127990, 48), (127991, 48), (127992, 48), (127993, 48), (127994, 48), (127995, 48), (127996, 48), (127997, 48), (127998, 48), (127999, 48), (128256, 48), (128257, 48), (128258, 48), (128259, 48), (128260, 48), (128261, 48), (128262, 48), (128263, 48), (128264, 48), (128265, 48), (128266, 48), (128267, 48), (128268, 48), (128269, 48), (128270, 48), (128271, 48), (128272, 48), (128273, 48), (128274, 48), (128275, 48), (128276, 48), (128277, 48), (128278, 48), (128279, 48), (128280, 48), (128281, 48), (128282, 48), (128283, 48), (128284, 48), (128285, 48), (128286, 48), (128287, 48), (128288, 48), (128289, 48), (128290, 48), (128291, 48), (128292, 48), (128293, 48), (128294, 48), (128295, 48), (128296, 48), (128297, 48), (128298, 48), (128299, 48), (128300, 48), (128301, 48), (128302, 48), (128303, 48), (128304, 48), (128305, 48), (128306, 48), (128307, 48), (128308, 48), (128309, 48), (128310, 48), (128311, 48), (128312, 48), (128313, 48), (128314, 48), (128315, 48), (128316, 48), (128317, 48), (128318, 48), (128319, 48), (128320, 48), (128321, 48), (128322, 48), (128323, 48), (128324, 48), (128325, 48), (128326, 48), (128327, 48), (128328, 48), (128329, 48), (128330, 48), (128331, 48), (128332, 48), (128333, 48), (128334, 48), (128335, 48), (128336, 48), (128337, 48), (128338, 48), (128339, 48), (128340, 48), (128341, 48), (128342, 48), (128343, 48), (128344, 48), (128345, 48), (128346, 48), (128347, 48), (128348, 48), (128349, 48), (128350, 48), (128351, 48), (128352, 48), (128353, 48), (128354, 48), (128355, 48), (128356, 48), (128357, 48), (128358, 48), (128359, 48), (128360, 48), (128361, 48), (128362, 48), (128363, 48), (128364, 48), (128365, 48), (128366, 48), (128367, 48), (128368, 48), (128369, 48), (128370, 48), (128371, 48), (128372, 48), (128373, 48), (128374, 48), (128375, 48), (128376, 48), (128377, 48), (128378, 48), (128379, 48), (128380, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 424, 439, 434, 440, 432, 432, 550, 602, 418, 418, 438, 440, 418, 418, 550, 669, 434, 439, 434, 440, 550, 602, 550, 602, 438, 439, 438, 440, 550, 0, 550, 0, 434, 439, 434, 440, 432, 432, 602, 602, 418, 418, 438, 440, 418, 418, 684, 684, 434, 439, 434, 440, 602, 602, 602, 602, 438, 439, 438, 440, 0, 0, 0, 0, 424, 439, 440, 440, 432, 432, 550, 669, 418, 418, 438, 440, 418, 418, 550, 669, 550, 439, 440, 440, 550, 0, 550, 0, 438, 439, 438, 440, 550, 0, 550, 0, 502, 439, 440, 440, 432, 432, 0, 0, 418, 418, 438, 440, 418, 418, 0, 0, 650, 439, 440, 440, 0, 0, 0, 0, 438, 439, 438, 440, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(127971, 80), (127974, 393), (127975, 622), (127978, 172), (127979, 274), (127982, 755), (127983, 1351), (127984, 0), (127986, 64), (127987, 128), (127988, 204), (127989, 716), (127990, 732), (127991, 1656), (127992, 0), (127994, 226), (127995, 446), (127996, 360), (127997, 1294), (127998, 1288), (127999, 3402), (128285, 90), (128287, 130), (128316, 32), (128317, 120), (128318, 100), (128319, 192), (128341, 140), (128343, 440), (128349, 290), (128351, 725), (128358, 122), (128359, 270), (128366, 267), (128367, 497), (128372, 68), (128373, 204), (128374, 232), (128375, 628), (128380, 104)]

theorem l127971 : P.leaf 18 127971 = 80 := by decide +kernel

theorem l127974 : P.leaf 18 127974 = 393 := by decide +kernel

theorem l127975 : P.leaf 18 127975 = 622 := by decide +kernel

theorem l127978 : P.leaf 18 127978 = 172 := by decide +kernel

theorem l127979 : P.leaf 18 127979 = 274 := by decide +kernel

theorem l127982 : P.leaf 18 127982 = 755 := by decide +kernel

theorem l127983 : P.leaf 18 127983 = 1351 := by decide +kernel

theorem l127984 : P.leaf 18 127984 = 0 := by decide +kernel

theorem l127986 : P.leaf 18 127986 = 64 := by decide +kernel

theorem l127987 : P.leaf 18 127987 = 128 := by decide +kernel

theorem l127988 : P.leaf 18 127988 = 204 := by decide +kernel

theorem l127989 : P.leaf 18 127989 = 716 := by decide +kernel

theorem l127990 : P.leaf 18 127990 = 732 := by decide +kernel

theorem l127991 : P.leaf 18 127991 = 1656 := by decide +kernel

theorem l127992 : P.leaf 18 127992 = 0 := by decide +kernel

theorem l127994 : P.leaf 18 127994 = 226 := by decide +kernel

theorem l127995 : P.leaf 18 127995 = 446 := by decide +kernel

theorem l127996 : P.leaf 18 127996 = 360 := by decide +kernel

theorem l127997 : P.leaf 18 127997 = 1294 := by decide +kernel

theorem l127998 : P.leaf 18 127998 = 1288 := by decide +kernel

theorem l127999 : P.leaf 18 127999 = 3402 := by decide +kernel

theorem l128285 : P.leaf 18 128285 = 90 := by decide +kernel

theorem l128287 : P.leaf 18 128287 = 130 := by decide +kernel

theorem l128316 : P.leaf 18 128316 = 32 := by decide +kernel

theorem l128317 : P.leaf 18 128317 = 120 := by decide +kernel

theorem l128318 : P.leaf 18 128318 = 100 := by decide +kernel

theorem l128319 : P.leaf 18 128319 = 192 := by decide +kernel

theorem l128341 : P.leaf 18 128341 = 140 := by decide +kernel

theorem l128343 : P.leaf 18 128343 = 440 := by decide +kernel

theorem l128349 : P.leaf 18 128349 = 290 := by decide +kernel

theorem l128351 : P.leaf 18 128351 = 725 := by decide +kernel

theorem l128358 : P.leaf 18 128358 = 122 := by decide +kernel

theorem l128359 : P.leaf 18 128359 = 270 := by decide +kernel

theorem l128366 : P.leaf 18 128366 = 267 := by decide +kernel

theorem l128367 : P.leaf 18 128367 = 497 := by decide +kernel

theorem l128372 : P.leaf 18 128372 = 68 := by decide +kernel

theorem l128373 : P.leaf 18 128373 = 204 := by decide +kernel

theorem l128374 : P.leaf 18 128374 = 232 := by decide +kernel

theorem l128375 : P.leaf 18 128375 = 628 := by decide +kernel

theorem l128380 : P.leaf 18 128380 = 104 := by decide +kernel

theorem segOK : checkSeg 20 perms 127971 128381 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 903072 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 127971 128381 7392 903072 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l127971 (.cons l127974 (.cons l127975 (.cons l127978 (.cons l127979 (.cons l127982 (.cons l127983 (.cons l127984 (.cons l127986 (.cons l127987 (.cons l127988 (.cons l127989 (.cons l127990 (.cons l127991 (.cons l127992 (.cons l127994 (.cons l127995 (.cons l127996 (.cons l127997 (.cons l127998 (.cons l127999 (.cons l128285 (.cons l128287 (.cons l128316 (.cons l128317 (.cons l128318 (.cons l128319 (.cons l128341 (.cons l128343 (.cons l128349 (.cons l128351 (.cons l128358 (.cons l128359 (.cons l128366 (.cons l128367 (.cons l128372 (.cons l128373 (.cons l128374 (.cons l128375 (.cons l128380 (.nil))))))))))))))))))))))))))))))))))))))))))

end S57

end RACert.S0N3.C0
