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

namespace S36

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(105471, 48), (106240, 24), (106241, 48), (106242, 48), (106243, 48), (106245, 48), (106246, 24), (106247, 48), (106249, 24), (106251, 48), (106255, 24), (106256, 48), (106257, 48), (106258, 48), (106259, 48), (106260, 48), (106261, 48), (106262, 48), (106263, 48), (106264, 48), (106265, 48), (106266, 48), (106267, 48), (106268, 48), (106269, 48), (106270, 48), (106271, 48), (106272, 48), (106273, 48), (106274, 48), (106275, 48), (106276, 48), (106277, 48), (106278, 48), (106279, 48), (106280, 48), (106281, 48), (106282, 48), (106283, 48), (106284, 48), (106285, 48), (106286, 48), (106287, 48), (106288, 48), (106289, 48), (106290, 48), (106291, 48), (106292, 48), (106293, 48), (106294, 48), (106295, 48), (106296, 48), (106297, 48), (106298, 48), (106299, 48), (106300, 48), (106301, 48), (106302, 48), (106303, 48), (106320, 48), (106321, 48), (106322, 48), (106323, 48), (106324, 48), (106325, 48), (106326, 48), (106327, 48), (106328, 48), (106329, 48), (106330, 48), (106331, 48), (106332, 48), (106333, 48), (106334, 48), (106335, 48), (106336, 24), (106337, 48), (106338, 48), (106339, 48), (106341, 48), (106342, 24), (106343, 48), (106345, 24), (106347, 48), (106351, 24), (106352, 48), (106353, 48), (106354, 48), (106355, 48), (106356, 48), (106357, 48), (106358, 48), (106359, 48), (106360, 48), (106361, 48), (106362, 48), (106363, 48), (106364, 48), (106365, 48), (106366, 48), (106367, 48), (106384, 24), (106385, 48), (106386, 48), (106387, 48), (106389, 48), (106390, 24), (106391, 48), (106393, 24), (106395, 48), (106399, 24), (106416, 48), (106417, 48), (106418, 48), (106419, 48), (106420, 48), (106421, 48), (106422, 48), (106423, 48), (106424, 48), (106425, 48), (106426, 48), (106427, 48), (106428, 48), (106429, 48), (106430, 48), (106431, 48), (106480, 24), (106481, 48), (106482, 48), (106483, 48), (106485, 48), (106486, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 420, 426, 434, 418, 424, 434, 418, 440, 0, 420, 434, 426, 434, 424, 434, 424, 434, 424, 439, 424, 440, 424, 0, 424, 0, 426, 420, 434, 434, 418, 418, 434, 434, 418, 418, 438, 440, 418, 418, 0, 0, 420, 434, 434, 434, 0, 434, 434, 434, 438, 439, 438, 440, 0, 0, 0, 0, 420, 439, 426, 440, 424, 0, 424, 0, 424, 439, 424, 440, 424, 0, 424, 0, 420, 432, 438, 440, 418, 0, 0, 418, 440, 0, 420, 439, 438, 440, 0, 0, 0, 0, 438, 439, 438, 440, 0, 0, 0, 0, 420, 434, 434, 434, 434, 424, 434, 439, 0, 0, 420, 434, 434, 434, 0, 434, 434, 434, 439, 439, 0, 0, 0, 0, 0, 0, 420, 439, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(105471, 656), (106240, 6), (106255, 16), (106269, 45), (106271, 112), (106286, 24), (106287, 48), (106292, 0), (106300, 14), (106301, 52), (106302, 52), (106303, 196), (106325, 108), (106327, 213), (106333, 162), (106335, 364), (106342, 45), (106343, 69), (106351, 140), (106356, 60), (106357, 120), (106358, 120), (106359, 456), (106364, 48), (106365, 184), (106366, 184), (106367, 656), (106395, 310), (106399, 668), (106420, 52), (106426, 290), (106427, 604), (106428, 184), (106429, 544), (106430, 872), (106431, 1480), (106482, 160), (106483, 376), (106485, 680), (106486, 1220)]

theorem l105471 : P.leaf 18 105471 = 656 := by decide +kernel

theorem l106240 : P.leaf 18 106240 = 6 := by decide +kernel

theorem l106255 : P.leaf 18 106255 = 16 := by decide +kernel

theorem l106269 : P.leaf 18 106269 = 45 := by decide +kernel

theorem l106271 : P.leaf 18 106271 = 112 := by decide +kernel

theorem l106286 : P.leaf 18 106286 = 24 := by decide +kernel

theorem l106287 : P.leaf 18 106287 = 48 := by decide +kernel

theorem l106292 : P.leaf 18 106292 = 0 := by decide +kernel

theorem l106300 : P.leaf 18 106300 = 14 := by decide +kernel

theorem l106301 : P.leaf 18 106301 = 52 := by decide +kernel

theorem l106302 : P.leaf 18 106302 = 52 := by decide +kernel

theorem l106303 : P.leaf 18 106303 = 196 := by decide +kernel

theorem l106325 : P.leaf 18 106325 = 108 := by decide +kernel

theorem l106327 : P.leaf 18 106327 = 213 := by decide +kernel

theorem l106333 : P.leaf 18 106333 = 162 := by decide +kernel

theorem l106335 : P.leaf 18 106335 = 364 := by decide +kernel

theorem l106342 : P.leaf 18 106342 = 45 := by decide +kernel

theorem l106343 : P.leaf 18 106343 = 69 := by decide +kernel

theorem l106351 : P.leaf 18 106351 = 140 := by decide +kernel

theorem l106356 : P.leaf 18 106356 = 60 := by decide +kernel

theorem l106357 : P.leaf 18 106357 = 120 := by decide +kernel

theorem l106358 : P.leaf 18 106358 = 120 := by decide +kernel

theorem l106359 : P.leaf 18 106359 = 456 := by decide +kernel

theorem l106364 : P.leaf 18 106364 = 48 := by decide +kernel

theorem l106365 : P.leaf 18 106365 = 184 := by decide +kernel

theorem l106366 : P.leaf 18 106366 = 184 := by decide +kernel

theorem l106367 : P.leaf 18 106367 = 656 := by decide +kernel

theorem l106395 : P.leaf 18 106395 = 310 := by decide +kernel

theorem l106399 : P.leaf 18 106399 = 668 := by decide +kernel

theorem l106420 : P.leaf 18 106420 = 52 := by decide +kernel

theorem l106426 : P.leaf 18 106426 = 290 := by decide +kernel

theorem l106427 : P.leaf 18 106427 = 604 := by decide +kernel

theorem l106428 : P.leaf 18 106428 = 184 := by decide +kernel

theorem l106429 : P.leaf 18 106429 = 544 := by decide +kernel

theorem l106430 : P.leaf 18 106430 = 872 := by decide +kernel

theorem l106431 : P.leaf 18 106431 = 1480 := by decide +kernel

theorem l106482 : P.leaf 18 106482 = 160 := by decide +kernel

theorem l106483 : P.leaf 18 106483 = 376 := by decide +kernel

theorem l106485 : P.leaf 18 106485 = 680 := by decide +kernel

theorem l106486 : P.leaf 18 106486 = 1220 := by decide +kernel

theorem segOK : checkSeg 20 perms 105471 106487 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 506040 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 105471 106487 6048 506040 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l105471 (.cons l106240 (.cons l106255 (.cons l106269 (.cons l106271 (.cons l106286 (.cons l106287 (.cons l106292 (.cons l106300 (.cons l106301 (.cons l106302 (.cons l106303 (.cons l106325 (.cons l106327 (.cons l106333 (.cons l106335 (.cons l106342 (.cons l106343 (.cons l106351 (.cons l106356 (.cons l106357 (.cons l106358 (.cons l106359 (.cons l106364 (.cons l106365 (.cons l106366 (.cons l106367 (.cons l106395 (.cons l106399 (.cons l106420 (.cons l106426 (.cons l106427 (.cons l106428 (.cons l106429 (.cons l106430 (.cons l106431 (.cons l106482 (.cons l106483 (.cons l106485 (.cons l106486 (.nil))))))))))))))))))))))))))))))))))))))))))

end S36

end RACert.S0N3.C0
