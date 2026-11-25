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

namespace S33

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(104294, 48), (104295, 48), (104296, 48), (104297, 48), (104298, 48), (104299, 48), (104300, 48), (104301, 48), (104302, 48), (104303, 48), (104304, 48), (104305, 48), (104306, 48), (104307, 48), (104308, 48), (104309, 48), (104310, 48), (104311, 48), (104312, 48), (104313, 48), (104314, 48), (104315, 48), (104316, 48), (104317, 48), (104318, 48), (104319, 48), (104320, 48), (104321, 48), (104322, 48), (104323, 48), (104324, 48), (104325, 48), (104326, 48), (104327, 48), (104328, 48), (104329, 48), (104330, 48), (104331, 48), (104332, 48), (104333, 48), (104334, 48), (104335, 48), (104336, 48), (104337, 48), (104338, 48), (104339, 48), (104340, 48), (104341, 48), (104342, 48), (104343, 48), (104344, 48), (104345, 48), (104346, 48), (104347, 48), (104348, 48), (104349, 48), (104350, 48), (104351, 48), (104352, 48), (104353, 48), (104354, 48), (104355, 48), (104356, 48), (104357, 48), (104358, 48), (104359, 48), (104360, 48), (104361, 48), (104362, 48), (104363, 48), (104364, 48), (104365, 48), (104366, 48), (104367, 48), (104368, 48), (104369, 48), (104370, 48), (104371, 48), (104372, 48), (104373, 48), (104374, 48), (104375, 48), (104376, 48), (104377, 48), (104378, 48), (104379, 48), (104380, 48), (104381, 48), (104382, 48), (104383, 48), (104384, 48), (104385, 48), (104386, 48), (104387, 48), (104388, 48), (104389, 48), (104390, 48), (104391, 48), (104392, 48), (104393, 48), (104394, 48), (104395, 48), (104396, 48), (104397, 48), (104398, 48), (104399, 48), (104400, 48), (104401, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 418, 418, 438, 440, 418, 418, 0, 0, 420, 439, 438, 440, 0, 0, 0, 0, 438, 439, 438, 440, 0, 0, 0, 0, 426, 420, 0, 434, 418, 418, 424, 434, 418, 418, 424, 0, 418, 418, 424, 0, 420, 434, 0, 434, 424, 434, 424, 434, 424, 439, 424, 0, 424, 0, 424, 0, 426, 420, 0, 434, 418, 418, 0, 434, 418, 418, 0, 0, 418, 418, 0, 0, 420, 434, 0, 434, 0, 434, 0, 434, 0, 439, 0, 0, 0, 0, 0, 0, 420, 432, 0, 0, 418, 418, 424, 0, 418, 418, 424, 0, 418, 418, 424, 0, 420, 439]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(104294, 32), (104295, 54), (104302, 64), (104303, 132), (104308, 30), (104309, 48), (104310, 48), (104311, 234), (104316, 30), (104317, 104), (104318, 104), (104319, 468), (104322, 0), (104331, 29), (104335, 112), (104338, 8), (104347, 182), (104349, 214), (104351, 540), (104354, 10), (104358, 24), (104362, 56), (104363, 98), (104366, 196), (104367, 344), (104370, 40), (104372, 26), (104374, 198), (104376, 0), (104378, 118), (104379, 300), (104380, 140), (104381, 404), (104382, 632), (104383, 1236), (104386, 0), (104387, 10), (104391, 52), (104395, 36), (104399, 180)]

theorem l104294 : P.leaf 18 104294 = 32 := by decide +kernel

theorem l104295 : P.leaf 18 104295 = 54 := by decide +kernel

theorem l104302 : P.leaf 18 104302 = 64 := by decide +kernel

theorem l104303 : P.leaf 18 104303 = 132 := by decide +kernel

theorem l104308 : P.leaf 18 104308 = 30 := by decide +kernel

theorem l104309 : P.leaf 18 104309 = 48 := by decide +kernel

theorem l104310 : P.leaf 18 104310 = 48 := by decide +kernel

theorem l104311 : P.leaf 18 104311 = 234 := by decide +kernel

theorem l104316 : P.leaf 18 104316 = 30 := by decide +kernel

theorem l104317 : P.leaf 18 104317 = 104 := by decide +kernel

theorem l104318 : P.leaf 18 104318 = 104 := by decide +kernel

theorem l104319 : P.leaf 18 104319 = 468 := by decide +kernel

theorem l104322 : P.leaf 18 104322 = 0 := by decide +kernel

theorem l104331 : P.leaf 18 104331 = 29 := by decide +kernel

theorem l104335 : P.leaf 18 104335 = 112 := by decide +kernel

theorem l104338 : P.leaf 18 104338 = 8 := by decide +kernel

theorem l104347 : P.leaf 18 104347 = 182 := by decide +kernel

theorem l104349 : P.leaf 18 104349 = 214 := by decide +kernel

theorem l104351 : P.leaf 18 104351 = 540 := by decide +kernel

theorem l104354 : P.leaf 18 104354 = 10 := by decide +kernel

theorem l104358 : P.leaf 18 104358 = 24 := by decide +kernel

theorem l104362 : P.leaf 18 104362 = 56 := by decide +kernel

theorem l104363 : P.leaf 18 104363 = 98 := by decide +kernel

theorem l104366 : P.leaf 18 104366 = 196 := by decide +kernel

theorem l104367 : P.leaf 18 104367 = 344 := by decide +kernel

theorem l104370 : P.leaf 18 104370 = 40 := by decide +kernel

theorem l104372 : P.leaf 18 104372 = 26 := by decide +kernel

theorem l104374 : P.leaf 18 104374 = 198 := by decide +kernel

theorem l104376 : P.leaf 18 104376 = 0 := by decide +kernel

theorem l104378 : P.leaf 18 104378 = 118 := by decide +kernel

theorem l104379 : P.leaf 18 104379 = 300 := by decide +kernel

theorem l104380 : P.leaf 18 104380 = 140 := by decide +kernel

theorem l104381 : P.leaf 18 104381 = 404 := by decide +kernel

theorem l104382 : P.leaf 18 104382 = 632 := by decide +kernel

theorem l104383 : P.leaf 18 104383 = 1236 := by decide +kernel

theorem l104386 : P.leaf 18 104386 = 0 := by decide +kernel

theorem l104387 : P.leaf 18 104387 = 10 := by decide +kernel

theorem l104391 : P.leaf 18 104391 = 52 := by decide +kernel

theorem l104395 : P.leaf 18 104395 = 36 := by decide +kernel

theorem l104399 : P.leaf 18 104399 = 180 := by decide +kernel

theorem segOK : checkSeg 20 perms 104294 104402 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 313584 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 104294 104402 5184 313584 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l104294 (.cons l104295 (.cons l104302 (.cons l104303 (.cons l104308 (.cons l104309 (.cons l104310 (.cons l104311 (.cons l104316 (.cons l104317 (.cons l104318 (.cons l104319 (.cons l104322 (.cons l104331 (.cons l104335 (.cons l104338 (.cons l104347 (.cons l104349 (.cons l104351 (.cons l104354 (.cons l104358 (.cons l104362 (.cons l104363 (.cons l104366 (.cons l104367 (.cons l104370 (.cons l104372 (.cons l104374 (.cons l104376 (.cons l104378 (.cons l104379 (.cons l104380 (.cons l104381 (.cons l104382 (.cons l104383 (.cons l104386 (.cons l104387 (.cons l104391 (.cons l104395 (.cons l104399 (.nil))))))))))))))))))))))))))))))))))))))))))

end S33

end RACert.S0N3.C0
