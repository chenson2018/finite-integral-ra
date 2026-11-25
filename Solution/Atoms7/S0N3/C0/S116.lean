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

namespace S116

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516193, 24), (516194, 24), (516195, 24), (516197, 24), (516198, 12), (516199, 24), (516201, 12), (516203, 24), (516207, 12), (516208, 24), (516209, 24), (516210, 24), (516211, 24), (516212, 24), (516213, 24), (516214, 24), (516215, 24), (516216, 24), (516217, 24), (516218, 24), (516219, 24), (516220, 24), (516221, 24), (516222, 24), (516223, 24), (516240, 12), (516241, 24), (516242, 24), (516243, 24), (516245, 24), (516246, 12), (516247, 24), (516249, 12), (516251, 24), (516255, 12), (516272, 24), (516273, 24), (516274, 24), (516275, 24), (516276, 24), (516277, 24), (516278, 24), (516279, 24), (516280, 24), (516281, 24), (516282, 24), (516283, 24), (516284, 24), (516285, 24), (516286, 24), (516287, 24), (516336, 12), (516337, 24), (516338, 24), (516339, 24), (516341, 24), (516342, 12), (516343, 24), (516345, 12), (516347, 24), (516351, 12), (516357, 24), (516358, 24), (516359, 24), (516361, 24), (516362, 24), (516363, 24), (516365, 24), (516366, 24), (516367, 24), (516373, 24), (516374, 12), (516375, 24), (516376, 24), (516377, 24), (516378, 24), (516379, 24), (516380, 24), (516381, 24), (516382, 24), (516383, 24), (516389, 12), (516391, 24), (516392, 24), (516393, 24), (516394, 24), (516395, 24), (516396, 24), (516397, 24), (516398, 24), (516399, 24), (516407, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 538, 538, 517, 0, 0, 0, 538, 0, 1224, 1224, 538, 538, 1224, 1224, 1224, 1224, 1224, 1224, 538, 538, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 0, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516193, 44), (516198, 117), (516199, 318), (516201, 179), (516207, 947), (516240, 5), (516241, 13), (516242, 14), (516243, 56), (516245, 59), (516246, 68), (516247, 192), (516249, 19), (516251, 112), (516255, 370), (516357, 3), (516358, 9), (516359, 12), (516362, 0), (516363, 0), (516366, 11), (516367, 12), (516373, 58), (516374, 81), (516375, 162), (516376, 0), (516377, 0), (516378, 0), (516379, 0), (516380, 51), (516381, 75), (516382, 117), (516383, 162), (516389, 2), (516391, 69), (516394, 0), (516395, 0), (516398, 94), (516399, 104), (516407, 207)]

theorem l516193 : P.leaf 18 516193 = 44 := by decide +kernel

theorem l516198 : P.leaf 18 516198 = 117 := by decide +kernel

theorem l516199 : P.leaf 18 516199 = 318 := by decide +kernel

theorem l516201 : P.leaf 18 516201 = 179 := by decide +kernel

theorem l516207 : P.leaf 18 516207 = 947 := by decide +kernel

theorem l516240 : P.leaf 18 516240 = 5 := by decide +kernel

theorem l516241 : P.leaf 18 516241 = 13 := by decide +kernel

theorem l516242 : P.leaf 18 516242 = 14 := by decide +kernel

theorem l516243 : P.leaf 18 516243 = 56 := by decide +kernel

theorem l516245 : P.leaf 18 516245 = 59 := by decide +kernel

theorem l516246 : P.leaf 18 516246 = 68 := by decide +kernel

theorem l516247 : P.leaf 18 516247 = 192 := by decide +kernel

theorem l516249 : P.leaf 18 516249 = 19 := by decide +kernel

theorem l516251 : P.leaf 18 516251 = 112 := by decide +kernel

theorem l516255 : P.leaf 18 516255 = 370 := by decide +kernel

theorem l516357 : P.leaf 18 516357 = 3 := by decide +kernel

theorem l516358 : P.leaf 18 516358 = 9 := by decide +kernel

theorem l516359 : P.leaf 18 516359 = 12 := by decide +kernel

theorem l516362 : P.leaf 18 516362 = 0 := by decide +kernel

theorem l516363 : P.leaf 18 516363 = 0 := by decide +kernel

theorem l516366 : P.leaf 18 516366 = 11 := by decide +kernel

theorem l516367 : P.leaf 18 516367 = 12 := by decide +kernel

theorem l516373 : P.leaf 18 516373 = 58 := by decide +kernel

theorem l516374 : P.leaf 18 516374 = 81 := by decide +kernel

theorem l516375 : P.leaf 18 516375 = 162 := by decide +kernel

theorem l516376 : P.leaf 18 516376 = 0 := by decide +kernel

theorem l516377 : P.leaf 18 516377 = 0 := by decide +kernel

theorem l516378 : P.leaf 18 516378 = 0 := by decide +kernel

theorem l516379 : P.leaf 18 516379 = 0 := by decide +kernel

theorem l516380 : P.leaf 18 516380 = 51 := by decide +kernel

theorem l516381 : P.leaf 18 516381 = 75 := by decide +kernel

theorem l516382 : P.leaf 18 516382 = 117 := by decide +kernel

theorem l516383 : P.leaf 18 516383 = 162 := by decide +kernel

theorem l516389 : P.leaf 18 516389 = 2 := by decide +kernel

theorem l516391 : P.leaf 18 516391 = 69 := by decide +kernel

theorem l516394 : P.leaf 18 516394 = 0 := by decide +kernel

theorem l516395 : P.leaf 18 516395 = 0 := by decide +kernel

theorem l516398 : P.leaf 18 516398 = 94 := by decide +kernel

theorem l516399 : P.leaf 18 516399 = 104 := by decide +kernel

theorem l516407 : P.leaf 18 516407 = 207 := by decide +kernel

theorem segOK : checkSeg 20 perms 516193 516408 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 65868 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516193 516408 2040 65868 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l516193 (.cons l516198 (.cons l516199 (.cons l516201 (.cons l516207 (.cons l516240 (.cons l516241 (.cons l516242 (.cons l516243 (.cons l516245 (.cons l516246 (.cons l516247 (.cons l516249 (.cons l516251 (.cons l516255 (.cons l516357 (.cons l516358 (.cons l516359 (.cons l516362 (.cons l516363 (.cons l516366 (.cons l516367 (.cons l516373 (.cons l516374 (.cons l516375 (.cons l516376 (.cons l516377 (.cons l516378 (.cons l516379 (.cons l516380 (.cons l516381 (.cons l516382 (.cons l516383 (.cons l516389 (.cons l516391 (.cons l516394 (.cons l516395 (.cons l516398 (.cons l516399 (.cons l516407 (.nil))))))))))))))))))))))))))))))))))))))))))

end S116

end RACert.S0N3.C0
