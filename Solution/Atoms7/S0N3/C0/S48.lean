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

namespace S48

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(124349, 48), (124350, 48), (124351, 48), (124352, 48), (124353, 48), (124354, 48), (124355, 48), (124356, 48), (124357, 48), (124358, 48), (124359, 48), (124360, 48), (124361, 48), (124362, 48), (124363, 48), (124364, 48), (124365, 48), (124366, 48), (124367, 48), (124368, 48), (124369, 48), (124370, 48), (124371, 48), (124372, 48), (124373, 48), (124374, 48), (124375, 48), (124376, 48), (124377, 48), (124378, 48), (124379, 48), (124380, 48), (124381, 48), (124382, 48), (124383, 48), (124384, 48), (124385, 48), (124386, 48), (124387, 48), (124388, 48), (124389, 48), (124390, 48), (124391, 48), (124392, 48), (124393, 48), (124394, 48), (124395, 48), (124396, 48), (124397, 48), (124398, 48), (124399, 48), (124400, 48), (124401, 48), (124402, 48), (124403, 48), (124404, 48), (124405, 48), (124406, 48), (124407, 48), (124408, 48), (124409, 48), (124410, 48), (124411, 48), (124412, 48), (124413, 48), (124414, 48), (124415, 48), (124416, 24), (124417, 48), (124418, 48), (124419, 48), (124421, 48), (124422, 24), (124423, 48), (124425, 24), (124427, 48), (124431, 24), (124432, 48), (124433, 48), (124434, 48), (124435, 48), (124436, 48), (124437, 48), (124438, 48), (124439, 48), (124440, 48), (124441, 48), (124442, 48), (124443, 48), (124444, 48), (124445, 48), (124446, 48), (124447, 48), (124448, 48), (124449, 48), (124450, 48), (124451, 48), (124452, 48), (124453, 48), (124454, 48), (124455, 48), (124456, 48), (124457, 48), (124458, 48), (124459, 48), (124460, 48), (124461, 48), (124462, 48), (124463, 48), (124464, 48), (124465, 48), (124466, 48), (124467, 48), (124468, 48), (124469, 48), (124470, 48), (124471, 48), (124472, 48), (124473, 48), (124474, 48), (124475, 48), (124476, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 424, 439, 550, 0, 432, 432, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 503, 439, 0, 0, 432, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 424, 432, 434, 440, 418, 550, 602, 0, 440, 663, 434, 503, 434, 440, 550, 602, 550, 602, 438, 503, 438, 440, 550, 0, 550, 0, 434, 432, 434, 440, 418, 418, 602, 602, 438, 0, 438, 440, 418, 418, 684, 684, 434, 503, 434, 440, 602, 602, 602, 602, 438, 503, 438, 440, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(124349, 272), (124350, 506), (124351, 1074), (124355, 4), (124359, 36), (124363, 16), (124367, 60), (124371, 80), (124373, 164), (124375, 574), (124379, 216), (124381, 273), (124383, 1060), (124386, 16), (124387, 24), (124390, 96), (124391, 226), (124394, 40), (124395, 80), (124398, 268), (124399, 492), (124400, 0), (124402, 40), (124403, 94), (124404, 64), (124405, 248), (124406, 400), (124407, 898), (124408, 0), (124410, 156), (124411, 264), (124412, 138), (124413, 376), (124414, 768), (124415, 1668), (124425, 6), (124445, 10), (124447, 40), (124457, 15), (124476, 8)]

theorem l124349 : P.leaf 18 124349 = 272 := by decide +kernel

theorem l124350 : P.leaf 18 124350 = 506 := by decide +kernel

theorem l124351 : P.leaf 18 124351 = 1074 := by decide +kernel

theorem l124355 : P.leaf 18 124355 = 4 := by decide +kernel

theorem l124359 : P.leaf 18 124359 = 36 := by decide +kernel

theorem l124363 : P.leaf 18 124363 = 16 := by decide +kernel

theorem l124367 : P.leaf 18 124367 = 60 := by decide +kernel

theorem l124371 : P.leaf 18 124371 = 80 := by decide +kernel

theorem l124373 : P.leaf 18 124373 = 164 := by decide +kernel

theorem l124375 : P.leaf 18 124375 = 574 := by decide +kernel

theorem l124379 : P.leaf 18 124379 = 216 := by decide +kernel

theorem l124381 : P.leaf 18 124381 = 273 := by decide +kernel

theorem l124383 : P.leaf 18 124383 = 1060 := by decide +kernel

theorem l124386 : P.leaf 18 124386 = 16 := by decide +kernel

theorem l124387 : P.leaf 18 124387 = 24 := by decide +kernel

theorem l124390 : P.leaf 18 124390 = 96 := by decide +kernel

theorem l124391 : P.leaf 18 124391 = 226 := by decide +kernel

theorem l124394 : P.leaf 18 124394 = 40 := by decide +kernel

theorem l124395 : P.leaf 18 124395 = 80 := by decide +kernel

theorem l124398 : P.leaf 18 124398 = 268 := by decide +kernel

theorem l124399 : P.leaf 18 124399 = 492 := by decide +kernel

theorem l124400 : P.leaf 18 124400 = 0 := by decide +kernel

theorem l124402 : P.leaf 18 124402 = 40 := by decide +kernel

theorem l124403 : P.leaf 18 124403 = 94 := by decide +kernel

theorem l124404 : P.leaf 18 124404 = 64 := by decide +kernel

theorem l124405 : P.leaf 18 124405 = 248 := by decide +kernel

theorem l124406 : P.leaf 18 124406 = 400 := by decide +kernel

theorem l124407 : P.leaf 18 124407 = 898 := by decide +kernel

theorem l124408 : P.leaf 18 124408 = 0 := by decide +kernel

theorem l124410 : P.leaf 18 124410 = 156 := by decide +kernel

theorem l124411 : P.leaf 18 124411 = 264 := by decide +kernel

theorem l124412 : P.leaf 18 124412 = 138 := by decide +kernel

theorem l124413 : P.leaf 18 124413 = 376 := by decide +kernel

theorem l124414 : P.leaf 18 124414 = 768 := by decide +kernel

theorem l124415 : P.leaf 18 124415 = 1668 := by decide +kernel

theorem l124425 : P.leaf 18 124425 = 6 := by decide +kernel

theorem l124445 : P.leaf 18 124445 = 10 := by decide +kernel

theorem l124447 : P.leaf 18 124447 = 40 := by decide +kernel

theorem l124457 : P.leaf 18 124457 = 15 := by decide +kernel

theorem l124476 : P.leaf 18 124476 = 8 := by decide +kernel

theorem segOK : checkSeg 20 perms 124349 124477 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 516816 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 124349 124477 5760 516816 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l124349 (.cons l124350 (.cons l124351 (.cons l124355 (.cons l124359 (.cons l124363 (.cons l124367 (.cons l124371 (.cons l124373 (.cons l124375 (.cons l124379 (.cons l124381 (.cons l124383 (.cons l124386 (.cons l124387 (.cons l124390 (.cons l124391 (.cons l124394 (.cons l124395 (.cons l124398 (.cons l124399 (.cons l124400 (.cons l124402 (.cons l124403 (.cons l124404 (.cons l124405 (.cons l124406 (.cons l124407 (.cons l124408 (.cons l124410 (.cons l124411 (.cons l124412 (.cons l124413 (.cons l124414 (.cons l124415 (.cons l124425 (.cons l124445 (.cons l124447 (.cons l124457 (.cons l124476 (.nil))))))))))))))))))))))))))))))))))))))))))

end S48

end RACert.S0N3.C0
