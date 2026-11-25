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

namespace S58

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(128381, 48), (128382, 48), (128383, 48), (128384, 48), (128385, 48), (128386, 48), (128387, 48), (128388, 48), (128389, 48), (128390, 48), (128391, 48), (128392, 48), (128393, 48), (128394, 48), (128395, 48), (128396, 48), (128397, 48), (128398, 48), (128399, 48), (128400, 48), (128401, 48), (128402, 48), (128403, 48), (128404, 48), (128405, 48), (128406, 48), (128407, 48), (128408, 48), (128409, 48), (128410, 48), (128411, 48), (128412, 48), (128413, 48), (128414, 48), (128415, 48), (128416, 48), (128417, 48), (128418, 48), (128419, 48), (128420, 48), (128421, 48), (128422, 48), (128423, 48), (128424, 48), (128425, 48), (128426, 48), (128427, 48), (128428, 48), (128429, 48), (128430, 48), (128431, 48), (128432, 48), (128433, 48), (128434, 48), (128435, 48), (128436, 48), (128437, 48), (128438, 48), (128439, 48), (128440, 48), (128441, 48), (128442, 48), (128443, 48), (128444, 48), (128445, 48), (128446, 48), (128447, 48), (128448, 48), (128449, 48), (128450, 48), (128451, 48), (128452, 48), (128453, 48), (128454, 48), (128455, 48), (128456, 48), (128457, 48), (128458, 48), (128459, 48), (128460, 48), (128461, 48), (128462, 48), (128463, 48), (128464, 48), (128465, 48), (128466, 48), (128467, 48), (128468, 48), (128469, 48), (128470, 48), (128471, 48), (128472, 48), (128473, 48), (128474, 48), (128475, 48), (128476, 48), (128477, 48), (128478, 48), (128479, 48), (128480, 48), (128481, 48), (128482, 48), (128483, 48), (128484, 48), (128485, 48), (128486, 48), (128487, 48), (128488, 48), (128489, 48), (128490, 48), (128491, 48), (128492, 48), (128493, 48), (128494, 48), (128495, 48), (128496, 48), (128497, 48), (128498, 48), (128499, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 424, 439, 550, 602, 432, 432, 550, 602, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 602, 550, 602, 550, 602, 550, 439, 550, 0, 550, 0, 550, 0, 502, 439, 602, 602, 432, 432, 602, 602, 418, 418, 0, 0, 418, 418, 0, 0, 602, 439, 602, 602, 602, 602, 602, 602, 0, 439, 0, 0, 0, 0, 0, 0, 424, 439, 550, 0, 432, 432, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 502, 439, 0, 0, 432, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(128381, 390), (128382, 456), (128383, 1156), (128395, 100), (128399, 110), (128411, 540), (128413, 428), (128415, 1171), (128426, 200), (128427, 469), (128430, 444), (128431, 866), (128440, 0), (128442, 312), (128443, 737), (128444, 168), (128445, 574), (128446, 800), (128447, 1868), (128451, 32), (128455, 100), (128459, 120), (128463, 172), (128467, 216), (128469, 298), (128471, 948), (128475, 726), (128477, 607), (128479, 2078), (128482, 104), (128483, 176), (128486, 280), (128487, 620), (128490, 316), (128491, 618), (128494, 800), (128495, 1652), (128496, 0), (128498, 120), (128499, 240)]

theorem l128381 : P.leaf 18 128381 = 390 := by decide +kernel

theorem l128382 : P.leaf 18 128382 = 456 := by decide +kernel

theorem l128383 : P.leaf 18 128383 = 1156 := by decide +kernel

theorem l128395 : P.leaf 18 128395 = 100 := by decide +kernel

theorem l128399 : P.leaf 18 128399 = 110 := by decide +kernel

theorem l128411 : P.leaf 18 128411 = 540 := by decide +kernel

theorem l128413 : P.leaf 18 128413 = 428 := by decide +kernel

theorem l128415 : P.leaf 18 128415 = 1171 := by decide +kernel

theorem l128426 : P.leaf 18 128426 = 200 := by decide +kernel

theorem l128427 : P.leaf 18 128427 = 469 := by decide +kernel

theorem l128430 : P.leaf 18 128430 = 444 := by decide +kernel

theorem l128431 : P.leaf 18 128431 = 866 := by decide +kernel

theorem l128440 : P.leaf 18 128440 = 0 := by decide +kernel

theorem l128442 : P.leaf 18 128442 = 312 := by decide +kernel

theorem l128443 : P.leaf 18 128443 = 737 := by decide +kernel

theorem l128444 : P.leaf 18 128444 = 168 := by decide +kernel

theorem l128445 : P.leaf 18 128445 = 574 := by decide +kernel

theorem l128446 : P.leaf 18 128446 = 800 := by decide +kernel

theorem l128447 : P.leaf 18 128447 = 1868 := by decide +kernel

theorem l128451 : P.leaf 18 128451 = 32 := by decide +kernel

theorem l128455 : P.leaf 18 128455 = 100 := by decide +kernel

theorem l128459 : P.leaf 18 128459 = 120 := by decide +kernel

theorem l128463 : P.leaf 18 128463 = 172 := by decide +kernel

theorem l128467 : P.leaf 18 128467 = 216 := by decide +kernel

theorem l128469 : P.leaf 18 128469 = 298 := by decide +kernel

theorem l128471 : P.leaf 18 128471 = 948 := by decide +kernel

theorem l128475 : P.leaf 18 128475 = 726 := by decide +kernel

theorem l128477 : P.leaf 18 128477 = 607 := by decide +kernel

theorem l128479 : P.leaf 18 128479 = 2078 := by decide +kernel

theorem l128482 : P.leaf 18 128482 = 104 := by decide +kernel

theorem l128483 : P.leaf 18 128483 = 176 := by decide +kernel

theorem l128486 : P.leaf 18 128486 = 280 := by decide +kernel

theorem l128487 : P.leaf 18 128487 = 620 := by decide +kernel

theorem l128490 : P.leaf 18 128490 = 316 := by decide +kernel

theorem l128491 : P.leaf 18 128491 = 618 := by decide +kernel

theorem l128494 : P.leaf 18 128494 = 800 := by decide +kernel

theorem l128495 : P.leaf 18 128495 = 1652 := by decide +kernel

theorem l128496 : P.leaf 18 128496 = 0 := by decide +kernel

theorem l128498 : P.leaf 18 128498 = 120 := by decide +kernel

theorem l128499 : P.leaf 18 128499 = 240 := by decide +kernel

theorem segOK : checkSeg 20 perms 128381 128500 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1008576 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 128381 128500 5712 1008576 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l128381 (.cons l128382 (.cons l128383 (.cons l128395 (.cons l128399 (.cons l128411 (.cons l128413 (.cons l128415 (.cons l128426 (.cons l128427 (.cons l128430 (.cons l128431 (.cons l128440 (.cons l128442 (.cons l128443 (.cons l128444 (.cons l128445 (.cons l128446 (.cons l128447 (.cons l128451 (.cons l128455 (.cons l128459 (.cons l128463 (.cons l128467 (.cons l128469 (.cons l128471 (.cons l128475 (.cons l128477 (.cons l128479 (.cons l128482 (.cons l128483 (.cons l128486 (.cons l128487 (.cons l128490 (.cons l128491 (.cons l128494 (.cons l128495 (.cons l128496 (.cons l128498 (.cons l128499 (.nil))))))))))))))))))))))))))))))))))))))))))

end S58

end RACert.S0N3.C0
