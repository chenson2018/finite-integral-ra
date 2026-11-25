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

namespace S55

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(127359, 48), (127360, 48), (127361, 48), (127362, 48), (127363, 48), (127364, 48), (127365, 48), (127366, 48), (127367, 48), (127368, 48), (127369, 48), (127370, 48), (127371, 48), (127372, 48), (127373, 48), (127374, 48), (127375, 48), (127376, 48), (127377, 48), (127378, 48), (127379, 48), (127380, 48), (127381, 48), (127382, 48), (127383, 48), (127384, 48), (127385, 48), (127386, 48), (127387, 48), (127388, 48), (127389, 48), (127390, 48), (127391, 48), (127392, 48), (127393, 48), (127394, 48), (127395, 48), (127396, 48), (127397, 48), (127398, 48), (127399, 48), (127400, 48), (127401, 48), (127402, 48), (127403, 48), (127404, 48), (127405, 48), (127406, 48), (127407, 48), (127408, 48), (127409, 48), (127410, 48), (127411, 48), (127412, 48), (127413, 48), (127414, 48), (127415, 48), (127416, 48), (127417, 48), (127418, 48), (127419, 48), (127420, 48), (127421, 48), (127422, 48), (127423, 48), (127424, 48), (127425, 48), (127426, 48), (127427, 48), (127428, 48), (127429, 48), (127430, 48), (127431, 48), (127432, 48), (127433, 48), (127434, 48), (127435, 48), (127436, 48), (127437, 48), (127438, 48), (127439, 48), (127440, 48), (127441, 48), (127442, 48), (127443, 48), (127444, 48), (127445, 48), (127446, 48), (127447, 48), (127448, 48), (127449, 48), (127450, 48), (127451, 48), (127452, 48), (127453, 48), (127454, 48), (127455, 48), (127456, 48), (127457, 48), (127458, 48), (127459, 48), (127460, 48), (127461, 48), (127462, 48), (127463, 48), (127464, 48), (127465, 48), (127466, 48), (127467, 48), (127468, 48), (127469, 48), (127470, 48), (127471, 48), (127472, 48), (127473, 48), (127474, 48), (127475, 48), (127476, 48), (127477, 48), (127478, 48), (127479, 48), (127480, 48), (127481, 48), (127482, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 424, 439, 550, 602, 502, 502, 550, 602, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 602, 550, 602, 550, 602, 550, 439, 550, 0, 550, 628, 550, 0, 502, 439, 602, 602, 502, 502, 602, 602, 418, 418, 0, 0, 418, 418, 0, 0, 602, 439, 602, 602, 602, 602, 602, 602, 628, 439, 0, 0, 628, 628, 0, 0, 424, 439, 550, 0, 502, 502, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 502, 439, 0, 0, 502, 502, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(127359, 160), (127371, 20), (127375, 20), (127387, 88), (127391, 160), (127402, 16), (127403, 60), (127406, 56), (127407, 96), (127418, 38), (127419, 194), (127422, 152), (127423, 320), (127427, 4), (127431, 16), (127435, 20), (127439, 48), (127443, 64), (127445, 78), (127447, 380), (127451, 211), (127453, 398), (127455, 1015), (127458, 26), (127459, 40), (127462, 74), (127463, 164), (127466, 38), (127467, 137), (127470, 307), (127471, 617), (127472, 0), (127474, 64), (127475, 128), (127476, 124), (127477, 156), (127478, 366), (127479, 958), (127480, 0), (127482, 92)]

theorem l127359 : P.leaf 18 127359 = 160 := by decide +kernel

theorem l127371 : P.leaf 18 127371 = 20 := by decide +kernel

theorem l127375 : P.leaf 18 127375 = 20 := by decide +kernel

theorem l127387 : P.leaf 18 127387 = 88 := by decide +kernel

theorem l127391 : P.leaf 18 127391 = 160 := by decide +kernel

theorem l127402 : P.leaf 18 127402 = 16 := by decide +kernel

theorem l127403 : P.leaf 18 127403 = 60 := by decide +kernel

theorem l127406 : P.leaf 18 127406 = 56 := by decide +kernel

theorem l127407 : P.leaf 18 127407 = 96 := by decide +kernel

theorem l127418 : P.leaf 18 127418 = 38 := by decide +kernel

theorem l127419 : P.leaf 18 127419 = 194 := by decide +kernel

theorem l127422 : P.leaf 18 127422 = 152 := by decide +kernel

theorem l127423 : P.leaf 18 127423 = 320 := by decide +kernel

theorem l127427 : P.leaf 18 127427 = 4 := by decide +kernel

theorem l127431 : P.leaf 18 127431 = 16 := by decide +kernel

theorem l127435 : P.leaf 18 127435 = 20 := by decide +kernel

theorem l127439 : P.leaf 18 127439 = 48 := by decide +kernel

theorem l127443 : P.leaf 18 127443 = 64 := by decide +kernel

theorem l127445 : P.leaf 18 127445 = 78 := by decide +kernel

theorem l127447 : P.leaf 18 127447 = 380 := by decide +kernel

theorem l127451 : P.leaf 18 127451 = 211 := by decide +kernel

theorem l127453 : P.leaf 18 127453 = 398 := by decide +kernel

theorem l127455 : P.leaf 18 127455 = 1015 := by decide +kernel

theorem l127458 : P.leaf 18 127458 = 26 := by decide +kernel

theorem l127459 : P.leaf 18 127459 = 40 := by decide +kernel

theorem l127462 : P.leaf 18 127462 = 74 := by decide +kernel

theorem l127463 : P.leaf 18 127463 = 164 := by decide +kernel

theorem l127466 : P.leaf 18 127466 = 38 := by decide +kernel

theorem l127467 : P.leaf 18 127467 = 137 := by decide +kernel

theorem l127470 : P.leaf 18 127470 = 307 := by decide +kernel

theorem l127471 : P.leaf 18 127471 = 617 := by decide +kernel

theorem l127472 : P.leaf 18 127472 = 0 := by decide +kernel

theorem l127474 : P.leaf 18 127474 = 64 := by decide +kernel

theorem l127475 : P.leaf 18 127475 = 128 := by decide +kernel

theorem l127476 : P.leaf 18 127476 = 124 := by decide +kernel

theorem l127477 : P.leaf 18 127477 = 156 := by decide +kernel

theorem l127478 : P.leaf 18 127478 = 366 := by decide +kernel

theorem l127479 : P.leaf 18 127479 = 958 := by decide +kernel

theorem l127480 : P.leaf 18 127480 = 0 := by decide +kernel

theorem l127482 : P.leaf 18 127482 = 92 := by decide +kernel

theorem segOK : checkSeg 20 perms 127359 127483 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 331440 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 127359 127483 5952 331440 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l127359 (.cons l127371 (.cons l127375 (.cons l127387 (.cons l127391 (.cons l127402 (.cons l127403 (.cons l127406 (.cons l127407 (.cons l127418 (.cons l127419 (.cons l127422 (.cons l127423 (.cons l127427 (.cons l127431 (.cons l127435 (.cons l127439 (.cons l127443 (.cons l127445 (.cons l127447 (.cons l127451 (.cons l127453 (.cons l127455 (.cons l127458 (.cons l127459 (.cons l127462 (.cons l127463 (.cons l127466 (.cons l127467 (.cons l127470 (.cons l127471 (.cons l127472 (.cons l127474 (.cons l127475 (.cons l127476 (.cons l127477 (.cons l127478 (.cons l127479 (.cons l127480 (.cons l127482 (.nil))))))))))))))))))))))))))))))))))))))))))

end S55

end RACert.S0N3.C0
