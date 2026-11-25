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

namespace S112

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(456308, 48), (456309, 48), (456310, 48), (456311, 48), (456312, 48), (456313, 48), (456314, 48), (456315, 48), (456316, 48), (456317, 48), (456318, 48), (456319, 48), (456432, 12), (456433, 48), (456435, 24), (456437, 24), (456438, 24), (456439, 48), (456447, 12), (456448, 24), (456449, 48), (456451, 24), (456452, 48), (456453, 48), (456454, 48), (456455, 48), (456460, 24), (456461, 48), (456463, 24), (456464, 48), (456465, 48), (456466, 48), (456467, 48), (456468, 48), (456469, 48), (456470, 48), (456471, 48), (456472, 48), (456473, 48), (456474, 48), (456475, 48), (456476, 48), (456477, 48), (456478, 48), (456479, 48), (456496, 24), (456497, 48), (456499, 24), (456500, 48), (456501, 48), (456502, 48), (456503, 48), (456508, 24), (456509, 48), (456511, 24), (456512, 48), (456513, 48), (456514, 48), (456515, 48), (456516, 48), (456517, 48), (456518, 48), (456519, 48), (456520, 48), (456521, 48), (456522, 48), (456523, 48), (456524, 48), (456525, 48), (456526, 48), (456527, 48), (456528, 48), (456529, 48), (456530, 48), (456531, 48), (456532, 48), (456533, 48), (456534, 48), (456535, 48), (456536, 48), (456537, 48), (456538, 48), (456539, 48), (456540, 48), (456541, 48), (456542, 48), (456543, 48), (456544, 48), (456545, 48), (456546, 48), (456547, 48), (456548, 48), (456549, 48), (456550, 48), (456551, 48), (456552, 48), (456553, 48), (456554, 48), (456555, 48), (456556, 48), (456557, 48), (456558, 48), (456559, 48), (456560, 48), (456561, 48), (456562, 48), (456563, 48), (456564, 48), (456565, 48), (456566, 48), (456567, 48), (456568, 48), (456569, 48), (456570, 48), (456571, 48), (456572, 48), (456573, 48), (456574, 48), (456575, 48), (456640, 24), (456641, 48), (456643, 24), (456644, 48), (456645, 48), (456646, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 439, 602, 502, 502, 431, 602, 502, 502, 0, 434, 440, 431, 602, 550, 602, 431, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 440, 602, 602, 602, 602, 602, 0, 0, 0, 418, 439, 550, 650, 502, 502, 550, 0, 502, 439, 550, 650, 502, 502, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 502, 439, 650, 650, 502, 502, 0, 0, 502, 439, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 418, 502, 0, 502, 502, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(456308, 40), (456309, 323), (456310, 162), (456311, 927), (456316, 310), (456317, 910), (456318, 1019), (456319, 2457), (456432, 25), (456433, 160), (456435, 1056), (456437, 1312), (456438, 513), (456439, 3325), (456447, 9392), (456463, 484), (456477, 386), (456479, 566), (456508, 256), (456509, 605), (456511, 965), (456519, 1113), (456527, 1850), (456533, 884), (456535, 1780), (456541, 1796), (456543, 3060), (456550, 873), (456551, 1779), (456558, 1788), (456559, 3061), (456564, 248), (456565, 1387), (456566, 1404), (456567, 3556), (456572, 1156), (456573, 2955), (456574, 2935), (456575, 7098), (456643, 1164)]

theorem l456308 : P.leaf 18 456308 = 40 := by decide +kernel

theorem l456309 : P.leaf 18 456309 = 323 := by decide +kernel

theorem l456310 : P.leaf 18 456310 = 162 := by decide +kernel

theorem l456311 : P.leaf 18 456311 = 927 := by decide +kernel

theorem l456316 : P.leaf 18 456316 = 310 := by decide +kernel

theorem l456317 : P.leaf 18 456317 = 910 := by decide +kernel

theorem l456318 : P.leaf 18 456318 = 1019 := by decide +kernel

theorem l456319 : P.leaf 18 456319 = 2457 := by decide +kernel

theorem l456432 : P.leaf 18 456432 = 25 := by decide +kernel

theorem l456433 : P.leaf 18 456433 = 160 := by decide +kernel

theorem l456435 : P.leaf 18 456435 = 1056 := by decide +kernel

theorem l456437 : P.leaf 18 456437 = 1312 := by decide +kernel

theorem l456438 : P.leaf 18 456438 = 513 := by decide +kernel

theorem l456439 : P.leaf 18 456439 = 3325 := by decide +kernel

theorem l456447 : P.leaf 18 456447 = 9392 := by decide +kernel

theorem l456463 : P.leaf 18 456463 = 484 := by decide +kernel

theorem l456477 : P.leaf 18 456477 = 386 := by decide +kernel

theorem l456479 : P.leaf 18 456479 = 566 := by decide +kernel

theorem l456508 : P.leaf 18 456508 = 256 := by decide +kernel

theorem l456509 : P.leaf 18 456509 = 605 := by decide +kernel

theorem l456511 : P.leaf 18 456511 = 965 := by decide +kernel

theorem l456519 : P.leaf 18 456519 = 1113 := by decide +kernel

theorem l456527 : P.leaf 18 456527 = 1850 := by decide +kernel

theorem l456533 : P.leaf 18 456533 = 884 := by decide +kernel

theorem l456535 : P.leaf 18 456535 = 1780 := by decide +kernel

theorem l456541 : P.leaf 18 456541 = 1796 := by decide +kernel

theorem l456543 : P.leaf 18 456543 = 3060 := by decide +kernel

theorem l456550 : P.leaf 18 456550 = 873 := by decide +kernel

theorem l456551 : P.leaf 18 456551 = 1779 := by decide +kernel

theorem l456558 : P.leaf 18 456558 = 1788 := by decide +kernel

theorem l456559 : P.leaf 18 456559 = 3061 := by decide +kernel

theorem l456564 : P.leaf 18 456564 = 248 := by decide +kernel

theorem l456565 : P.leaf 18 456565 = 1387 := by decide +kernel

theorem l456566 : P.leaf 18 456566 = 1404 := by decide +kernel

theorem l456567 : P.leaf 18 456567 = 3556 := by decide +kernel

theorem l456572 : P.leaf 18 456572 = 1156 := by decide +kernel

theorem l456573 : P.leaf 18 456573 = 2955 := by decide +kernel

theorem l456574 : P.leaf 18 456574 = 2935 := by decide +kernel

theorem l456575 : P.leaf 18 456575 = 7098 := by decide +kernel

theorem l456643 : P.leaf 18 456643 = 1164 := by decide +kernel

theorem segOK : checkSeg 20 perms 456308 456647 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2646828 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 456308 456647 5616 2646828 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l456308 (.cons l456309 (.cons l456310 (.cons l456311 (.cons l456316 (.cons l456317 (.cons l456318 (.cons l456319 (.cons l456432 (.cons l456433 (.cons l456435 (.cons l456437 (.cons l456438 (.cons l456439 (.cons l456447 (.cons l456463 (.cons l456477 (.cons l456479 (.cons l456508 (.cons l456509 (.cons l456511 (.cons l456519 (.cons l456527 (.cons l456533 (.cons l456535 (.cons l456541 (.cons l456543 (.cons l456550 (.cons l456551 (.cons l456558 (.cons l456559 (.cons l456564 (.cons l456565 (.cons l456566 (.cons l456567 (.cons l456572 (.cons l456573 (.cons l456574 (.cons l456575 (.cons l456643 (.nil))))))))))))))))))))))))))))))))))))))))))

end S112

end RACert.S0N3.C0
