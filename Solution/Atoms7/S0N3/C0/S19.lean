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

namespace S19

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(91094, 48), (91095, 48), (91097, 48), (91098, 48), (91099, 48), (91101, 48), (91102, 48), (91103, 48), (91109, 48), (91110, 48), (91111, 48), (91113, 48), (91114, 48), (91115, 48), (91117, 48), (91118, 48), (91119, 48), (91125, 48), (91126, 48), (91127, 48), (91129, 48), (91130, 48), (91131, 48), (91132, 24), (91133, 48), (91134, 48), (91135, 48), (91477, 48), (91478, 24), (91479, 48), (91481, 24), (91482, 48), (91483, 48), (91485, 48), (91486, 48), (91487, 48), (91493, 24), (91495, 48), (91497, 48), (91498, 48), (91499, 48), (91501, 48), (91502, 48), (91503, 48), (91511, 24), (91513, 48), (91514, 48), (91515, 48), (91517, 48), (91518, 48), (91519, 48), (91541, 24), (91542, 48), (91543, 48), (91546, 48), (91547, 48), (91549, 48), (91550, 48), (91551, 48), (91557, 48), (91559, 48), (91562, 16), (91563, 48), (91565, 48), (91566, 48), (91567, 48), (91573, 48), (91574, 48), (91575, 48), (91579, 48), (91581, 48), (91582, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 439, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 684, 684, 684, 439, 438, 440, 684, 684, 684, 432, 684, 418, 438, 440, 418, 684, 684, 684, 439, 438, 440, 684, 684, 684, 0, 427, 0, 0, 0, 0, 0, 0, 432, 0, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(91094, 35), (91095, 70), (91098, 20), (91099, 24), (91101, 60), (91102, 138), (91103, 110), (91110, 21), (91111, 28), (91114, 12), (91115, 16), (91118, 72), (91119, 86), (91125, 80), (91126, 136), (91127, 192), (91130, 44), (91131, 68), (91132, 48), (91133, 128), (91134, 248), (91135, 352), (91541, 7), (91543, 20), (91546, 4), (91547, 32), (91549, 50), (91550, 14), (91551, 78), (91559, 8), (91562, 18), (91563, 32), (91566, 49), (91567, 62), (91573, 23), (91574, 32), (91575, 130), (91579, 126), (91581, 84), (91582, 186)]

theorem l91094 : P.leaf 18 91094 = 35 := by decide +kernel

theorem l91095 : P.leaf 18 91095 = 70 := by decide +kernel

theorem l91098 : P.leaf 18 91098 = 20 := by decide +kernel

theorem l91099 : P.leaf 18 91099 = 24 := by decide +kernel

theorem l91101 : P.leaf 18 91101 = 60 := by decide +kernel

theorem l91102 : P.leaf 18 91102 = 138 := by decide +kernel

theorem l91103 : P.leaf 18 91103 = 110 := by decide +kernel

theorem l91110 : P.leaf 18 91110 = 21 := by decide +kernel

theorem l91111 : P.leaf 18 91111 = 28 := by decide +kernel

theorem l91114 : P.leaf 18 91114 = 12 := by decide +kernel

theorem l91115 : P.leaf 18 91115 = 16 := by decide +kernel

theorem l91118 : P.leaf 18 91118 = 72 := by decide +kernel

theorem l91119 : P.leaf 18 91119 = 86 := by decide +kernel

theorem l91125 : P.leaf 18 91125 = 80 := by decide +kernel

theorem l91126 : P.leaf 18 91126 = 136 := by decide +kernel

theorem l91127 : P.leaf 18 91127 = 192 := by decide +kernel

theorem l91130 : P.leaf 18 91130 = 44 := by decide +kernel

theorem l91131 : P.leaf 18 91131 = 68 := by decide +kernel

theorem l91132 : P.leaf 18 91132 = 48 := by decide +kernel

theorem l91133 : P.leaf 18 91133 = 128 := by decide +kernel

theorem l91134 : P.leaf 18 91134 = 248 := by decide +kernel

theorem l91135 : P.leaf 18 91135 = 352 := by decide +kernel

theorem l91541 : P.leaf 18 91541 = 7 := by decide +kernel

theorem l91543 : P.leaf 18 91543 = 20 := by decide +kernel

theorem l91546 : P.leaf 18 91546 = 4 := by decide +kernel

theorem l91547 : P.leaf 18 91547 = 32 := by decide +kernel

theorem l91549 : P.leaf 18 91549 = 50 := by decide +kernel

theorem l91550 : P.leaf 18 91550 = 14 := by decide +kernel

theorem l91551 : P.leaf 18 91551 = 78 := by decide +kernel

theorem l91559 : P.leaf 18 91559 = 8 := by decide +kernel

theorem l91562 : P.leaf 18 91562 = 18 := by decide +kernel

theorem l91563 : P.leaf 18 91563 = 32 := by decide +kernel

theorem l91566 : P.leaf 18 91566 = 49 := by decide +kernel

theorem l91567 : P.leaf 18 91567 = 62 := by decide +kernel

theorem l91573 : P.leaf 18 91573 = 23 := by decide +kernel

theorem l91574 : P.leaf 18 91574 = 32 := by decide +kernel

theorem l91575 : P.leaf 18 91575 = 130 := by decide +kernel

theorem l91579 : P.leaf 18 91579 = 126 := by decide +kernel

theorem l91581 : P.leaf 18 91581 = 84 := by decide +kernel

theorem l91582 : P.leaf 18 91582 = 186 := by decide +kernel

theorem segOK : checkSeg 20 perms 91094 91583 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 139368 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 91094 91583 3280 139368 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l91094 (.cons l91095 (.cons l91098 (.cons l91099 (.cons l91101 (.cons l91102 (.cons l91103 (.cons l91110 (.cons l91111 (.cons l91114 (.cons l91115 (.cons l91118 (.cons l91119 (.cons l91125 (.cons l91126 (.cons l91127 (.cons l91130 (.cons l91131 (.cons l91132 (.cons l91133 (.cons l91134 (.cons l91135 (.cons l91541 (.cons l91543 (.cons l91546 (.cons l91547 (.cons l91549 (.cons l91550 (.cons l91551 (.cons l91559 (.cons l91562 (.cons l91563 (.cons l91566 (.cons l91567 (.cons l91573 (.cons l91574 (.cons l91575 (.cons l91579 (.cons l91581 (.cons l91582 (.nil))))))))))))))))))))))))))))))))))))))))))

end S19

end RACert.S0N3.C0
