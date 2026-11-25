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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 91094 91583 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 139368 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 91094 91583 3280 139368 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S19

end RACert.S0N3.C0
