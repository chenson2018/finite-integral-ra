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

namespace S124

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(517113, 24), (517114, 24), (517115, 24), (517116, 12), (517117, 24), (517118, 24), (517119, 24), (517461, 24), (517462, 12), (517463, 24), (517465, 12), (517466, 24), (517467, 24), (517469, 24), (517470, 24), (517471, 24), (517477, 12), (517479, 24), (517481, 24), (517482, 24), (517483, 24), (517485, 24), (517486, 24), (517487, 24), (517495, 12), (517497, 24), (517498, 24), (517499, 24), (517501, 24), (517502, 24), (517503, 24), (517525, 12), (517526, 24), (517527, 24), (517530, 24), (517531, 24), (517533, 24), (517534, 24), (517535, 24), (517541, 24), (517543, 24), (517546, 8), (517547, 24), (517549, 24), (517550, 24), (517551, 24), (517557, 24), (517558, 24), (517559, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 440, 0, 0, 0, 0, 0, 418, 440, 440, 418, 0, 0, 0, 0, 440, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(517113, 596), (517114, 1744), (517115, 2000), (517116, 816), (517117, 1246), (517118, 3736), (517119, 5394), (517461, 554), (517462, 541), (517463, 1539), (517465, 130), (517469, 689), (517470, 705), (517471, 1539), (517477, 23), (517479, 829), (517486, 806), (517487, 988), (517495, 2570), (517497, 266), (517501, 941), (517502, 1823), (517503, 2612), (517525, 1088), (517526, 1010), (517527, 2432), (517530, 822), (517531, 1660), (517533, 1484), (517534, 1812), (517535, 3580), (517541, 139), (517543, 1153), (517546, 918), (517547, 1203), (517550, 2085), (517551, 2175), (517557, 1312), (517558, 2793), (517559, 4071)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 517113 517563 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1407072 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 517113 517563 1088 1407072 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S124

end RACert.S0N3.C0
