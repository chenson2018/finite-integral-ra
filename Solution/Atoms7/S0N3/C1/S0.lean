/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 4), (7, 4), (15, 1), (16, 2), (17, 4), (19, 2), (20, 4), (21, 8), (23, 4), (28, 2), (29, 4), (31, 2), (48, 1), (49, 4), (51, 2), (53, 4), (55, 4), (63, 1)]

/-- Evidence: `0` for a leaf evaluated below, `i + 1` for a leaf killed by the `i`-th quadruple. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 618), (1, 584), (3, 1473), (5, 624), (7, 1064), (15, 2974), (16, 2214), (17, 3202), (19, 13023), (20, 4009), (21, 7803), (23, 24268), (28, 24926), (29, 34688), (31, 102122), (48, 5340), (49, 9047), (51, 42522), (53, 18817), (55, 69094), (63, 258125)]

theorem leavesOK0 : P.checkLeavesR 22 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem evOK : P.checkEvR 22 qmFlat seg ev live 0 1363629 = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf 22) 0 64 64 1363629 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEvR_sum check rows flatOK evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S0N3.C1
