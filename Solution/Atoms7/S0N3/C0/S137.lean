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

namespace S137

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1044977, 24), (1044979, 12), (1044980, 24), (1044981, 24), (1044982, 24), (1044983, 24), (1044988, 12), (1044989, 24), (1044991, 12), (1045263, 6), (1045277, 6), (1045278, 6), (1045279, 12), (1045311, 3), (1045319, 12), (1045323, 12), (1045327, 12), (1045333, 24), (1045334, 24), (1045335, 24), (1045337, 24), (1045338, 24), (1045339, 24), (1045341, 24), (1045342, 24), (1045343, 24), (1045364, 6), (1045365, 24), (1045367, 12), (1045368, 6), (1045369, 24), (1045371, 12), (1045372, 12), (1045373, 24), (1045375, 12), (1045443, 2), (1045447, 12), (1045455, 6), (1045461, 24), (1045462, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1044977, 4230), (1044979, 7184), (1044980, 5472), (1044981, 6942), (1044982, 7086), (1044983, 9763), (1044988, 9924), (1044989, 10908), (1044991, 24314), (1045263, 872), (1045277, 912), (1045278, 800), (1045279, 912), (1045311, 912), (1045319, 4110), (1045323, 3084), (1045327, 5839), (1045333, 5125), (1045334, 3865), (1045335, 6278), (1045337, 3894), (1045338, 2898), (1045339, 5015), (1045341, 7627), (1045342, 5923), (1045343, 13627), (1045364, 3584), (1045365, 5175), (1045367, 6328), (1045368, 2932), (1045369, 4226), (1045371, 5494), (1045372, 6980), (1045373, 7727), (1045375, 13803), (1045443, 4626), (1045447, 7613), (1045455, 9068), (1045461, 9181), (1045462, 7449)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 1044977 1045463 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4445880 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1044977 1045463 665 4445880 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S137

end RACert.S0N3.C0
