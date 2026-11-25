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

namespace S1

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(159, 2), (176, 1), (177, 4), (179, 4), (182, 2), (183, 4), (191, 1), (192, 1), (193, 4), (195, 4), (198, 2), (199, 4), (207, 1), (208, 2), (209, 8), (211, 4), (213, 4), (214, 4), (215, 8), (223, 2), (240, 1), (241, 4), (243, 4), (246, 2), (247, 4), (255, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(159, 30434), (176, 979), (177, 868), (179, 4894), (182, 9353), (183, 15551), (191, 70546), (192, 490), (193, 2), (195, 0), (198, 164), (199, 0), (207, 17770), (208, 588), (209, 406), (211, 3523), (213, 2766), (214, 2971), (215, 7666), (223, 63107), (240, 2614), (241, 1742), (243, 6268), (246, 9556), (247, 15551), (255, 78137)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 8 perms 159 256 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 678060 = true := by decide +kernel

theorem total : OrbitSeg 8 perms (P.leaf 20) 159 256 82 678060 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S1

end RACert.S0N3.C1
