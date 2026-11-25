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

namespace S138

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1045463, 24), (1045469, 12), (1045470, 12), (1045471, 12), (1045493, 24), (1045495, 12), (1045500, 3), (1045501, 12), (1045503, 6), (1045845, 8), (1045846, 12), (1045847, 24), (1045849, 12), (1045850, 24), (1045851, 24), (1045853, 24), (1045854, 24), (1045855, 24), (1045879, 12), (1045881, 24), (1045882, 24), (1045883, 24), (1045885, 24), (1045886, 24), (1045887, 24), (1046005, 24), (1046007, 24), (1046015, 6), (1046106, 4), (1046107, 24), (1046111, 12), (1046121, 4), (1046123, 24), (1046127, 12), (1046139, 12), (1046141, 24), (1046142, 24), (1046143, 24), (1046261, 12), (1046262, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1045463, 11744), (1045469, 12665), (1045470, 10705), (1045471, 26854), (1045493, 9369), (1045495, 11950), (1045500, 11624), (1045501, 13021), (1045503, 27446), (1045845, 7141), (1045846, 5420), (1045847, 9622), (1045849, 4677), (1045850, 3139), (1045851, 7084), (1045853, 9875), (1045854, 7579), (1045855, 18457), (1045879, 13783), (1045881, 7339), (1045882, 7930), (1045883, 11761), (1045885, 13398), (1045886, 13097), (1045887, 27906), (1046005, 12863), (1046007, 16991), (1046015, 33418), (1046106, 2840), (1046107, 6120), (1046111, 15944), (1046121, 1883), (1046123, 5441), (1046127, 16502), (1046139, 10035), (1046141, 11196), (1046142, 10963), (1046143, 25478), (1046261, 10479), (1046262, 9887)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 1045463 1046263 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 8355588 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1045463 1046263 691 8355588 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S138

end RACert.S0N3.C0
