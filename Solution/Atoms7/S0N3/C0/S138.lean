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

theorem l1045463 : P.leaf 18 1045463 = 11744 := by decide +kernel

theorem l1045469 : P.leaf 18 1045469 = 12665 := by decide +kernel

theorem l1045470 : P.leaf 18 1045470 = 10705 := by decide +kernel

theorem l1045471 : P.leaf 18 1045471 = 26854 := by decide +kernel

theorem l1045493 : P.leaf 18 1045493 = 9369 := by decide +kernel

theorem l1045495 : P.leaf 18 1045495 = 11950 := by decide +kernel

theorem l1045500 : P.leaf 18 1045500 = 11624 := by decide +kernel

theorem l1045501 : P.leaf 18 1045501 = 13021 := by decide +kernel

theorem l1045503 : P.leaf 18 1045503 = 27446 := by decide +kernel

theorem l1045845 : P.leaf 18 1045845 = 7141 := by decide +kernel

theorem l1045846 : P.leaf 18 1045846 = 5420 := by decide +kernel

theorem l1045847 : P.leaf 18 1045847 = 9622 := by decide +kernel

theorem l1045849 : P.leaf 18 1045849 = 4677 := by decide +kernel

theorem l1045850 : P.leaf 18 1045850 = 3139 := by decide +kernel

theorem l1045851 : P.leaf 18 1045851 = 7084 := by decide +kernel

theorem l1045853 : P.leaf 18 1045853 = 9875 := by decide +kernel

theorem l1045854 : P.leaf 18 1045854 = 7579 := by decide +kernel

theorem l1045855 : P.leaf 18 1045855 = 18457 := by decide +kernel

theorem l1045879 : P.leaf 18 1045879 = 13783 := by decide +kernel

theorem l1045881 : P.leaf 18 1045881 = 7339 := by decide +kernel

theorem l1045882 : P.leaf 18 1045882 = 7930 := by decide +kernel

theorem l1045883 : P.leaf 18 1045883 = 11761 := by decide +kernel

theorem l1045885 : P.leaf 18 1045885 = 13398 := by decide +kernel

theorem l1045886 : P.leaf 18 1045886 = 13097 := by decide +kernel

theorem l1045887 : P.leaf 18 1045887 = 27906 := by decide +kernel

theorem l1046005 : P.leaf 18 1046005 = 12863 := by decide +kernel

theorem l1046007 : P.leaf 18 1046007 = 16991 := by decide +kernel

theorem l1046015 : P.leaf 18 1046015 = 33418 := by decide +kernel

theorem l1046106 : P.leaf 18 1046106 = 2840 := by decide +kernel

theorem l1046107 : P.leaf 18 1046107 = 6120 := by decide +kernel

theorem l1046111 : P.leaf 18 1046111 = 15944 := by decide +kernel

theorem l1046121 : P.leaf 18 1046121 = 1883 := by decide +kernel

theorem l1046123 : P.leaf 18 1046123 = 5441 := by decide +kernel

theorem l1046127 : P.leaf 18 1046127 = 16502 := by decide +kernel

theorem l1046139 : P.leaf 18 1046139 = 10035 := by decide +kernel

theorem l1046141 : P.leaf 18 1046141 = 11196 := by decide +kernel

theorem l1046142 : P.leaf 18 1046142 = 10963 := by decide +kernel

theorem l1046143 : P.leaf 18 1046143 = 25478 := by decide +kernel

theorem l1046261 : P.leaf 18 1046261 = 10479 := by decide +kernel

theorem l1046262 : P.leaf 18 1046262 = 9887 := by decide +kernel

theorem segOK : checkSeg 20 perms 1045463 1046263 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 8355588 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1045463 1046263 691 8355588 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1045463 (.cons l1045469 (.cons l1045470 (.cons l1045471 (.cons l1045493 (.cons l1045495 (.cons l1045500 (.cons l1045501 (.cons l1045503 (.cons l1045845 (.cons l1045846 (.cons l1045847 (.cons l1045849 (.cons l1045850 (.cons l1045851 (.cons l1045853 (.cons l1045854 (.cons l1045855 (.cons l1045879 (.cons l1045881 (.cons l1045882 (.cons l1045883 (.cons l1045885 (.cons l1045886 (.cons l1045887 (.cons l1046005 (.cons l1046007 (.cons l1046015 (.cons l1046106 (.cons l1046107 (.cons l1046111 (.cons l1046121 (.cons l1046123 (.cons l1046127 (.cons l1046139 (.cons l1046141 (.cons l1046142 (.cons l1046143 (.cons l1046261 (.cons l1046262 (.nil))))))))))))))))))))))))))))))))))))))))))

end S138

end RACert.S0N3.C0
