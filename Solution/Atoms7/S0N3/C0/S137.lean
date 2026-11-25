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

theorem l1044977 : P.leaf 18 1044977 = 4230 := by decide +kernel

theorem l1044979 : P.leaf 18 1044979 = 7184 := by decide +kernel

theorem l1044980 : P.leaf 18 1044980 = 5472 := by decide +kernel

theorem l1044981 : P.leaf 18 1044981 = 6942 := by decide +kernel

theorem l1044982 : P.leaf 18 1044982 = 7086 := by decide +kernel

theorem l1044983 : P.leaf 18 1044983 = 9763 := by decide +kernel

theorem l1044988 : P.leaf 18 1044988 = 9924 := by decide +kernel

theorem l1044989 : P.leaf 18 1044989 = 10908 := by decide +kernel

theorem l1044991 : P.leaf 18 1044991 = 24314 := by decide +kernel

theorem l1045263 : P.leaf 18 1045263 = 872 := by decide +kernel

theorem l1045277 : P.leaf 18 1045277 = 912 := by decide +kernel

theorem l1045278 : P.leaf 18 1045278 = 800 := by decide +kernel

theorem l1045279 : P.leaf 18 1045279 = 912 := by decide +kernel

theorem l1045311 : P.leaf 18 1045311 = 912 := by decide +kernel

theorem l1045319 : P.leaf 18 1045319 = 4110 := by decide +kernel

theorem l1045323 : P.leaf 18 1045323 = 3084 := by decide +kernel

theorem l1045327 : P.leaf 18 1045327 = 5839 := by decide +kernel

theorem l1045333 : P.leaf 18 1045333 = 5125 := by decide +kernel

theorem l1045334 : P.leaf 18 1045334 = 3865 := by decide +kernel

theorem l1045335 : P.leaf 18 1045335 = 6278 := by decide +kernel

theorem l1045337 : P.leaf 18 1045337 = 3894 := by decide +kernel

theorem l1045338 : P.leaf 18 1045338 = 2898 := by decide +kernel

theorem l1045339 : P.leaf 18 1045339 = 5015 := by decide +kernel

theorem l1045341 : P.leaf 18 1045341 = 7627 := by decide +kernel

theorem l1045342 : P.leaf 18 1045342 = 5923 := by decide +kernel

theorem l1045343 : P.leaf 18 1045343 = 13627 := by decide +kernel

theorem l1045364 : P.leaf 18 1045364 = 3584 := by decide +kernel

theorem l1045365 : P.leaf 18 1045365 = 5175 := by decide +kernel

theorem l1045367 : P.leaf 18 1045367 = 6328 := by decide +kernel

theorem l1045368 : P.leaf 18 1045368 = 2932 := by decide +kernel

theorem l1045369 : P.leaf 18 1045369 = 4226 := by decide +kernel

theorem l1045371 : P.leaf 18 1045371 = 5494 := by decide +kernel

theorem l1045372 : P.leaf 18 1045372 = 6980 := by decide +kernel

theorem l1045373 : P.leaf 18 1045373 = 7727 := by decide +kernel

theorem l1045375 : P.leaf 18 1045375 = 13803 := by decide +kernel

theorem l1045443 : P.leaf 18 1045443 = 4626 := by decide +kernel

theorem l1045447 : P.leaf 18 1045447 = 7613 := by decide +kernel

theorem l1045455 : P.leaf 18 1045455 = 9068 := by decide +kernel

theorem l1045461 : P.leaf 18 1045461 = 9181 := by decide +kernel

theorem l1045462 : P.leaf 18 1045462 = 7449 := by decide +kernel

theorem segOK : checkSeg 20 perms 1044977 1045463 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4445880 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1044977 1045463 665 4445880 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1044977 (.cons l1044979 (.cons l1044980 (.cons l1044981 (.cons l1044982 (.cons l1044983 (.cons l1044988 (.cons l1044989 (.cons l1044991 (.cons l1045263 (.cons l1045277 (.cons l1045278 (.cons l1045279 (.cons l1045311 (.cons l1045319 (.cons l1045323 (.cons l1045327 (.cons l1045333 (.cons l1045334 (.cons l1045335 (.cons l1045337 (.cons l1045338 (.cons l1045339 (.cons l1045341 (.cons l1045342 (.cons l1045343 (.cons l1045364 (.cons l1045365 (.cons l1045367 (.cons l1045368 (.cons l1045369 (.cons l1045371 (.cons l1045372 (.cons l1045373 (.cons l1045375 (.cons l1045443 (.cons l1045447 (.cons l1045455 (.cons l1045461 (.cons l1045462 (.nil))))))))))))))))))))))))))))))))))))))))))

end S137

end RACert.S0N3.C0
