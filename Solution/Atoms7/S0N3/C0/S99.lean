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

namespace S99

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(431062, 48), (431063, 48), (431069, 24), (431070, 24), (431071, 24), (431093, 48), (431095, 24), (431100, 6), (431101, 24), (431103, 12), (431445, 16), (431446, 24), (431447, 48), (431449, 24), (431450, 48), (431451, 48), (431453, 48), (431454, 48), (431455, 48), (431479, 24), (431481, 48), (431482, 48), (431483, 48), (431485, 48), (431486, 48), (431487, 48), (431605, 48), (431607, 48), (431615, 12), (431706, 8), (431707, 48), (431711, 24), (431721, 8), (431723, 48), (431727, 24), (431739, 24), (431741, 48), (431742, 48), (431743, 48), (431861, 24), (431862, 24), (431863, 48), (431871, 12), (431967, 48), (431983, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 684, 0, 0, 684, 0, 684, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(431062, 211), (431063, 1355), (431069, 1466), (431070, 801), (431071, 2842), (431093, 892), (431095, 2328), (431100, 1376), (431101, 1991), (431103, 5788), (431445, 51), (431446, 7), (431447, 240), (431449, 4), (431451, 26), (431453, 234), (431454, 65), (431455, 538), (431479, 788), (431481, 60), (431482, 51), (431483, 262), (431485, 813), (431486, 745), (431487, 1528), (431605, 796), (431607, 2123), (431615, 4840), (431711, 230), (431721, 0), (431727, 242), (431741, 341), (431742, 323), (431743, 1077), (431861, 336), (431862, 106), (431863, 1240), (431871, 4716), (431967, 1469), (431983, 1600)]

theorem l431062 : P.leaf 18 431062 = 211 := by decide +kernel

theorem l431063 : P.leaf 18 431063 = 1355 := by decide +kernel

theorem l431069 : P.leaf 18 431069 = 1466 := by decide +kernel

theorem l431070 : P.leaf 18 431070 = 801 := by decide +kernel

theorem l431071 : P.leaf 18 431071 = 2842 := by decide +kernel

theorem l431093 : P.leaf 18 431093 = 892 := by decide +kernel

theorem l431095 : P.leaf 18 431095 = 2328 := by decide +kernel

theorem l431100 : P.leaf 18 431100 = 1376 := by decide +kernel

theorem l431101 : P.leaf 18 431101 = 1991 := by decide +kernel

theorem l431103 : P.leaf 18 431103 = 5788 := by decide +kernel

theorem l431445 : P.leaf 18 431445 = 51 := by decide +kernel

theorem l431446 : P.leaf 18 431446 = 7 := by decide +kernel

theorem l431447 : P.leaf 18 431447 = 240 := by decide +kernel

theorem l431449 : P.leaf 18 431449 = 4 := by decide +kernel

theorem l431451 : P.leaf 18 431451 = 26 := by decide +kernel

theorem l431453 : P.leaf 18 431453 = 234 := by decide +kernel

theorem l431454 : P.leaf 18 431454 = 65 := by decide +kernel

theorem l431455 : P.leaf 18 431455 = 538 := by decide +kernel

theorem l431479 : P.leaf 18 431479 = 788 := by decide +kernel

theorem l431481 : P.leaf 18 431481 = 60 := by decide +kernel

theorem l431482 : P.leaf 18 431482 = 51 := by decide +kernel

theorem l431483 : P.leaf 18 431483 = 262 := by decide +kernel

theorem l431485 : P.leaf 18 431485 = 813 := by decide +kernel

theorem l431486 : P.leaf 18 431486 = 745 := by decide +kernel

theorem l431487 : P.leaf 18 431487 = 1528 := by decide +kernel

theorem l431605 : P.leaf 18 431605 = 796 := by decide +kernel

theorem l431607 : P.leaf 18 431607 = 2123 := by decide +kernel

theorem l431615 : P.leaf 18 431615 = 4840 := by decide +kernel

theorem l431711 : P.leaf 18 431711 = 230 := by decide +kernel

theorem l431721 : P.leaf 18 431721 = 0 := by decide +kernel

theorem l431727 : P.leaf 18 431727 = 242 := by decide +kernel

theorem l431741 : P.leaf 18 431741 = 341 := by decide +kernel

theorem l431742 : P.leaf 18 431742 = 323 := by decide +kernel

theorem l431743 : P.leaf 18 431743 = 1077 := by decide +kernel

theorem l431861 : P.leaf 18 431861 = 336 := by decide +kernel

theorem l431862 : P.leaf 18 431862 = 106 := by decide +kernel

theorem l431863 : P.leaf 18 431863 = 1240 := by decide +kernel

theorem l431871 : P.leaf 18 431871 = 4716 := by decide +kernel

theorem l431967 : P.leaf 18 431967 = 1469 := by decide +kernel

theorem l431983 : P.leaf 18 431983 = 1600 := by decide +kernel

theorem segOK : checkSeg 20 perms 431062 431999 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1228056 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 431062 431999 1586 1228056 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l431062 (.cons l431063 (.cons l431069 (.cons l431070 (.cons l431071 (.cons l431093 (.cons l431095 (.cons l431100 (.cons l431101 (.cons l431103 (.cons l431445 (.cons l431446 (.cons l431447 (.cons l431449 (.cons l431451 (.cons l431453 (.cons l431454 (.cons l431455 (.cons l431479 (.cons l431481 (.cons l431482 (.cons l431483 (.cons l431485 (.cons l431486 (.cons l431487 (.cons l431605 (.cons l431607 (.cons l431615 (.cons l431711 (.cons l431721 (.cons l431727 (.cons l431741 (.cons l431742 (.cons l431743 (.cons l431861 (.cons l431862 (.cons l431863 (.cons l431871 (.cons l431967 (.cons l431983 (.nil))))))))))))))))))))))))))))))))))))))))))

end S99

end RACert.S0N3.C0
