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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 431062 431999 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1228056 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 431062 431999 1586 1228056 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S99

end RACert.S0N3.C0
