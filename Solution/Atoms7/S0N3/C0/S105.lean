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

namespace S105

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439678, 48), (439679, 48), (439701, 48), (439702, 48), (439703, 48), (439705, 16), (439707, 48), (439709, 48), (439710, 48), (439711, 48), (439717, 48), (439718, 24), (439719, 48), (439723, 48), (439725, 48), (439726, 48), (439727, 48), (439733, 48), (439734, 48), (439735, 48), (439739, 48), (439741, 48), (439742, 48), (439743, 48), (439766, 48), (439767, 48), (439770, 48), (439771, 48), (439774, 48), (439775, 48), (439781, 48), (439783, 48), (439785, 48), (439787, 48), (439789, 48), (439790, 24), (439791, 48), (439797, 48), (439798, 48), (439799, 48), (439801, 48), (439802, 48), (439803, 48), (439805, 48), (439806, 48), (439807, 48), (439898, 8), (439899, 48), (439903, 24), (439913, 24), (439915, 48), (439917, 48), (439919, 48), (439931, 24), (439933, 48), (439934, 48), (439935, 48), (439973, 24), (439975, 48), (439983, 24), (439989, 48), (439990, 48), (439991, 48), (439997, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 602, 431, 602, 0, 0, 0, 0, 0, 502, 602, 602, 0, 502, 0, 0, 602, 602, 602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 502, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 684, 0, 502, 684, 502, 0, 684, 0, 0, 0, 502, 602, 0, 602, 602, 602, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439678, 1002), (439679, 2318), (439705, 155), (439707, 393), (439709, 571), (439710, 100), (439711, 957), (439723, 515), (439726, 613), (439727, 1143), (439739, 1157), (439741, 1527), (439742, 1331), (439743, 2609), (439766, 138), (439767, 1105), (439770, 100), (439771, 867), (439774, 500), (439775, 1916), (439783, 1451), (439787, 997), (439790, 1262), (439791, 2401), (439797, 1476), (439798, 1367), (439799, 3007), (439801, 1187), (439802, 868), (439803, 2299), (439805, 2907), (439806, 2611), (439807, 5512), (439903, 230), (439919, 304), (439933, 541), (439934, 323), (439935, 1201), (439983, 374), (439997, 796)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 439678 439998 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2356544 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439678 439998 2832 2356544 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S105

end RACert.S0N3.C0
