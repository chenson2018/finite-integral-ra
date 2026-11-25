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

namespace S136

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1044838, 24), (1044839, 24), (1044840, 12), (1044841, 24), (1044842, 24), (1044843, 24), (1044844, 24), (1044845, 24), (1044846, 24), (1044847, 24), (1044851, 24), (1044852, 24), (1044853, 24), (1044854, 24), (1044855, 24), (1044856, 24), (1044857, 24), (1044858, 24), (1044859, 24), (1044860, 24), (1044861, 24), (1044862, 24), (1044863, 24), (1044931, 12), (1044935, 24), (1044943, 12), (1044945, 24), (1044946, 24), (1044947, 24), (1044949, 24), (1044950, 24), (1044951, 24), (1044953, 24), (1044954, 24), (1044955, 24), (1044956, 12), (1044957, 24), (1044958, 24), (1044959, 24), (1044976, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1044838, 2838), (1044839, 4044), (1044840, 942), (1044841, 1406), (1044842, 1876), (1044843, 2809), (1044844, 3768), (1044845, 3952), (1044846, 5064), (1044847, 9740), (1044851, 1655), (1044852, 2658), (1044853, 3625), (1044854, 3681), (1044855, 5081), (1044856, 2111), (1044857, 2759), (1044858, 2719), (1044859, 4156), (1044860, 5568), (1044861, 6170), (1044862, 6154), (1044863, 12235), (1044931, 1284), (1044935, 2162), (1044943, 2250), (1044945, 2900), (1044946, 2187), (1044947, 5835), (1044949, 5832), (1044950, 4934), (1044951, 8714), (1044953, 6086), (1044954, 4463), (1044955, 8943), (1044956, 8388), (1044957, 10318), (1044958, 8814), (1044959, 22818), (1044976, 760)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 1044838 1044977 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4677288 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1044838 1044977 900 4677288 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S136

end RACert.S0N3.C0
