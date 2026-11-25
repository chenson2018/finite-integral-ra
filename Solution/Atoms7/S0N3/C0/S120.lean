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

namespace S120

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516575, 24), (516576, 24), (516577, 24), (516578, 24), (516579, 24), (516580, 24), (516581, 24), (516582, 24), (516583, 24), (516584, 24), (516585, 24), (516586, 24), (516587, 24), (516588, 24), (516589, 24), (516590, 24), (516591, 24), (516592, 24), (516593, 24), (516594, 24), (516595, 24), (516596, 24), (516597, 24), (516598, 24), (516599, 24), (516600, 24), (516601, 24), (516602, 24), (516603, 24), (516604, 24), (516605, 24), (516606, 24), (516607, 24), (516617, 24), (516619, 24), (516621, 24), (516623, 24), (516633, 24), (516634, 12), (516635, 24), (516637, 24), (516638, 24), (516639, 24), (516649, 12), (516651, 24), (516652, 24), (516653, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 418]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516575, 3921), (516576, 0), (516577, 47), (516578, 232), (516579, 527), (516580, 76), (516581, 104), (516582, 1287), (516583, 1427), (516586, 649), (516587, 722), (516590, 2026), (516591, 2118), (516592, 67), (516593, 305), (516594, 488), (516595, 1136), (516596, 288), (516597, 821), (516598, 2761), (516599, 3184), (516600, 127), (516601, 351), (516602, 1154), (516603, 1475), (516604, 737), (516605, 1104), (516606, 3492), (516607, 5394), (516617, 42), (516619, 40), (516623, 0), (516633, 40), (516634, 108), (516635, 216), (516637, 0), (516638, 0), (516639, 0), (516649, 90), (516651, 82)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 516575 516654 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 876936 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516575 516654 1104 876936 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S120

end RACert.S0N3.C0
