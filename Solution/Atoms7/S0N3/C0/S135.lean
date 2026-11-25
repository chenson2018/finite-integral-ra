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

namespace S135

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1044757, 24), (1044758, 12), (1044759, 24), (1044762, 12), (1044763, 24), (1044764, 24), (1044765, 24), (1044766, 24), (1044767, 24), (1044791, 12), (1044796, 12), (1044797, 24), (1044799, 12), (1044801, 8), (1044802, 8), (1044803, 24), (1044805, 24), (1044806, 24), (1044807, 24), (1044809, 24), (1044810, 24), (1044811, 24), (1044813, 24), (1044814, 24), (1044815, 24), (1044819, 24), (1044820, 24), (1044821, 24), (1044822, 24), (1044823, 24), (1044824, 12), (1044825, 24), (1044826, 24), (1044827, 24), (1044828, 24), (1044829, 24), (1044830, 24), (1044831, 24), (1044835, 24), (1044837, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1044757, 201), (1044758, 200), (1044759, 286), (1044762, 138), (1044763, 254), (1044764, 286), (1044765, 318), (1044766, 286), (1044767, 356), (1044791, 339), (1044796, 310), (1044797, 318), (1044799, 356), (1044801, 71), (1044802, 71), (1044803, 331), (1044805, 494), (1044806, 741), (1044807, 1446), (1044809, 449), (1044810, 314), (1044811, 888), (1044813, 912), (1044814, 912), (1044815, 1479), (1044819, 898), (1044820, 1132), (1044821, 2241), (1044822, 1774), (1044823, 3337), (1044824, 466), (1044825, 1265), (1044826, 851), (1044827, 2157), (1044828, 2462), (1044829, 3384), (1044830, 2652), (1044831, 6638), (1044835, 1194), (1044837, 1816)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 1044757 1044838 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1032572 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 1044757 1044838 856 1032572 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S135

end RACert.S0N3.C0
