/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C6.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C6

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 1), (2, 2), (3, 2), (6, 1), (7, 1), (8, 2), (9, 2), (10, 4), (11, 4), (14, 2), (15, 2), (24, 1), (25, 1), (26, 2), (27, 2), (30, 1), (31, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

theorem sumOK0 : P.sumEvE 20 1 qt ow qmFlat seg0 ev0 0 1315498 = true := by decide +kernel

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 5 perms 0 32 seg = true := by decide +kernel

theorem total : OrbitSeg 5 perms (P.leaf (20 + 1)) 0 32 32 1315498 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S2N2.C6
