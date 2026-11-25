/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C7.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C7

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (3, 1), (4, 4), (5, 8), (7, 4), (12, 2), (13, 4), (15, 2), (20, 4), (21, 4), (22, 4), (23, 4), (28, 4), (29, 8), (31, 4), (60, 1), (61, 2), (63, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := [0, 0, 0, 29, 0, 0, 29]

theorem sumOK0 : P.sumEvE 20 2 qt ow qmFlat seg0 ev0 0 3501868 = true := by decide +kernel

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf (20 + 2)) 0 64 64 3501868 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S4N1.C7
