/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S1N2.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S1N2.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 4), (7, 4), (15, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

theorem segOK0 : checkSeg 4 perms 0 16 seg0 = true := by decide +kernel

theorem sumOK0 : P.sumEvE 20 1 qt ow qmFlat seg0 ev0 0 312508 = true := by decide +kernel

theorem part0 : OrbitSeg 4 perms (P.leaf (20 + 1)) 0 16 16 312508 :=
  OrbitSeg.of_check segOK0 (by decide +kernel) (sumEvE_sum check rows elimOK flatOK sumOK0)

theorem total : OrbitSeg 4 perms (P.leaf (20 + 1)) 0 16 16 312508 :=
  OrbitSeg.cast (part0)
    (by decide +kernel) (by decide +kernel)

end S0

end RACert.S1N2.C0
