/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S3N1.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S3N1.C1

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

theorem segOK0 : checkSeg 0 perms 0 1 seg0 = true := by decide +kernel

theorem sumOK0 : P.sumEvE 21 3 qt ow qmFlat seg0 ev0 0 680611 = true := by decide +kernel

theorem part0 : OrbitSeg 0 perms (P.leaf (21 + 3)) 0 1 1 680611 :=
  OrbitSeg.of_check segOK0 (by decide +kernel) (sumEvE_sum check rows elimOK flatOK sumOK0)

theorem total : OrbitSeg 0 perms (P.leaf (21 + 3)) 0 1 1 680611 :=
  OrbitSeg.cast (part0)
    (by decide +kernel) (by decide +kernel)

end S0

end RACert.S3N1.C1
