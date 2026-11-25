/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0

open RACert RACert.Problem

namespace S192

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(67108535, 24), (67108542, 12), (67108543, 12), (67108574, 12), (67108575, 12), (67108606, 8), (67108607, 8), (67108862, 1), (67108863, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

theorem segOK0 : checkSeg 26 perms 67108535 67108864 seg0 = true := by decide +kernel

theorem sumOK0 : P.sumEvE 20 4 qt ow qmFlat seg0 ev0 0 442052730 = true := by decide +kernel

theorem part0 : OrbitSeg 26 perms (P.leaf (20 + 4)) 67108535 67108864 90 442052730 :=
  OrbitSeg.of_check segOK0 (by decide +kernel) (sumEvE_sum check rows elimOK flatOK sumOK0)

theorem total : OrbitSeg 26 perms (P.leaf (20 + 4)) 67108535 67108864 90 442052730 :=
  OrbitSeg.cast (part0)
    (by decide +kernel) (by decide +kernel)

end S192

end RACert.S4N1.C0
