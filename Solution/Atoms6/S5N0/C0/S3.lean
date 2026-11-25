/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S3

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(2488, 60), (2489, 120), (2491, 60), (2492, 60), (2493, 120), (2495, 60), (2528, 30), (2529, 60), (2531, 30), (2532, 60), (2533, 120), (2535, 60), (2540, 30), (2541, 60), (2543, 30), (2544, 30), (2545, 60), (2547, 30), (2548, 60), (2549, 120), (2551, 60), (2556, 30), (2557, 60), (2559, 30), (2752, 60), (2753, 120), (2755, 60), (2756, 60), (2757, 120), (2759, 60), (2760, 120), (2761, 120), (2762, 120), (2763, 120), (2764, 120), (2765, 120), (2766, 120), (2767, 120), (2776, 60), (2777, 120)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(2488, 32), (2489, 28), (2491, 44), (2492, 42), (2493, 40), (2495, 72), (2528, 51), (2529, 64), (2531, 84), (2532, 52), (2533, 66), (2535, 86), (2540, 56), (2541, 72), (2543, 92), (2544, 73), (2545, 80), (2547, 132), (2548, 78), (2549, 86), (2551, 146), (2556, 96), (2557, 104), (2559, 188), (2752, 10), (2753, 12), (2755, 16), (2756, 14), (2757, 20), (2759, 32), (2760, 10), (2761, 12), (2762, 12), (2763, 16), (2764, 13), (2765, 20), (2766, 21), (2767, 32), (2776, 14), (2777, 16)]

theorem leavesOK : P.checkLeavesR 20 qm live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 2488 2779 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 129120 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 2488 2779 3060 129120 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S3

end RACert.S5N0.C0
