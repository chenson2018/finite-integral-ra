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

theorem l2488 : P.leaf 20 2488 = 32 := by decide +kernel

theorem l2489 : P.leaf 20 2489 = 28 := by decide +kernel

theorem l2491 : P.leaf 20 2491 = 44 := by decide +kernel

theorem l2492 : P.leaf 20 2492 = 42 := by decide +kernel

theorem l2493 : P.leaf 20 2493 = 40 := by decide +kernel

theorem l2495 : P.leaf 20 2495 = 72 := by decide +kernel

theorem l2528 : P.leaf 20 2528 = 51 := by decide +kernel

theorem l2529 : P.leaf 20 2529 = 64 := by decide +kernel

theorem l2531 : P.leaf 20 2531 = 84 := by decide +kernel

theorem l2532 : P.leaf 20 2532 = 52 := by decide +kernel

theorem l2533 : P.leaf 20 2533 = 66 := by decide +kernel

theorem l2535 : P.leaf 20 2535 = 86 := by decide +kernel

theorem l2540 : P.leaf 20 2540 = 56 := by decide +kernel

theorem l2541 : P.leaf 20 2541 = 72 := by decide +kernel

theorem l2543 : P.leaf 20 2543 = 92 := by decide +kernel

theorem l2544 : P.leaf 20 2544 = 73 := by decide +kernel

theorem l2545 : P.leaf 20 2545 = 80 := by decide +kernel

theorem l2547 : P.leaf 20 2547 = 132 := by decide +kernel

theorem l2548 : P.leaf 20 2548 = 78 := by decide +kernel

theorem l2549 : P.leaf 20 2549 = 86 := by decide +kernel

theorem l2551 : P.leaf 20 2551 = 146 := by decide +kernel

theorem l2556 : P.leaf 20 2556 = 96 := by decide +kernel

theorem l2557 : P.leaf 20 2557 = 104 := by decide +kernel

theorem l2559 : P.leaf 20 2559 = 188 := by decide +kernel

theorem l2752 : P.leaf 20 2752 = 10 := by decide +kernel

theorem l2753 : P.leaf 20 2753 = 12 := by decide +kernel

theorem l2755 : P.leaf 20 2755 = 16 := by decide +kernel

theorem l2756 : P.leaf 20 2756 = 14 := by decide +kernel

theorem l2757 : P.leaf 20 2757 = 20 := by decide +kernel

theorem l2759 : P.leaf 20 2759 = 32 := by decide +kernel

theorem l2760 : P.leaf 20 2760 = 10 := by decide +kernel

theorem l2761 : P.leaf 20 2761 = 12 := by decide +kernel

theorem l2762 : P.leaf 20 2762 = 12 := by decide +kernel

theorem l2763 : P.leaf 20 2763 = 16 := by decide +kernel

theorem l2764 : P.leaf 20 2764 = 13 := by decide +kernel

theorem l2765 : P.leaf 20 2765 = 20 := by decide +kernel

theorem l2766 : P.leaf 20 2766 = 21 := by decide +kernel

theorem l2767 : P.leaf 20 2767 = 32 := by decide +kernel

theorem l2776 : P.leaf 20 2776 = 14 := by decide +kernel

theorem l2777 : P.leaf 20 2777 = 16 := by decide +kernel

theorem segOK : checkSeg 15 perms 2488 2779 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 129120 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 2488 2779 3060 129120 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l2488 (.cons l2489 (.cons l2491 (.cons l2492 (.cons l2493 (.cons l2495 (.cons l2528 (.cons l2529 (.cons l2531 (.cons l2532 (.cons l2533 (.cons l2535 (.cons l2540 (.cons l2541 (.cons l2543 (.cons l2544 (.cons l2545 (.cons l2547 (.cons l2548 (.cons l2549 (.cons l2551 (.cons l2556 (.cons l2557 (.cons l2559 (.cons l2752 (.cons l2753 (.cons l2755 (.cons l2756 (.cons l2757 (.cons l2759 (.cons l2760 (.cons l2761 (.cons l2762 (.cons l2763 (.cons l2764 (.cons l2765 (.cons l2766 (.cons l2767 (.cons l2776 (.cons l2777 (.nil))))))))))))))))))))))))))))))))))))))))))

end S3

end RACert.S5N0.C0
