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

namespace S4

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(2779, 60), (2780, 60), (2781, 120), (2783, 60), (2784, 60), (2785, 120), (2787, 60), (2788, 60), (2789, 120), (2791, 60), (2792, 120), (2793, 120), (2794, 120), (2795, 120), (2796, 120), (2797, 120), (2798, 120), (2799, 120), (2808, 60), (2809, 120), (2811, 60), (2812, 60), (2813, 120), (2815, 60), (3008, 60), (3009, 60), (3010, 120), (3011, 120), (3014, 60), (3015, 60), (3016, 60), (3017, 60), (3018, 120), (3019, 120), (3022, 60), (3023, 60), (3024, 60), (3025, 60), (3026, 120), (3027, 120)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(2779, 20), (2780, 17), (2781, 24), (2783, 37), (2784, 108), (2785, 168), (2787, 259), (2788, 120), (2789, 196), (2791, 323), (2792, 108), (2793, 168), (2794, 168), (2795, 259), (2796, 120), (2797, 196), (2798, 196), (2799, 323), (2808, 116), (2809, 190), (2811, 311), (2812, 132), (2813, 228), (2815, 395), (3008, 98), (3009, 151), (3010, 124), (3011, 202), (3014, 156), (3015, 264), (3016, 128), (3017, 169), (3018, 148), (3019, 229), (3022, 188), (3023, 301), (3024, 98), (3025, 151), (3026, 124), (3027, 202)]

theorem l2779 : P.leaf 20 2779 = 20 := by decide +kernel

theorem l2780 : P.leaf 20 2780 = 17 := by decide +kernel

theorem l2781 : P.leaf 20 2781 = 24 := by decide +kernel

theorem l2783 : P.leaf 20 2783 = 37 := by decide +kernel

theorem l2784 : P.leaf 20 2784 = 108 := by decide +kernel

theorem l2785 : P.leaf 20 2785 = 168 := by decide +kernel

theorem l2787 : P.leaf 20 2787 = 259 := by decide +kernel

theorem l2788 : P.leaf 20 2788 = 120 := by decide +kernel

theorem l2789 : P.leaf 20 2789 = 196 := by decide +kernel

theorem l2791 : P.leaf 20 2791 = 323 := by decide +kernel

theorem l2792 : P.leaf 20 2792 = 108 := by decide +kernel

theorem l2793 : P.leaf 20 2793 = 168 := by decide +kernel

theorem l2794 : P.leaf 20 2794 = 168 := by decide +kernel

theorem l2795 : P.leaf 20 2795 = 259 := by decide +kernel

theorem l2796 : P.leaf 20 2796 = 120 := by decide +kernel

theorem l2797 : P.leaf 20 2797 = 196 := by decide +kernel

theorem l2798 : P.leaf 20 2798 = 196 := by decide +kernel

theorem l2799 : P.leaf 20 2799 = 323 := by decide +kernel

theorem l2808 : P.leaf 20 2808 = 116 := by decide +kernel

theorem l2809 : P.leaf 20 2809 = 190 := by decide +kernel

theorem l2811 : P.leaf 20 2811 = 311 := by decide +kernel

theorem l2812 : P.leaf 20 2812 = 132 := by decide +kernel

theorem l2813 : P.leaf 20 2813 = 228 := by decide +kernel

theorem l2815 : P.leaf 20 2815 = 395 := by decide +kernel

theorem l3008 : P.leaf 20 3008 = 98 := by decide +kernel

theorem l3009 : P.leaf 20 3009 = 151 := by decide +kernel

theorem l3010 : P.leaf 20 3010 = 124 := by decide +kernel

theorem l3011 : P.leaf 20 3011 = 202 := by decide +kernel

theorem l3014 : P.leaf 20 3014 = 156 := by decide +kernel

theorem l3015 : P.leaf 20 3015 = 264 := by decide +kernel

theorem l3016 : P.leaf 20 3016 = 128 := by decide +kernel

theorem l3017 : P.leaf 20 3017 = 169 := by decide +kernel

theorem l3018 : P.leaf 20 3018 = 148 := by decide +kernel

theorem l3019 : P.leaf 20 3019 = 229 := by decide +kernel

theorem l3022 : P.leaf 20 3022 = 188 := by decide +kernel

theorem l3023 : P.leaf 20 3023 = 301 := by decide +kernel

theorem l3024 : P.leaf 20 3024 = 98 := by decide +kernel

theorem l3025 : P.leaf 20 3025 = 151 := by decide +kernel

theorem l3026 : P.leaf 20 3026 = 124 := by decide +kernel

theorem l3027 : P.leaf 20 3027 = 202 := by decide +kernel

theorem segOK : checkSeg 15 perms 2779 3030 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 617280 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 2779 3030 3540 617280 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l2779 (.cons l2780 (.cons l2781 (.cons l2783 (.cons l2784 (.cons l2785 (.cons l2787 (.cons l2788 (.cons l2789 (.cons l2791 (.cons l2792 (.cons l2793 (.cons l2794 (.cons l2795 (.cons l2796 (.cons l2797 (.cons l2798 (.cons l2799 (.cons l2808 (.cons l2809 (.cons l2811 (.cons l2812 (.cons l2813 (.cons l2815 (.cons l3008 (.cons l3009 (.cons l3010 (.cons l3011 (.cons l3014 (.cons l3015 (.cons l3016 (.cons l3017 (.cons l3018 (.cons l3019 (.cons l3022 (.cons l3023 (.cons l3024 (.cons l3025 (.cons l3026 (.cons l3027 (.nil))))))))))))))))))))))))))))))))))))))))))

end S4

end RACert.S5N0.C0
