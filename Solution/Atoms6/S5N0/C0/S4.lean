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

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 2779 3030 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 617280 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 2779 3030 3540 617280 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S4

end RACert.S5N0.C0
