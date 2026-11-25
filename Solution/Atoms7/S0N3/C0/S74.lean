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

namespace S74

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(240703, 12), (240711, 12), (240715, 6), (240719, 12), (240723, 24), (240727, 24), (240731, 24), (240735, 24), (240755, 12), (240759, 12), (240763, 12), (240767, 12), (240775, 6), (240783, 12), (240787, 24), (240791, 24), (240795, 24), (240799, 24), (240819, 12), (240823, 12), (240827, 12), (240831, 12), (240847, 6), (240851, 24), (240855, 24), (240859, 24), (240863, 24), (240883, 12), (240887, 12), (240891, 12), (240895, 12), (240915, 12), (240919, 24), (240923, 24), (240927, 24), (240931, 12), (240935, 24), (240939, 24), (240943, 24), (240947, 24), (240951, 24), (240955, 24), (240959, 24), (240983, 24), (240987, 12), (240991, 24), (240999, 24), (241003, 12), (241007, 24), (241011, 24), (241015, 24), (241019, 24), (241023, 24), (241047, 12), (241055, 24), (241063, 12), (241071, 24), (241075, 24), (241079, 24), (241083, 24), (241087, 24), (241119, 12), (241135, 12), (241139, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 517, 440, 517, 440, 0, 440, 0, 440, 0, 440, 0, 517, 517, 573, 0, 573, 0, 0, 0, 0, 0, 517, 573, 0, 573, 0, 0, 0, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 0, 440, 0, 0, 440, 0, 440, 0, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(240703, 294), (240727, 96), (240735, 128), (240759, 613), (240767, 684), (240791, 252), (240799, 320), (240819, 288), (240823, 1421), (240827, 585), (240831, 3001), (240855, 252), (240863, 320), (240883, 384), (240887, 2278), (240891, 774), (240895, 4024), (240919, 103), (240927, 144), (240935, 93), (240943, 140), (240951, 336), (240959, 448), (240983, 325), (240991, 437), (240999, 315), (241007, 418), (241015, 846), (241023, 1026), (241047, 672), (241055, 1499), (241063, 636), (241071, 1568), (241075, 288), (241079, 1830), (241083, 903), (241087, 3708), (241119, 2396), (241135, 2324), (241139, 384)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 240703 241143 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 632784 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 240703 241143 1194 632784 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S74

end RACert.S0N3.C0
