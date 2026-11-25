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

theorem l240703 : P.leaf 18 240703 = 294 := by decide +kernel

theorem l240727 : P.leaf 18 240727 = 96 := by decide +kernel

theorem l240735 : P.leaf 18 240735 = 128 := by decide +kernel

theorem l240759 : P.leaf 18 240759 = 613 := by decide +kernel

theorem l240767 : P.leaf 18 240767 = 684 := by decide +kernel

theorem l240791 : P.leaf 18 240791 = 252 := by decide +kernel

theorem l240799 : P.leaf 18 240799 = 320 := by decide +kernel

theorem l240819 : P.leaf 18 240819 = 288 := by decide +kernel

theorem l240823 : P.leaf 18 240823 = 1421 := by decide +kernel

theorem l240827 : P.leaf 18 240827 = 585 := by decide +kernel

theorem l240831 : P.leaf 18 240831 = 3001 := by decide +kernel

theorem l240855 : P.leaf 18 240855 = 252 := by decide +kernel

theorem l240863 : P.leaf 18 240863 = 320 := by decide +kernel

theorem l240883 : P.leaf 18 240883 = 384 := by decide +kernel

theorem l240887 : P.leaf 18 240887 = 2278 := by decide +kernel

theorem l240891 : P.leaf 18 240891 = 774 := by decide +kernel

theorem l240895 : P.leaf 18 240895 = 4024 := by decide +kernel

theorem l240919 : P.leaf 18 240919 = 103 := by decide +kernel

theorem l240927 : P.leaf 18 240927 = 144 := by decide +kernel

theorem l240935 : P.leaf 18 240935 = 93 := by decide +kernel

theorem l240943 : P.leaf 18 240943 = 140 := by decide +kernel

theorem l240951 : P.leaf 18 240951 = 336 := by decide +kernel

theorem l240959 : P.leaf 18 240959 = 448 := by decide +kernel

theorem l240983 : P.leaf 18 240983 = 325 := by decide +kernel

theorem l240991 : P.leaf 18 240991 = 437 := by decide +kernel

theorem l240999 : P.leaf 18 240999 = 315 := by decide +kernel

theorem l241007 : P.leaf 18 241007 = 418 := by decide +kernel

theorem l241015 : P.leaf 18 241015 = 846 := by decide +kernel

theorem l241023 : P.leaf 18 241023 = 1026 := by decide +kernel

theorem l241047 : P.leaf 18 241047 = 672 := by decide +kernel

theorem l241055 : P.leaf 18 241055 = 1499 := by decide +kernel

theorem l241063 : P.leaf 18 241063 = 636 := by decide +kernel

theorem l241071 : P.leaf 18 241071 = 1568 := by decide +kernel

theorem l241075 : P.leaf 18 241075 = 288 := by decide +kernel

theorem l241079 : P.leaf 18 241079 = 1830 := by decide +kernel

theorem l241083 : P.leaf 18 241083 = 903 := by decide +kernel

theorem l241087 : P.leaf 18 241087 = 3708 := by decide +kernel

theorem l241119 : P.leaf 18 241119 = 2396 := by decide +kernel

theorem l241135 : P.leaf 18 241135 = 2324 := by decide +kernel

theorem l241139 : P.leaf 18 241139 = 384 := by decide +kernel

theorem segOK : checkSeg 20 perms 240703 241143 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 632784 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 240703 241143 1194 632784 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l240703 (.cons l240727 (.cons l240735 (.cons l240759 (.cons l240767 (.cons l240791 (.cons l240799 (.cons l240819 (.cons l240823 (.cons l240827 (.cons l240831 (.cons l240855 (.cons l240863 (.cons l240883 (.cons l240887 (.cons l240891 (.cons l240895 (.cons l240919 (.cons l240927 (.cons l240935 (.cons l240943 (.cons l240951 (.cons l240959 (.cons l240983 (.cons l240991 (.cons l240999 (.cons l241007 (.cons l241015 (.cons l241023 (.cons l241047 (.cons l241055 (.cons l241063 (.cons l241071 (.cons l241075 (.cons l241079 (.cons l241083 (.cons l241087 (.cons l241119 (.cons l241135 (.cons l241139 (.nil))))))))))))))))))))))))))))))))))))))))))

end S74

end RACert.S0N3.C0
