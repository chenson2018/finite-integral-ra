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

namespace S94

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(259959, 48), (259961, 24), (259962, 24), (259963, 48), (259965, 48), (259966, 48), (259967, 48), (259971, 48), (259975, 48), (259979, 48), (259983, 48), (259987, 48), (259991, 48), (259995, 48), (259999, 48), (260003, 48), (260007, 48), (260011, 48), (260015, 48), (260019, 48), (260021, 24), (260022, 24), (260023, 48), (260027, 48), (260029, 48), (260030, 48), (260031, 48), (260035, 48), (260039, 48), (260043, 48), (260047, 48), (260051, 48), (260055, 48), (260059, 48), (260063, 48), (260067, 48), (260071, 48), (260075, 48), (260079, 48), (260083, 48), (260087, 48), (260091, 48), (260093, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 439, 438, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(259959, 2782), (259965, 1580), (259966, 1380), (259967, 3916), (259971, 168), (259975, 1420), (259979, 1098), (259983, 2508), (259987, 272), (259991, 2248), (259995, 1600), (259999, 4243), (260003, 292), (260007, 2348), (260011, 1656), (260015, 4230), (260019, 428), (260021, 2264), (260022, 1712), (260023, 4150), (260027, 2228), (260029, 2916), (260030, 2548), (260031, 6534), (260035, 400), (260039, 2584), (260043, 1278), (260047, 3400), (260051, 616), (260055, 3730), (260059, 2012), (260063, 6158), (260067, 632), (260071, 3792), (260075, 2074), (260079, 6158), (260083, 856), (260087, 5182), (260091, 2858), (260093, 3752)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 259959 260094 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4614672 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 259959 260094 1944 4614672 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S94

end RACert.S0N3.C0
