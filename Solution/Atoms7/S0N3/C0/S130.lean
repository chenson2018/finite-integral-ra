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

namespace S130

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(520991, 48), (521005, 24), (521007, 48), (521023, 24), (521031, 48), (521035, 48), (521039, 48), (521045, 48), (521046, 48), (521047, 48), (521049, 48), (521050, 48), (521051, 48), (521053, 48), (521054, 48), (521055, 48), (521061, 48), (521062, 48), (521063, 48), (521065, 48), (521066, 48), (521067, 48), (521069, 48), (521070, 48), (521071, 48), (521076, 48), (521077, 48), (521078, 48), (521079, 48), (521080, 24), (521081, 48), (521082, 48), (521083, 48), (521084, 48), (521085, 48), (521086, 48), (521087, 48), (521095, 48), (521099, 48), (521103, 48), (521109, 48), (521110, 48), (521111, 48), (521113, 48), (521114, 48), (521115, 48), (521117, 48), (521118, 48), (521119, 48), (521125, 48), (521126, 48), (521127, 48), (521129, 48), (521130, 48), (521131, 48), (521133, 48), (521134, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 502, 0, 0, 0, 650, 0, 0, 0, 0, 650, 650, 650, 0, 0, 0, 502, 0, 0, 439, 650, 650, 502, 0, 0, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 0, 502, 0, 0, 502, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(520991, 250), (521007, 174), (521023, 276), (521031, 604), (521039, 714), (521045, 851), (521046, 780), (521047, 1368), (521053, 962), (521054, 980), (521055, 1697), (521062, 809), (521063, 956), (521070, 1018), (521071, 1177), (521076, 334), (521077, 859), (521078, 1061), (521079, 1392), (521084, 848), (521085, 974), (521086, 1298), (521087, 1745), (521095, 725), (521099, 946), (521103, 1676), (521109, 888), (521110, 967), (521111, 1337), (521113, 998), (521114, 1174), (521115, 1550), (521117, 1760), (521118, 2064), (521119, 3316), (521126, 830), (521127, 905), (521130, 1134), (521131, 1190), (521134, 2084)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 520991 521135 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2137584 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 520991 521135 2664 2137584 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S130

end RACert.S0N3.C0
