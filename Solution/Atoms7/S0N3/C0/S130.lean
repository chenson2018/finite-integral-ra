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

theorem l520991 : P.leaf 18 520991 = 250 := by decide +kernel

theorem l521007 : P.leaf 18 521007 = 174 := by decide +kernel

theorem l521023 : P.leaf 18 521023 = 276 := by decide +kernel

theorem l521031 : P.leaf 18 521031 = 604 := by decide +kernel

theorem l521039 : P.leaf 18 521039 = 714 := by decide +kernel

theorem l521045 : P.leaf 18 521045 = 851 := by decide +kernel

theorem l521046 : P.leaf 18 521046 = 780 := by decide +kernel

theorem l521047 : P.leaf 18 521047 = 1368 := by decide +kernel

theorem l521053 : P.leaf 18 521053 = 962 := by decide +kernel

theorem l521054 : P.leaf 18 521054 = 980 := by decide +kernel

theorem l521055 : P.leaf 18 521055 = 1697 := by decide +kernel

theorem l521062 : P.leaf 18 521062 = 809 := by decide +kernel

theorem l521063 : P.leaf 18 521063 = 956 := by decide +kernel

theorem l521070 : P.leaf 18 521070 = 1018 := by decide +kernel

theorem l521071 : P.leaf 18 521071 = 1177 := by decide +kernel

theorem l521076 : P.leaf 18 521076 = 334 := by decide +kernel

theorem l521077 : P.leaf 18 521077 = 859 := by decide +kernel

theorem l521078 : P.leaf 18 521078 = 1061 := by decide +kernel

theorem l521079 : P.leaf 18 521079 = 1392 := by decide +kernel

theorem l521084 : P.leaf 18 521084 = 848 := by decide +kernel

theorem l521085 : P.leaf 18 521085 = 974 := by decide +kernel

theorem l521086 : P.leaf 18 521086 = 1298 := by decide +kernel

theorem l521087 : P.leaf 18 521087 = 1745 := by decide +kernel

theorem l521095 : P.leaf 18 521095 = 725 := by decide +kernel

theorem l521099 : P.leaf 18 521099 = 946 := by decide +kernel

theorem l521103 : P.leaf 18 521103 = 1676 := by decide +kernel

theorem l521109 : P.leaf 18 521109 = 888 := by decide +kernel

theorem l521110 : P.leaf 18 521110 = 967 := by decide +kernel

theorem l521111 : P.leaf 18 521111 = 1337 := by decide +kernel

theorem l521113 : P.leaf 18 521113 = 998 := by decide +kernel

theorem l521114 : P.leaf 18 521114 = 1174 := by decide +kernel

theorem l521115 : P.leaf 18 521115 = 1550 := by decide +kernel

theorem l521117 : P.leaf 18 521117 = 1760 := by decide +kernel

theorem l521118 : P.leaf 18 521118 = 2064 := by decide +kernel

theorem l521119 : P.leaf 18 521119 = 3316 := by decide +kernel

theorem l521126 : P.leaf 18 521126 = 830 := by decide +kernel

theorem l521127 : P.leaf 18 521127 = 905 := by decide +kernel

theorem l521130 : P.leaf 18 521130 = 1134 := by decide +kernel

theorem l521131 : P.leaf 18 521131 = 1190 := by decide +kernel

theorem l521134 : P.leaf 18 521134 = 2084 := by decide +kernel

theorem segOK : checkSeg 20 perms 520991 521135 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2137584 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 520991 521135 2664 2137584 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l520991 (.cons l521007 (.cons l521023 (.cons l521031 (.cons l521039 (.cons l521045 (.cons l521046 (.cons l521047 (.cons l521053 (.cons l521054 (.cons l521055 (.cons l521062 (.cons l521063 (.cons l521070 (.cons l521071 (.cons l521076 (.cons l521077 (.cons l521078 (.cons l521079 (.cons l521084 (.cons l521085 (.cons l521086 (.cons l521087 (.cons l521095 (.cons l521099 (.cons l521103 (.cons l521109 (.cons l521110 (.cons l521111 (.cons l521113 (.cons l521114 (.cons l521115 (.cons l521117 (.cons l521118 (.cons l521119 (.cons l521126 (.cons l521127 (.cons l521130 (.cons l521131 (.cons l521134 (.nil))))))))))))))))))))))))))))))))))))))))))

end S130

end RACert.S0N3.C0
