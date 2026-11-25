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

namespace S84

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(243999, 48), (244002, 48), (244003, 48), (244006, 48), (244007, 48), (244010, 48), (244011, 48), (244014, 48), (244015, 48), (244018, 48), (244019, 48), (244022, 48), (244023, 48), (244026, 48), (244027, 48), (244030, 48), (244031, 48), (244035, 48), (244039, 48), (244043, 48), (244047, 48), (244051, 48), (244054, 48), (244055, 48), (244058, 24), (244059, 48), (244062, 48), (244063, 48), (244066, 48), (244067, 48), (244070, 48), (244071, 48), (244074, 48), (244075, 48), (244078, 48), (244079, 48), (244082, 48), (244083, 48), (244086, 48), (244087, 48), (244090, 48), (244091, 48), (244094, 48), (244095, 48), (244099, 48), (244103, 48), (244107, 48), (244111, 48), (244115, 48), (244118, 24), (244119, 48), (244123, 48), (244126, 48), (244127, 48), (244130, 48), (244131, 48), (244134, 48), (244135, 48), (244138, 48), (244139, 48), (244142, 48), (244143, 48), (244146, 48), (244147, 48), (244150, 48), (244151, 48), (244154, 48), (244155, 48), (244158, 48), (244159, 48), (244163, 48), (244167, 48), (244171, 48), (244175, 48), (244179, 48), (244183, 48), (244187, 48), (244190, 24), (244191, 48), (244194, 48), (244195, 48), (244198, 48), (244199, 48), (244202, 48), (244203, 48), (244206, 48), (244207, 48), (244210, 48), (244211, 48), (244214, 48), (244215, 48), (244218, 48), (244219, 48), (244222, 48), (244223, 48), (244227, 48), (244231, 48), (244235, 48), (244239, 48), (244243, 48), (244247, 48), (244251, 48), (244255, 48), (244258, 24), (244259, 48), (244262, 48), (244263, 48), (244266, 48), (244267, 48), (244270, 48), (244271, 48), (244274, 48), (244275, 48), (244278, 48), (244279, 48), (244282, 48), (244283, 48), (244286, 48), (244287, 48), (244291, 48), (244295, 48), (244299, 48), (244303, 48), (244307, 48), (244311, 48), (244315, 48), (244319, 48), (244323, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 552, 440, 0, 0, 552, 440, 0, 0, 552, 440, 0, 0, 552, 440, 0, 0, 440, 669, 440, 669, 440, 424, 0, 0, 440, 424, 0, 552, 440, 1218, 1218, 552, 440, 1218, 1218, 552, 440, 1218, 1218, 552, 440, 1218, 1218, 0, 0, 0, 0, 1218, 424, 1218, 1218, 424, 1218, 0, 0, 0, 0, 0, 0, 0, 0, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 0, 0, 0, 0, 1218, 1218, 1218, 424, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 440, 663, 440, 663, 440, 0, 440, 0, 438, 440, 0, 0, 438, 440, 0, 0, 438, 440, 0, 0, 438, 440, 0, 0, 440, 663, 440, 663, 440, 0, 440, 0, 440]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(243999, 0), (244006, 14), (244007, 64), (244014, 22), (244015, 144), (244022, 29), (244023, 191), (244030, 31), (244031, 302), (244055, 180), (244058, 254), (244063, 303), (244099, 7), (244103, 75), (244107, 19), (244111, 132), (244130, 2), (244131, 19), (244134, 47), (244135, 240), (244138, 6), (244139, 73), (244142, 81), (244143, 542), (244163, 18), (244167, 159), (244171, 38), (244175, 220), (244247, 63), (244255, 100), (244262, 26), (244263, 127), (244270, 38), (244271, 170), (244278, 36), (244279, 218), (244286, 46), (244287, 276), (244311, 328), (244319, 441)]

theorem l243999 : P.leaf 18 243999 = 0 := by decide +kernel

theorem l244006 : P.leaf 18 244006 = 14 := by decide +kernel

theorem l244007 : P.leaf 18 244007 = 64 := by decide +kernel

theorem l244014 : P.leaf 18 244014 = 22 := by decide +kernel

theorem l244015 : P.leaf 18 244015 = 144 := by decide +kernel

theorem l244022 : P.leaf 18 244022 = 29 := by decide +kernel

theorem l244023 : P.leaf 18 244023 = 191 := by decide +kernel

theorem l244030 : P.leaf 18 244030 = 31 := by decide +kernel

theorem l244031 : P.leaf 18 244031 = 302 := by decide +kernel

theorem l244055 : P.leaf 18 244055 = 180 := by decide +kernel

theorem l244058 : P.leaf 18 244058 = 254 := by decide +kernel

theorem l244063 : P.leaf 18 244063 = 303 := by decide +kernel

theorem l244099 : P.leaf 18 244099 = 7 := by decide +kernel

theorem l244103 : P.leaf 18 244103 = 75 := by decide +kernel

theorem l244107 : P.leaf 18 244107 = 19 := by decide +kernel

theorem l244111 : P.leaf 18 244111 = 132 := by decide +kernel

theorem l244130 : P.leaf 18 244130 = 2 := by decide +kernel

theorem l244131 : P.leaf 18 244131 = 19 := by decide +kernel

theorem l244134 : P.leaf 18 244134 = 47 := by decide +kernel

theorem l244135 : P.leaf 18 244135 = 240 := by decide +kernel

theorem l244138 : P.leaf 18 244138 = 6 := by decide +kernel

theorem l244139 : P.leaf 18 244139 = 73 := by decide +kernel

theorem l244142 : P.leaf 18 244142 = 81 := by decide +kernel

theorem l244143 : P.leaf 18 244143 = 542 := by decide +kernel

theorem l244163 : P.leaf 18 244163 = 18 := by decide +kernel

theorem l244167 : P.leaf 18 244167 = 159 := by decide +kernel

theorem l244171 : P.leaf 18 244171 = 38 := by decide +kernel

theorem l244175 : P.leaf 18 244175 = 220 := by decide +kernel

theorem l244247 : P.leaf 18 244247 = 63 := by decide +kernel

theorem l244255 : P.leaf 18 244255 = 100 := by decide +kernel

theorem l244262 : P.leaf 18 244262 = 26 := by decide +kernel

theorem l244263 : P.leaf 18 244263 = 127 := by decide +kernel

theorem l244270 : P.leaf 18 244270 = 38 := by decide +kernel

theorem l244271 : P.leaf 18 244271 = 170 := by decide +kernel

theorem l244278 : P.leaf 18 244278 = 36 := by decide +kernel

theorem l244279 : P.leaf 18 244279 = 218 := by decide +kernel

theorem l244286 : P.leaf 18 244286 = 46 := by decide +kernel

theorem l244287 : P.leaf 18 244287 = 276 := by decide +kernel

theorem l244311 : P.leaf 18 244311 = 328 := by decide +kernel

theorem l244319 : P.leaf 18 244319 = 441 := by decide +kernel

theorem segOK : checkSeg 20 perms 243999 244326 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 237792 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 243999 244326 6048 237792 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l243999 (.cons l244006 (.cons l244007 (.cons l244014 (.cons l244015 (.cons l244022 (.cons l244023 (.cons l244030 (.cons l244031 (.cons l244055 (.cons l244058 (.cons l244063 (.cons l244099 (.cons l244103 (.cons l244107 (.cons l244111 (.cons l244130 (.cons l244131 (.cons l244134 (.cons l244135 (.cons l244138 (.cons l244139 (.cons l244142 (.cons l244143 (.cons l244163 (.cons l244167 (.cons l244171 (.cons l244175 (.cons l244247 (.cons l244255 (.cons l244262 (.cons l244263 (.cons l244270 (.cons l244271 (.cons l244278 (.cons l244279 (.cons l244286 (.cons l244287 (.cons l244311 (.cons l244319 (.nil))))))))))))))))))))))))))))))))))))))))))

end S84

end RACert.S0N3.C0
