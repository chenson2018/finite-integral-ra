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

namespace S123

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(517023, 24), (517029, 24), (517030, 24), (517031, 24), (517033, 24), (517034, 24), (517035, 24), (517037, 24), (517038, 24), (517039, 24), (517044, 12), (517045, 24), (517046, 24), (517047, 24), (517049, 24), (517050, 24), (517051, 24), (517052, 24), (517053, 24), (517054, 24), (517055, 24), (517059, 8), (517063, 24), (517067, 24), (517071, 24), (517077, 24), (517078, 24), (517079, 24), (517081, 24), (517082, 24), (517083, 24), (517085, 24), (517086, 24), (517087, 24), (517093, 24), (517094, 24), (517095, 24), (517097, 24), (517098, 24), (517099, 24), (517101, 24), (517102, 24), (517103, 24), (517109, 24), (517110, 24), (517111, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(517023, 856), (517030, 197), (517031, 204), (517034, 280), (517035, 280), (517038, 560), (517039, 560), (517044, 52), (517045, 188), (517046, 484), (517047, 484), (517049, 136), (517050, 384), (517051, 400), (517052, 288), (517053, 312), (517054, 768), (517055, 856), (517059, 729), (517063, 1300), (517067, 872), (517071, 1648), (517077, 829), (517078, 2092), (517079, 2834), (517081, 494), (517082, 1060), (517083, 1712), (517085, 1065), (517086, 2527), (517087, 4511), (517094, 1487), (517095, 1519), (517098, 1072), (517099, 1080), (517102, 2150), (517103, 2150), (517109, 963), (517110, 3043), (517111, 3253)]

theorem l517023 : P.leaf 18 517023 = 856 := by decide +kernel

theorem l517030 : P.leaf 18 517030 = 197 := by decide +kernel

theorem l517031 : P.leaf 18 517031 = 204 := by decide +kernel

theorem l517034 : P.leaf 18 517034 = 280 := by decide +kernel

theorem l517035 : P.leaf 18 517035 = 280 := by decide +kernel

theorem l517038 : P.leaf 18 517038 = 560 := by decide +kernel

theorem l517039 : P.leaf 18 517039 = 560 := by decide +kernel

theorem l517044 : P.leaf 18 517044 = 52 := by decide +kernel

theorem l517045 : P.leaf 18 517045 = 188 := by decide +kernel

theorem l517046 : P.leaf 18 517046 = 484 := by decide +kernel

theorem l517047 : P.leaf 18 517047 = 484 := by decide +kernel

theorem l517049 : P.leaf 18 517049 = 136 := by decide +kernel

theorem l517050 : P.leaf 18 517050 = 384 := by decide +kernel

theorem l517051 : P.leaf 18 517051 = 400 := by decide +kernel

theorem l517052 : P.leaf 18 517052 = 288 := by decide +kernel

theorem l517053 : P.leaf 18 517053 = 312 := by decide +kernel

theorem l517054 : P.leaf 18 517054 = 768 := by decide +kernel

theorem l517055 : P.leaf 18 517055 = 856 := by decide +kernel

theorem l517059 : P.leaf 18 517059 = 729 := by decide +kernel

theorem l517063 : P.leaf 18 517063 = 1300 := by decide +kernel

theorem l517067 : P.leaf 18 517067 = 872 := by decide +kernel

theorem l517071 : P.leaf 18 517071 = 1648 := by decide +kernel

theorem l517077 : P.leaf 18 517077 = 829 := by decide +kernel

theorem l517078 : P.leaf 18 517078 = 2092 := by decide +kernel

theorem l517079 : P.leaf 18 517079 = 2834 := by decide +kernel

theorem l517081 : P.leaf 18 517081 = 494 := by decide +kernel

theorem l517082 : P.leaf 18 517082 = 1060 := by decide +kernel

theorem l517083 : P.leaf 18 517083 = 1712 := by decide +kernel

theorem l517085 : P.leaf 18 517085 = 1065 := by decide +kernel

theorem l517086 : P.leaf 18 517086 = 2527 := by decide +kernel

theorem l517087 : P.leaf 18 517087 = 4511 := by decide +kernel

theorem l517094 : P.leaf 18 517094 = 1487 := by decide +kernel

theorem l517095 : P.leaf 18 517095 = 1519 := by decide +kernel

theorem l517098 : P.leaf 18 517098 = 1072 := by decide +kernel

theorem l517099 : P.leaf 18 517099 = 1080 := by decide +kernel

theorem l517102 : P.leaf 18 517102 = 2150 := by decide +kernel

theorem l517103 : P.leaf 18 517103 = 2150 := by decide +kernel

theorem l517109 : P.leaf 18 517109 = 963 := by decide +kernel

theorem l517110 : P.leaf 18 517110 = 3043 := by decide +kernel

theorem l517111 : P.leaf 18 517111 = 3253 := by decide +kernel

theorem segOK : checkSeg 20 perms 517023 517113 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1084008 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 517023 517113 1076 1084008 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l517023 (.cons l517030 (.cons l517031 (.cons l517034 (.cons l517035 (.cons l517038 (.cons l517039 (.cons l517044 (.cons l517045 (.cons l517046 (.cons l517047 (.cons l517049 (.cons l517050 (.cons l517051 (.cons l517052 (.cons l517053 (.cons l517054 (.cons l517055 (.cons l517059 (.cons l517063 (.cons l517067 (.cons l517071 (.cons l517077 (.cons l517078 (.cons l517079 (.cons l517081 (.cons l517082 (.cons l517083 (.cons l517085 (.cons l517086 (.cons l517087 (.cons l517094 (.cons l517095 (.cons l517098 (.cons l517099 (.cons l517102 (.cons l517103 (.cons l517109 (.cons l517110 (.cons l517111 (.nil))))))))))))))))))))))))))))))))))))))))))

end S123

end RACert.S0N3.C0
