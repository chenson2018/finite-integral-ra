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

namespace S102

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439019, 48), (439021, 48), (439022, 48), (439023, 48), (439024, 48), (439025, 48), (439026, 48), (439027, 48), (439028, 48), (439029, 48), (439030, 48), (439031, 48), (439032, 48), (439033, 48), (439034, 48), (439035, 48), (439036, 48), (439037, 48), (439038, 48), (439039, 48), (439055, 48), (439069, 48), (439070, 24), (439071, 48), (439085, 24), (439087, 48), (439103, 24), (439111, 48), (439115, 48), (439119, 48), (439125, 48), (439126, 48), (439127, 48), (439129, 48), (439130, 48), (439131, 48), (439133, 48), (439134, 48), (439135, 48), (439141, 48), (439142, 48), (439143, 48), (439145, 48), (439146, 48), (439147, 48), (439149, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 0, 0, 0, 0, 502, 0, 0, 439, 0, 0, 502]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439019, 368), (439022, 235), (439023, 1239), (439024, 19), (439025, 68), (439026, 25), (439027, 516), (439028, 84), (439029, 726), (439030, 138), (439031, 1396), (439032, 52), (439033, 227), (439034, 163), (439035, 856), (439036, 550), (439037, 1722), (439038, 634), (439039, 3626), (439055, 80), (439069, 69), (439070, 25), (439071, 122), (439087, 138), (439103, 196), (439111, 89), (439115, 65), (439119, 136), (439125, 62), (439126, 16), (439127, 142), (439129, 17), (439131, 65), (439133, 142), (439134, 52), (439135, 256), (439142, 60), (439143, 168), (439146, 17), (439147, 118)]

theorem l439019 : P.leaf 18 439019 = 368 := by decide +kernel

theorem l439022 : P.leaf 18 439022 = 235 := by decide +kernel

theorem l439023 : P.leaf 18 439023 = 1239 := by decide +kernel

theorem l439024 : P.leaf 18 439024 = 19 := by decide +kernel

theorem l439025 : P.leaf 18 439025 = 68 := by decide +kernel

theorem l439026 : P.leaf 18 439026 = 25 := by decide +kernel

theorem l439027 : P.leaf 18 439027 = 516 := by decide +kernel

theorem l439028 : P.leaf 18 439028 = 84 := by decide +kernel

theorem l439029 : P.leaf 18 439029 = 726 := by decide +kernel

theorem l439030 : P.leaf 18 439030 = 138 := by decide +kernel

theorem l439031 : P.leaf 18 439031 = 1396 := by decide +kernel

theorem l439032 : P.leaf 18 439032 = 52 := by decide +kernel

theorem l439033 : P.leaf 18 439033 = 227 := by decide +kernel

theorem l439034 : P.leaf 18 439034 = 163 := by decide +kernel

theorem l439035 : P.leaf 18 439035 = 856 := by decide +kernel

theorem l439036 : P.leaf 18 439036 = 550 := by decide +kernel

theorem l439037 : P.leaf 18 439037 = 1722 := by decide +kernel

theorem l439038 : P.leaf 18 439038 = 634 := by decide +kernel

theorem l439039 : P.leaf 18 439039 = 3626 := by decide +kernel

theorem l439055 : P.leaf 18 439055 = 80 := by decide +kernel

theorem l439069 : P.leaf 18 439069 = 69 := by decide +kernel

theorem l439070 : P.leaf 18 439070 = 25 := by decide +kernel

theorem l439071 : P.leaf 18 439071 = 122 := by decide +kernel

theorem l439087 : P.leaf 18 439087 = 138 := by decide +kernel

theorem l439103 : P.leaf 18 439103 = 196 := by decide +kernel

theorem l439111 : P.leaf 18 439111 = 89 := by decide +kernel

theorem l439115 : P.leaf 18 439115 = 65 := by decide +kernel

theorem l439119 : P.leaf 18 439119 = 136 := by decide +kernel

theorem l439125 : P.leaf 18 439125 = 62 := by decide +kernel

theorem l439126 : P.leaf 18 439126 = 16 := by decide +kernel

theorem l439127 : P.leaf 18 439127 = 142 := by decide +kernel

theorem l439129 : P.leaf 18 439129 = 17 := by decide +kernel

theorem l439131 : P.leaf 18 439131 = 65 := by decide +kernel

theorem l439133 : P.leaf 18 439133 = 142 := by decide +kernel

theorem l439134 : P.leaf 18 439134 = 52 := by decide +kernel

theorem l439135 : P.leaf 18 439135 = 256 := by decide +kernel

theorem l439142 : P.leaf 18 439142 = 60 := by decide +kernel

theorem l439143 : P.leaf 18 439143 = 168 := by decide +kernel

theorem l439146 : P.leaf 18 439146 = 17 := by decide +kernel

theorem l439147 : P.leaf 18 439147 = 118 := by decide +kernel

theorem segOK : checkSeg 20 perms 439019 439150 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 699288 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439019 439150 2136 699288 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l439019 (.cons l439022 (.cons l439023 (.cons l439024 (.cons l439025 (.cons l439026 (.cons l439027 (.cons l439028 (.cons l439029 (.cons l439030 (.cons l439031 (.cons l439032 (.cons l439033 (.cons l439034 (.cons l439035 (.cons l439036 (.cons l439037 (.cons l439038 (.cons l439039 (.cons l439055 (.cons l439069 (.cons l439070 (.cons l439071 (.cons l439087 (.cons l439103 (.cons l439111 (.cons l439115 (.cons l439119 (.cons l439125 (.cons l439126 (.cons l439127 (.cons l439129 (.cons l439131 (.cons l439133 (.cons l439134 (.cons l439135 (.cons l439142 (.cons l439143 (.cons l439146 (.cons l439147 (.nil))))))))))))))))))))))))))))))))))))))))))

end S102

end RACert.S0N3.C0
