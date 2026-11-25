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

namespace S23

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(95131, 48), (95133, 48), (95134, 48), (95135, 48), (95141, 48), (95142, 48), (95143, 48), (95145, 48), (95146, 48), (95147, 48), (95149, 48), (95150, 48), (95151, 48), (95156, 24), (95157, 48), (95158, 48), (95159, 48), (95161, 48), (95162, 48), (95163, 48), (95164, 48), (95165, 48), (95166, 48), (95167, 48), (95171, 16), (95175, 48), (95179, 48), (95183, 48), (95189, 48), (95190, 48), (95191, 48), (95193, 48), (95194, 48), (95195, 48), (95197, 48), (95198, 48), (95199, 48), (95205, 48), (95206, 48), (95207, 48), (95209, 48), (95210, 48), (95211, 48), (95213, 48), (95214, 48), (95215, 48), (95221, 48), (95222, 48), (95223, 48), (95225, 48), (95226, 48), (95227, 48), (95228, 24), (95229, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 628, 0, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 427, 628, 0, 0, 439, 0, 0, 628, 628, 0, 0, 0, 0, 0, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 439, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(95131, 32), (95134, 28), (95135, 40), (95142, 12), (95143, 36), (95146, 40), (95147, 72), (95150, 48), (95151, 84), (95158, 16), (95159, 88), (95162, 48), (95163, 104), (95166, 64), (95167, 124), (95171, 1), (95175, 8), (95179, 12), (95183, 28), (95189, 30), (95190, 35), (95191, 70), (95194, 32), (95195, 48), (95197, 72), (95198, 164), (95199, 124), (95206, 35), (95207, 62), (95210, 72), (95211, 120), (95214, 142), (95215, 228), (95221, 120), (95222, 136), (95223, 208), (95226, 96), (95227, 168), (95228, 64), (95229, 240)]

theorem l95131 : P.leaf 18 95131 = 32 := by decide +kernel

theorem l95134 : P.leaf 18 95134 = 28 := by decide +kernel

theorem l95135 : P.leaf 18 95135 = 40 := by decide +kernel

theorem l95142 : P.leaf 18 95142 = 12 := by decide +kernel

theorem l95143 : P.leaf 18 95143 = 36 := by decide +kernel

theorem l95146 : P.leaf 18 95146 = 40 := by decide +kernel

theorem l95147 : P.leaf 18 95147 = 72 := by decide +kernel

theorem l95150 : P.leaf 18 95150 = 48 := by decide +kernel

theorem l95151 : P.leaf 18 95151 = 84 := by decide +kernel

theorem l95158 : P.leaf 18 95158 = 16 := by decide +kernel

theorem l95159 : P.leaf 18 95159 = 88 := by decide +kernel

theorem l95162 : P.leaf 18 95162 = 48 := by decide +kernel

theorem l95163 : P.leaf 18 95163 = 104 := by decide +kernel

theorem l95166 : P.leaf 18 95166 = 64 := by decide +kernel

theorem l95167 : P.leaf 18 95167 = 124 := by decide +kernel

theorem l95171 : P.leaf 18 95171 = 1 := by decide +kernel

theorem l95175 : P.leaf 18 95175 = 8 := by decide +kernel

theorem l95179 : P.leaf 18 95179 = 12 := by decide +kernel

theorem l95183 : P.leaf 18 95183 = 28 := by decide +kernel

theorem l95189 : P.leaf 18 95189 = 30 := by decide +kernel

theorem l95190 : P.leaf 18 95190 = 35 := by decide +kernel

theorem l95191 : P.leaf 18 95191 = 70 := by decide +kernel

theorem l95194 : P.leaf 18 95194 = 32 := by decide +kernel

theorem l95195 : P.leaf 18 95195 = 48 := by decide +kernel

theorem l95197 : P.leaf 18 95197 = 72 := by decide +kernel

theorem l95198 : P.leaf 18 95198 = 164 := by decide +kernel

theorem l95199 : P.leaf 18 95199 = 124 := by decide +kernel

theorem l95206 : P.leaf 18 95206 = 35 := by decide +kernel

theorem l95207 : P.leaf 18 95207 = 62 := by decide +kernel

theorem l95210 : P.leaf 18 95210 = 72 := by decide +kernel

theorem l95211 : P.leaf 18 95211 = 120 := by decide +kernel

theorem l95214 : P.leaf 18 95214 = 142 := by decide +kernel

theorem l95215 : P.leaf 18 95215 = 228 := by decide +kernel

theorem l95221 : P.leaf 18 95221 = 120 := by decide +kernel

theorem l95222 : P.leaf 18 95222 = 136 := by decide +kernel

theorem l95223 : P.leaf 18 95223 = 208 := by decide +kernel

theorem l95226 : P.leaf 18 95226 = 96 := by decide +kernel

theorem l95227 : P.leaf 18 95227 = 168 := by decide +kernel

theorem l95228 : P.leaf 18 95228 = 64 := by decide +kernel

theorem l95229 : P.leaf 18 95229 = 240 := by decide +kernel

theorem segOK : checkSeg 20 perms 95131 95230 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 149680 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 95131 95230 2512 149680 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l95131 (.cons l95134 (.cons l95135 (.cons l95142 (.cons l95143 (.cons l95146 (.cons l95147 (.cons l95150 (.cons l95151 (.cons l95158 (.cons l95159 (.cons l95162 (.cons l95163 (.cons l95166 (.cons l95167 (.cons l95171 (.cons l95175 (.cons l95179 (.cons l95183 (.cons l95189 (.cons l95190 (.cons l95191 (.cons l95194 (.cons l95195 (.cons l95197 (.cons l95198 (.cons l95199 (.cons l95206 (.cons l95207 (.cons l95210 (.cons l95211 (.cons l95214 (.cons l95215 (.cons l95221 (.cons l95222 (.cons l95223 (.cons l95226 (.cons l95227 (.cons l95228 (.cons l95229 (.nil))))))))))))))))))))))))))))))))))))))))))

end S23

end RACert.S0N3.C0
