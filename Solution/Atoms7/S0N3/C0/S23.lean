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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 95131 95230 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 149680 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 95131 95230 2512 149680 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S23

end RACert.S0N3.C0
