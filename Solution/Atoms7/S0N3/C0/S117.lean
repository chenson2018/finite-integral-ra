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

namespace S117

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516408, 24), (516409, 24), (516410, 24), (516411, 24), (516412, 24), (516413, 24), (516414, 24), (516415, 24), (516417, 24), (516418, 24), (516419, 24), (516421, 24), (516422, 24), (516423, 24), (516425, 24), (516426, 24), (516427, 24), (516429, 24), (516430, 24), (516431, 24), (516433, 24), (516434, 24), (516435, 24), (516436, 24), (516437, 24), (516438, 24), (516439, 24), (516440, 12), (516441, 24), (516442, 24), (516443, 24), (516444, 24), (516445, 24), (516446, 24), (516447, 24), (516448, 24), (516449, 24), (516450, 24), (516451, 24), (516452, 24), (516453, 24), (516454, 24), (516455, 24), (516456, 24), (516457, 24), (516458, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 419, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 419, 0, 0, 0, 0, 0, 0, 418, 418, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516408, 0), (516409, 0), (516410, 0), (516411, 0), (516412, 65), (516413, 82), (516414, 198), (516415, 216), (516418, 3), (516419, 6), (516421, 6), (516422, 23), (516423, 30), (516426, 0), (516427, 0), (516430, 27), (516431, 32), (516433, 18), (516434, 16), (516435, 82), (516436, 33), (516437, 154), (516438, 189), (516439, 405), (516440, 0), (516441, 0), (516442, 0), (516443, 0), (516444, 90), (516445, 192), (516446, 264), (516447, 435), (516448, 22), (516450, 49), (516451, 65), (516452, 16), (516453, 10), (516454, 242), (516455, 270), (516458, 54)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 516408 516459 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 79056 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516408 516459 1092 79056 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S117

end RACert.S0N3.C0
