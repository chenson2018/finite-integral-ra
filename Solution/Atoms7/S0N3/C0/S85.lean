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

namespace S85

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(244326, 48), (244327, 48), (244330, 24), (244331, 48), (244334, 48), (244335, 48), (244338, 48), (244339, 48), (244342, 48), (244343, 48), (244346, 48), (244347, 48), (244350, 48), (244351, 48), (244355, 48), (244359, 48), (244363, 48), (244367, 48), (244371, 48), (244375, 48), (244379, 48), (244383, 48), (244387, 48), (244390, 24), (244391, 48), (244395, 48), (244398, 48), (244399, 48), (244402, 48), (244403, 48), (244406, 48), (244407, 48), (244410, 48), (244411, 48), (244414, 48), (244415, 48), (244419, 48), (244423, 48), (244427, 48), (244431, 48), (244435, 48), (244439, 48), (244443, 48), (244447, 48), (244451, 48), (244455, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 438, 440, 0, 0, 438, 440, 0, 0, 438, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(244326, 68), (244327, 416), (244334, 99), (244335, 523), (244342, 128), (244343, 810), (244350, 156), (244351, 976), (244355, 6), (244359, 58), (244363, 18), (244367, 58), (244371, 34), (244375, 459), (244379, 208), (244383, 865), (244387, 62), (244390, 248), (244391, 715), (244395, 272), (244398, 330), (244399, 1053), (244402, 96), (244403, 114), (244406, 478), (244407, 1378), (244410, 162), (244411, 504), (244414, 596), (244415, 1938), (244419, 7), (244423, 72), (244427, 22), (244431, 72), (244435, 70), (244439, 974), (244443, 280), (244447, 1330), (244451, 98), (244455, 1194)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 244326 244459 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 807504 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 244326 244459 2160 807504 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S85

end RACert.S0N3.C0
