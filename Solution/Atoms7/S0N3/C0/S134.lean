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

namespace S134

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(522239, 48), (522646, 8), (522647, 48), (522655, 24), (522679, 24), (522686, 48), (522687, 48), (522742, 24), (522743, 48), (522751, 24), (523167, 48), (523199, 24), (523223, 16), (523231, 48), (523262, 24), (523263, 48), (524287, 8), (1044480, 1), (1044481, 12), (1044483, 6), (1044485, 12), (1044487, 12), (1044495, 3), (1044497, 6), (1044498, 6), (1044499, 12), (1044500, 24), (1044501, 24), (1044502, 24), (1044503, 24), (1044508, 12), (1044509, 12), (1044510, 12), (1044511, 12), (1044531, 3), (1044532, 12), (1044533, 24), (1044535, 12), (1044540, 6), (1044541, 12), (1044543, 6), (1044560, 12), (1044561, 24), (1044562, 24), (1044563, 24), (1044565, 12), (1044566, 24), (1044567, 24), (1044570, 12), (1044571, 24), (1044575, 12), (1044592, 12), (1044593, 24), (1044595, 12), (1044596, 12), (1044597, 24), (1044599, 12), (1044600, 12), (1044601, 24), (1044603, 12), (1044604, 12), (1044605, 24), (1044607, 12), (1044720, 3), (1044721, 12), (1044723, 6), (1044725, 12), (1044727, 12), (1044735, 3), (1044741, 24), (1044742, 24), (1044743, 24), (1044749, 24), (1044751, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 434, 434, 1218, 1218, 1218, 434, 434, 434, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 434, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 1218, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(522239, 22289), (522646, 2444), (522647, 4900), (522655, 11152), (522679, 7831), (522686, 8391), (522687, 17574), (522742, 8023), (522743, 11049), (522751, 20474), (523167, 16659), (523199, 31425), (523223, 12921), (523231, 22797), (523262, 21937), (523263, 36385), (524287, 54225), (1044592, 217), (1044593, 834), (1044595, 1591), (1044596, 1737), (1044597, 2520), (1044599, 3956), (1044600, 1442), (1044601, 1995), (1044603, 3410), (1044604, 3862), (1044605, 4256), (1044607, 9843), (1044720, 694), (1044721, 3442), (1044723, 6068), (1044725, 4252), (1044727, 6635), (1044735, 17670), (1044741, 100), (1044742, 134), (1044743, 236), (1044749, 216), (1044751, 272)]

theorem l522239 : P.leaf 18 522239 = 22289 := by decide +kernel

theorem l522646 : P.leaf 18 522646 = 2444 := by decide +kernel

theorem l522647 : P.leaf 18 522647 = 4900 := by decide +kernel

theorem l522655 : P.leaf 18 522655 = 11152 := by decide +kernel

theorem l522679 : P.leaf 18 522679 = 7831 := by decide +kernel

theorem l522686 : P.leaf 18 522686 = 8391 := by decide +kernel

theorem l522687 : P.leaf 18 522687 = 17574 := by decide +kernel

theorem l522742 : P.leaf 18 522742 = 8023 := by decide +kernel

theorem l522743 : P.leaf 18 522743 = 11049 := by decide +kernel

theorem l522751 : P.leaf 18 522751 = 20474 := by decide +kernel

theorem l523167 : P.leaf 18 523167 = 16659 := by decide +kernel

theorem l523199 : P.leaf 18 523199 = 31425 := by decide +kernel

theorem l523223 : P.leaf 18 523223 = 12921 := by decide +kernel

theorem l523231 : P.leaf 18 523231 = 22797 := by decide +kernel

theorem l523262 : P.leaf 18 523262 = 21937 := by decide +kernel

theorem l523263 : P.leaf 18 523263 = 36385 := by decide +kernel

theorem l524287 : P.leaf 18 524287 = 54225 := by decide +kernel

theorem l1044592 : P.leaf 18 1044592 = 217 := by decide +kernel

theorem l1044593 : P.leaf 18 1044593 = 834 := by decide +kernel

theorem l1044595 : P.leaf 18 1044595 = 1591 := by decide +kernel

theorem l1044596 : P.leaf 18 1044596 = 1737 := by decide +kernel

theorem l1044597 : P.leaf 18 1044597 = 2520 := by decide +kernel

theorem l1044599 : P.leaf 18 1044599 = 3956 := by decide +kernel

theorem l1044600 : P.leaf 18 1044600 = 1442 := by decide +kernel

theorem l1044601 : P.leaf 18 1044601 = 1995 := by decide +kernel

theorem l1044603 : P.leaf 18 1044603 = 3410 := by decide +kernel

theorem l1044604 : P.leaf 18 1044604 = 3862 := by decide +kernel

theorem l1044605 : P.leaf 18 1044605 = 4256 := by decide +kernel

theorem l1044607 : P.leaf 18 1044607 = 9843 := by decide +kernel

theorem l1044720 : P.leaf 18 1044720 = 694 := by decide +kernel

theorem l1044721 : P.leaf 18 1044721 = 3442 := by decide +kernel

theorem l1044723 : P.leaf 18 1044723 = 6068 := by decide +kernel

theorem l1044725 : P.leaf 18 1044725 = 4252 := by decide +kernel

theorem l1044727 : P.leaf 18 1044727 = 6635 := by decide +kernel

theorem l1044735 : P.leaf 18 1044735 = 17670 := by decide +kernel

theorem l1044741 : P.leaf 18 1044741 = 100 := by decide +kernel

theorem l1044742 : P.leaf 18 1044742 = 134 := by decide +kernel

theorem l1044743 : P.leaf 18 1044743 = 236 := by decide +kernel

theorem l1044749 : P.leaf 18 1044749 = 216 := by decide +kernel

theorem l1044751 : P.leaf 18 1044751 = 272 := by decide +kernel

theorem segOK : checkSeg 20 perms 522239 1044757 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 10628800 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 522239 1044757 1389 10628800 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l522239 (.cons l522646 (.cons l522647 (.cons l522655 (.cons l522679 (.cons l522686 (.cons l522687 (.cons l522742 (.cons l522743 (.cons l522751 (.cons l523167 (.cons l523199 (.cons l523223 (.cons l523231 (.cons l523262 (.cons l523263 (.cons l524287 (.cons l1044592 (.cons l1044593 (.cons l1044595 (.cons l1044596 (.cons l1044597 (.cons l1044599 (.cons l1044600 (.cons l1044601 (.cons l1044603 (.cons l1044604 (.cons l1044605 (.cons l1044607 (.cons l1044720 (.cons l1044721 (.cons l1044723 (.cons l1044725 (.cons l1044727 (.cons l1044735 (.cons l1044741 (.cons l1044742 (.cons l1044743 (.cons l1044749 (.cons l1044751 (.nil))))))))))))))))))))))))))))))))))))))))))

end S134

end RACert.S0N3.C0
