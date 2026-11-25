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

namespace S128

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(520586, 48), (520587, 48), (520589, 48), (520590, 48), (520591, 48), (520595, 48), (520596, 24), (520597, 48), (520598, 48), (520599, 48), (520601, 48), (520602, 48), (520603, 48), (520604, 48), (520605, 48), (520606, 48), (520607, 48), (520611, 48), (520612, 48), (520613, 48), (520614, 48), (520615, 48), (520616, 48), (520617, 48), (520618, 48), (520619, 48), (520620, 48), (520621, 48), (520622, 48), (520623, 48), (520627, 48), (520628, 48), (520629, 48), (520630, 48), (520631, 48), (520632, 48), (520633, 48), (520634, 48), (520635, 48), (520636, 48), (520637, 48), (520638, 48), (520639, 48), (520641, 48), (520643, 48), (520645, 48), (520647, 48), (520649, 48), (520651, 48), (520653, 48), (520655, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 502, 0, 0, 502, 502, 0, 0, 502, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 502, 0, 502, 0, 502, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(520586, 66), (520587, 184), (520590, 184), (520591, 224), (520595, 265), (520596, 218), (520597, 517), (520598, 609), (520599, 998), (520601, 580), (520602, 620), (520603, 1153), (520604, 1074), (520605, 1296), (520606, 1580), (520607, 2738), (520611, 86), (520614, 278), (520615, 346), (520618, 534), (520619, 633), (520622, 990), (520623, 1262), (520627, 289), (520628, 330), (520629, 644), (520630, 1044), (520631, 1196), (520632, 300), (520633, 740), (520634, 1148), (520635, 1375), (520636, 1446), (520637, 1534), (520638, 2280), (520639, 3316), (520643, 216), (520647, 400), (520651, 272), (520655, 400)]

theorem l520586 : P.leaf 18 520586 = 66 := by decide +kernel

theorem l520587 : P.leaf 18 520587 = 184 := by decide +kernel

theorem l520590 : P.leaf 18 520590 = 184 := by decide +kernel

theorem l520591 : P.leaf 18 520591 = 224 := by decide +kernel

theorem l520595 : P.leaf 18 520595 = 265 := by decide +kernel

theorem l520596 : P.leaf 18 520596 = 218 := by decide +kernel

theorem l520597 : P.leaf 18 520597 = 517 := by decide +kernel

theorem l520598 : P.leaf 18 520598 = 609 := by decide +kernel

theorem l520599 : P.leaf 18 520599 = 998 := by decide +kernel

theorem l520601 : P.leaf 18 520601 = 580 := by decide +kernel

theorem l520602 : P.leaf 18 520602 = 620 := by decide +kernel

theorem l520603 : P.leaf 18 520603 = 1153 := by decide +kernel

theorem l520604 : P.leaf 18 520604 = 1074 := by decide +kernel

theorem l520605 : P.leaf 18 520605 = 1296 := by decide +kernel

theorem l520606 : P.leaf 18 520606 = 1580 := by decide +kernel

theorem l520607 : P.leaf 18 520607 = 2738 := by decide +kernel

theorem l520611 : P.leaf 18 520611 = 86 := by decide +kernel

theorem l520614 : P.leaf 18 520614 = 278 := by decide +kernel

theorem l520615 : P.leaf 18 520615 = 346 := by decide +kernel

theorem l520618 : P.leaf 18 520618 = 534 := by decide +kernel

theorem l520619 : P.leaf 18 520619 = 633 := by decide +kernel

theorem l520622 : P.leaf 18 520622 = 990 := by decide +kernel

theorem l520623 : P.leaf 18 520623 = 1262 := by decide +kernel

theorem l520627 : P.leaf 18 520627 = 289 := by decide +kernel

theorem l520628 : P.leaf 18 520628 = 330 := by decide +kernel

theorem l520629 : P.leaf 18 520629 = 644 := by decide +kernel

theorem l520630 : P.leaf 18 520630 = 1044 := by decide +kernel

theorem l520631 : P.leaf 18 520631 = 1196 := by decide +kernel

theorem l520632 : P.leaf 18 520632 = 300 := by decide +kernel

theorem l520633 : P.leaf 18 520633 = 740 := by decide +kernel

theorem l520634 : P.leaf 18 520634 = 1148 := by decide +kernel

theorem l520635 : P.leaf 18 520635 = 1375 := by decide +kernel

theorem l520636 : P.leaf 18 520636 = 1446 := by decide +kernel

theorem l520637 : P.leaf 18 520637 = 1534 := by decide +kernel

theorem l520638 : P.leaf 18 520638 = 2280 := by decide +kernel

theorem l520639 : P.leaf 18 520639 = 3316 := by decide +kernel

theorem l520643 : P.leaf 18 520643 = 216 := by decide +kernel

theorem l520647 : P.leaf 18 520647 = 400 := by decide +kernel

theorem l520651 : P.leaf 18 520651 = 272 := by decide +kernel

theorem l520655 : P.leaf 18 520655 = 400 := by decide +kernel

theorem segOK : checkSeg 20 perms 520586 520657 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1596288 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 520586 520657 2424 1596288 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l520586 (.cons l520587 (.cons l520590 (.cons l520591 (.cons l520595 (.cons l520596 (.cons l520597 (.cons l520598 (.cons l520599 (.cons l520601 (.cons l520602 (.cons l520603 (.cons l520604 (.cons l520605 (.cons l520606 (.cons l520607 (.cons l520611 (.cons l520614 (.cons l520615 (.cons l520618 (.cons l520619 (.cons l520622 (.cons l520623 (.cons l520627 (.cons l520628 (.cons l520629 (.cons l520630 (.cons l520631 (.cons l520632 (.cons l520633 (.cons l520634 (.cons l520635 (.cons l520636 (.cons l520637 (.cons l520638 (.cons l520639 (.cons l520643 (.cons l520647 (.cons l520651 (.cons l520655 (.nil))))))))))))))))))))))))))))))))))))))))))

end S128

end RACert.S0N3.C0
