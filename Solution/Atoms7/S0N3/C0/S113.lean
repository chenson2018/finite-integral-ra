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

namespace S113

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(456647, 48), (456652, 24), (456653, 48), (456655, 24), (456656, 48), (456657, 48), (456658, 48), (456659, 48), (456660, 48), (456661, 48), (456662, 48), (456663, 48), (456664, 48), (456665, 48), (456666, 48), (456667, 48), (456668, 48), (456669, 48), (456670, 48), (456671, 48), (456688, 24), (456689, 48), (456691, 24), (456692, 48), (456693, 48), (456694, 48), (456695, 48), (456700, 24), (456701, 48), (456703, 24), (456960, 12), (456961, 48), (456963, 24), (456965, 24), (456966, 24), (456967, 48), (456975, 12), (456976, 48), (456977, 48), (456978, 48), (456979, 48), (456980, 48), (456981, 48), (456982, 48), (456983, 48), (456984, 48), (456985, 48), (456986, 48), (456987, 48), (456988, 48), (456989, 48), (456990, 48), (456991, 48), (457008, 24), (457009, 48), (457011, 24), (457012, 48), (457013, 48), (457014, 48), (457015, 48), (457020, 24), (457021, 48), (457023, 24), (457040, 24), (457041, 48), (457042, 48), (457043, 48), (457045, 24), (457046, 48), (457047, 48), (457050, 24), (457051, 48), (457055, 24), (457056, 24), (457057, 48), (457058, 48), (457059, 48), (457061, 48), (457062, 24), (457063, 48), (457065, 24), (457067, 48), (457071, 24), (457072, 48), (457073, 48), (457074, 48), (457075, 48), (457076, 48), (457077, 48), (457078, 48), (457079, 48), (457080, 48), (457081, 48), (457082, 48), (457083, 48), (457084, 48), (457085, 48), (457086, 48), (457087, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 502, 502, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 434, 602, 502, 431, 602, 0, 434, 434, 431, 602, 431, 602, 431, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 434, 602, 602, 602, 602, 602, 0, 0, 0, 550, 650, 550, 650, 0, 550, 0, 550, 650, 0, 502, 439, 650, 650, 502, 0, 0, 439, 650, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(456647, 2133), (456655, 3880), (456657, 246), (456659, 1534), (456661, 1473), (456663, 2827), (456665, 1549), (456667, 2837), (456669, 3427), (456671, 6053), (456688, 122), (456689, 392), (456691, 2980), (456692, 380), (456693, 2338), (456694, 2932), (456695, 6069), (456700, 1992), (456701, 5811), (456703, 14786), (456975, 168), (456989, 348), (456991, 544), (457020, 328), (457021, 471), (457023, 778), (457045, 807), (457047, 1887), (457055, 3842), (457062, 864), (457063, 2070), (457071, 4168), (457076, 346), (457077, 1424), (457078, 1412), (457079, 3683), (457084, 1878), (457085, 3219), (457086, 3221), (457087, 8526)]

theorem l456647 : P.leaf 18 456647 = 2133 := by decide +kernel

theorem l456655 : P.leaf 18 456655 = 3880 := by decide +kernel

theorem l456657 : P.leaf 18 456657 = 246 := by decide +kernel

theorem l456659 : P.leaf 18 456659 = 1534 := by decide +kernel

theorem l456661 : P.leaf 18 456661 = 1473 := by decide +kernel

theorem l456663 : P.leaf 18 456663 = 2827 := by decide +kernel

theorem l456665 : P.leaf 18 456665 = 1549 := by decide +kernel

theorem l456667 : P.leaf 18 456667 = 2837 := by decide +kernel

theorem l456669 : P.leaf 18 456669 = 3427 := by decide +kernel

theorem l456671 : P.leaf 18 456671 = 6053 := by decide +kernel

theorem l456688 : P.leaf 18 456688 = 122 := by decide +kernel

theorem l456689 : P.leaf 18 456689 = 392 := by decide +kernel

theorem l456691 : P.leaf 18 456691 = 2980 := by decide +kernel

theorem l456692 : P.leaf 18 456692 = 380 := by decide +kernel

theorem l456693 : P.leaf 18 456693 = 2338 := by decide +kernel

theorem l456694 : P.leaf 18 456694 = 2932 := by decide +kernel

theorem l456695 : P.leaf 18 456695 = 6069 := by decide +kernel

theorem l456700 : P.leaf 18 456700 = 1992 := by decide +kernel

theorem l456701 : P.leaf 18 456701 = 5811 := by decide +kernel

theorem l456703 : P.leaf 18 456703 = 14786 := by decide +kernel

theorem l456975 : P.leaf 18 456975 = 168 := by decide +kernel

theorem l456989 : P.leaf 18 456989 = 348 := by decide +kernel

theorem l456991 : P.leaf 18 456991 = 544 := by decide +kernel

theorem l457020 : P.leaf 18 457020 = 328 := by decide +kernel

theorem l457021 : P.leaf 18 457021 = 471 := by decide +kernel

theorem l457023 : P.leaf 18 457023 = 778 := by decide +kernel

theorem l457045 : P.leaf 18 457045 = 807 := by decide +kernel

theorem l457047 : P.leaf 18 457047 = 1887 := by decide +kernel

theorem l457055 : P.leaf 18 457055 = 3842 := by decide +kernel

theorem l457062 : P.leaf 18 457062 = 864 := by decide +kernel

theorem l457063 : P.leaf 18 457063 = 2070 := by decide +kernel

theorem l457071 : P.leaf 18 457071 = 4168 := by decide +kernel

theorem l457076 : P.leaf 18 457076 = 346 := by decide +kernel

theorem l457077 : P.leaf 18 457077 = 1424 := by decide +kernel

theorem l457078 : P.leaf 18 457078 = 1412 := by decide +kernel

theorem l457079 : P.leaf 18 457079 = 3683 := by decide +kernel

theorem l457084 : P.leaf 18 457084 = 1878 := by decide +kernel

theorem l457085 : P.leaf 18 457085 = 3219 := by decide +kernel

theorem l457086 : P.leaf 18 457086 = 3221 := by decide +kernel

theorem l457087 : P.leaf 18 457087 = 8526 := by decide +kernel

theorem segOK : checkSeg 20 perms 456647 457200 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4144584 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 456647 457200 4176 4144584 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l456647 (.cons l456655 (.cons l456657 (.cons l456659 (.cons l456661 (.cons l456663 (.cons l456665 (.cons l456667 (.cons l456669 (.cons l456671 (.cons l456688 (.cons l456689 (.cons l456691 (.cons l456692 (.cons l456693 (.cons l456694 (.cons l456695 (.cons l456700 (.cons l456701 (.cons l456703 (.cons l456975 (.cons l456989 (.cons l456991 (.cons l457020 (.cons l457021 (.cons l457023 (.cons l457045 (.cons l457047 (.cons l457055 (.cons l457062 (.cons l457063 (.cons l457071 (.cons l457076 (.cons l457077 (.cons l457078 (.cons l457079 (.cons l457084 (.cons l457085 (.cons l457086 (.cons l457087 (.nil))))))))))))))))))))))))))))))))))))))))))

end S113

end RACert.S0N3.C0
