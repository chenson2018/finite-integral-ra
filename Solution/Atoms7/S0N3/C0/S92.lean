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

namespace S92

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(259445, 48), (259446, 48), (259447, 48), (259449, 48), (259450, 48), (259451, 48), (259453, 48), (259454, 48), (259455, 48), (259459, 48), (259463, 48), (259467, 48), (259471, 48), (259474, 48), (259475, 48), (259477, 24), (259478, 48), (259479, 48), (259482, 48), (259483, 48), (259485, 48), (259486, 48), (259487, 48), (259489, 48), (259491, 48), (259493, 48), (259494, 24), (259495, 48), (259497, 48), (259499, 48), (259501, 48), (259502, 48), (259503, 48), (259505, 48), (259506, 48), (259507, 48), (259509, 48), (259510, 48), (259511, 48), (259513, 48), (259514, 48), (259515, 48), (259517, 48), (259518, 48), (259519, 48), (259523, 48), (259527, 48), (259531, 48), (259535, 48), (259538, 48), (259539, 48), (259542, 48), (259543, 48), (259546, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 439, 438, 440, 0, 0, 0, 0, 0, 0, 0, 550, 0, 0, 550, 0, 550, 0, 0, 550, 0, 502, 0, 502, 0, 0, 502, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 550, 0, 550, 0, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(259445, 904), (259446, 777), (259447, 2038), (259453, 1156), (259454, 992), (259455, 2754), (259459, 40), (259463, 192), (259467, 192), (259471, 232), (259475, 208), (259477, 652), (259479, 1184), (259483, 1224), (259485, 1434), (259487, 2586), (259491, 246), (259494, 499), (259495, 1271), (259499, 1379), (259502, 1300), (259503, 2950), (259505, 222), (259506, 200), (259507, 418), (259509, 1308), (259510, 1006), (259511, 2414), (259513, 1142), (259514, 981), (259515, 2160), (259517, 2150), (259518, 1838), (259519, 4728), (259523, 80), (259527, 300), (259531, 220), (259535, 300), (259539, 548), (259543, 2625)]

theorem l259445 : P.leaf 18 259445 = 904 := by decide +kernel

theorem l259446 : P.leaf 18 259446 = 777 := by decide +kernel

theorem l259447 : P.leaf 18 259447 = 2038 := by decide +kernel

theorem l259453 : P.leaf 18 259453 = 1156 := by decide +kernel

theorem l259454 : P.leaf 18 259454 = 992 := by decide +kernel

theorem l259455 : P.leaf 18 259455 = 2754 := by decide +kernel

theorem l259459 : P.leaf 18 259459 = 40 := by decide +kernel

theorem l259463 : P.leaf 18 259463 = 192 := by decide +kernel

theorem l259467 : P.leaf 18 259467 = 192 := by decide +kernel

theorem l259471 : P.leaf 18 259471 = 232 := by decide +kernel

theorem l259475 : P.leaf 18 259475 = 208 := by decide +kernel

theorem l259477 : P.leaf 18 259477 = 652 := by decide +kernel

theorem l259479 : P.leaf 18 259479 = 1184 := by decide +kernel

theorem l259483 : P.leaf 18 259483 = 1224 := by decide +kernel

theorem l259485 : P.leaf 18 259485 = 1434 := by decide +kernel

theorem l259487 : P.leaf 18 259487 = 2586 := by decide +kernel

theorem l259491 : P.leaf 18 259491 = 246 := by decide +kernel

theorem l259494 : P.leaf 18 259494 = 499 := by decide +kernel

theorem l259495 : P.leaf 18 259495 = 1271 := by decide +kernel

theorem l259499 : P.leaf 18 259499 = 1379 := by decide +kernel

theorem l259502 : P.leaf 18 259502 = 1300 := by decide +kernel

theorem l259503 : P.leaf 18 259503 = 2950 := by decide +kernel

theorem l259505 : P.leaf 18 259505 = 222 := by decide +kernel

theorem l259506 : P.leaf 18 259506 = 200 := by decide +kernel

theorem l259507 : P.leaf 18 259507 = 418 := by decide +kernel

theorem l259509 : P.leaf 18 259509 = 1308 := by decide +kernel

theorem l259510 : P.leaf 18 259510 = 1006 := by decide +kernel

theorem l259511 : P.leaf 18 259511 = 2414 := by decide +kernel

theorem l259513 : P.leaf 18 259513 = 1142 := by decide +kernel

theorem l259514 : P.leaf 18 259514 = 981 := by decide +kernel

theorem l259515 : P.leaf 18 259515 = 2160 := by decide +kernel

theorem l259517 : P.leaf 18 259517 = 2150 := by decide +kernel

theorem l259518 : P.leaf 18 259518 = 1838 := by decide +kernel

theorem l259519 : P.leaf 18 259519 = 4728 := by decide +kernel

theorem l259523 : P.leaf 18 259523 = 80 := by decide +kernel

theorem l259527 : P.leaf 18 259527 = 300 := by decide +kernel

theorem l259531 : P.leaf 18 259531 = 220 := by decide +kernel

theorem l259535 : P.leaf 18 259535 = 300 := by decide +kernel

theorem l259539 : P.leaf 18 259539 = 548 := by decide +kernel

theorem l259543 : P.leaf 18 259543 = 2625 := by decide +kernel

theorem segOK : checkSeg 20 perms 259445 259547 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2221176 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 259445 259547 2544 2221176 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l259445 (.cons l259446 (.cons l259447 (.cons l259453 (.cons l259454 (.cons l259455 (.cons l259459 (.cons l259463 (.cons l259467 (.cons l259471 (.cons l259475 (.cons l259477 (.cons l259479 (.cons l259483 (.cons l259485 (.cons l259487 (.cons l259491 (.cons l259494 (.cons l259495 (.cons l259499 (.cons l259502 (.cons l259503 (.cons l259505 (.cons l259506 (.cons l259507 (.cons l259509 (.cons l259510 (.cons l259511 (.cons l259513 (.cons l259514 (.cons l259515 (.cons l259517 (.cons l259518 (.cons l259519 (.cons l259523 (.cons l259527 (.cons l259531 (.cons l259535 (.cons l259539 (.cons l259543 (.nil))))))))))))))))))))))))))))))))))))))))))

end S92

end RACert.S0N3.C0
