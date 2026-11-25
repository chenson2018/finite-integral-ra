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

namespace S7

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(27453, 48), (27455, 24), (27456, 48), (27457, 48), (27458, 48), (27459, 48), (27460, 48), (27461, 48), (27462, 48), (27463, 48), (27464, 48), (27465, 48), (27466, 48), (27467, 48), (27468, 48), (27469, 48), (27470, 48), (27471, 48), (27472, 48), (27473, 48), (27474, 48), (27475, 48), (27476, 48), (27477, 48), (27478, 48), (27479, 48), (27480, 48), (27481, 48), (27482, 48), (27483, 48), (27484, 48), (27485, 48), (27486, 48), (27487, 48), (27488, 48), (27489, 48), (27490, 48), (27491, 48), (27492, 48), (27493, 48), (27494, 48), (27495, 48), (27496, 48), (27497, 48), (27498, 48), (27499, 48), (27500, 48), (27501, 48), (27502, 48), (27503, 48), (27504, 48), (27505, 48), (27506, 48), (27507, 48), (27508, 48), (27509, 48), (27510, 48), (27511, 48), (27512, 48), (27513, 48), (27514, 48), (27515, 48), (27516, 48), (27517, 48), (27518, 48), (27519, 48), (27584, 24), (27585, 48), (27587, 24), (27588, 48), (27589, 48), (27590, 48), (27591, 48), (27596, 24), (27597, 48), (27599, 24), (27600, 48), (27601, 48), (27602, 48), (27603, 48), (27604, 48), (27605, 48), (27606, 48), (27607, 48), (27608, 48), (27609, 48), (27610, 48), (27611, 48), (27612, 48), (27613, 48), (27614, 48), (27615, 48), (27632, 24), (27633, 48), (27635, 24), (27636, 48), (27637, 48), (27638, 48), (27639, 48), (27644, 24), (27645, 48), (27647, 24), (28416, 12), (28417, 48), (28419, 24), (28421, 24), (28422, 24), (28423, 48), (28431, 12), (28432, 48), (28433, 48), (28434, 48), (28435, 48), (28436, 48), (28437, 48), (28438, 48), (28439, 48), (28440, 48), (28441, 48), (28442, 48), (28443, 48), (28444, 48), (28445, 48), (28446, 48), (28447, 48), (28464, 24), (28465, 48), (28467, 24), (28468, 48), (28469, 48), (28470, 48), (28471, 48), (28476, 24), (28477, 48), (28479, 24), (28496, 24), (28497, 48), (28498, 48), (28499, 48), (28501, 24), (28502, 48), (28503, 48), (28506, 24), (28507, 48), (28511, 24), (28512, 24), (28513, 48), (28514, 48), (28515, 48), (28517, 48), (28518, 24), (28519, 48), (28521, 24), (28523, 48), (28527, 24), (28528, 48), (28529, 48), (28530, 48), (28531, 48), (28532, 48), (28533, 48), (28534, 48), (28535, 48), (28536, 48), (28537, 48), (28538, 48), (28539, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 427, 419, 431, 440, 418, 418, 424, 0, 418, 418, 424, 440, 418, 418, 424, 0, 419, 432, 431, 440, 424, 432, 424, 0, 424, 439, 424, 440, 424, 0, 424, 0, 427, 419, 431, 440, 418, 418, 431, 0, 418, 418, 438, 440, 418, 418, 0, 0, 419, 432, 431, 440, 431, 432, 431, 0, 439, 439, 438, 440, 0, 0, 0, 0, 419, 432, 0, 418, 418, 424, 0, 418, 418, 0, 419, 432, 431, 0, 424, 432, 424, 0, 424, 439, 424, 0, 424, 0, 424, 0, 419, 432, 0, 431, 432, 431, 0, 0, 0, 0, 0, 419, 434, 418, 424, 434, 0, 419, 432, 427, 434, 424, 432, 424, 434, 424, 439, 424, 440, 424, 0, 424, 0, 419, 432, 434, 431, 432, 431, 434, 0, 0, 0, 419, 432, 431, 440, 432, 424, 0, 424, 440, 0, 427, 419, 431, 440, 418, 431, 0, 418, 440, 0, 419, 432, 431, 440, 431, 432, 431, 0, 438, 439, 438, 440]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(27453, 24), (27455, 60), (27463, 9), (27471, 24), (27479, 54), (27485, 49), (27487, 132), (27495, 54), (27502, 49), (27503, 136), (27511, 134), (27516, 28), (27517, 96), (27518, 96), (27519, 424), (27587, 4), (27591, 16), (27599, 100), (27603, 24), (27607, 88), (27611, 88), (27613, 204), (27615, 492), (27635, 156), (27639, 312), (27644, 276), (27645, 618), (27647, 1728), (28416, 4), (28431, 4), (28445, 9), (28447, 24), (28476, 10), (28477, 40), (28479, 124), (28503, 54), (28511, 140), (28519, 54), (28527, 140), (28535, 204)]

theorem l27453 : P.leaf 18 27453 = 24 := by decide +kernel

theorem l27455 : P.leaf 18 27455 = 60 := by decide +kernel

theorem l27463 : P.leaf 18 27463 = 9 := by decide +kernel

theorem l27471 : P.leaf 18 27471 = 24 := by decide +kernel

theorem l27479 : P.leaf 18 27479 = 54 := by decide +kernel

theorem l27485 : P.leaf 18 27485 = 49 := by decide +kernel

theorem l27487 : P.leaf 18 27487 = 132 := by decide +kernel

theorem l27495 : P.leaf 18 27495 = 54 := by decide +kernel

theorem l27502 : P.leaf 18 27502 = 49 := by decide +kernel

theorem l27503 : P.leaf 18 27503 = 136 := by decide +kernel

theorem l27511 : P.leaf 18 27511 = 134 := by decide +kernel

theorem l27516 : P.leaf 18 27516 = 28 := by decide +kernel

theorem l27517 : P.leaf 18 27517 = 96 := by decide +kernel

theorem l27518 : P.leaf 18 27518 = 96 := by decide +kernel

theorem l27519 : P.leaf 18 27519 = 424 := by decide +kernel

theorem l27587 : P.leaf 18 27587 = 4 := by decide +kernel

theorem l27591 : P.leaf 18 27591 = 16 := by decide +kernel

theorem l27599 : P.leaf 18 27599 = 100 := by decide +kernel

theorem l27603 : P.leaf 18 27603 = 24 := by decide +kernel

theorem l27607 : P.leaf 18 27607 = 88 := by decide +kernel

theorem l27611 : P.leaf 18 27611 = 88 := by decide +kernel

theorem l27613 : P.leaf 18 27613 = 204 := by decide +kernel

theorem l27615 : P.leaf 18 27615 = 492 := by decide +kernel

theorem l27635 : P.leaf 18 27635 = 156 := by decide +kernel

theorem l27639 : P.leaf 18 27639 = 312 := by decide +kernel

theorem l27644 : P.leaf 18 27644 = 276 := by decide +kernel

theorem l27645 : P.leaf 18 27645 = 618 := by decide +kernel

theorem l27647 : P.leaf 18 27647 = 1728 := by decide +kernel

theorem l28416 : P.leaf 18 28416 = 4 := by decide +kernel

theorem l28431 : P.leaf 18 28431 = 4 := by decide +kernel

theorem l28445 : P.leaf 18 28445 = 9 := by decide +kernel

theorem l28447 : P.leaf 18 28447 = 24 := by decide +kernel

theorem l28476 : P.leaf 18 28476 = 10 := by decide +kernel

theorem l28477 : P.leaf 18 28477 = 40 := by decide +kernel

theorem l28479 : P.leaf 18 28479 = 124 := by decide +kernel

theorem l28503 : P.leaf 18 28503 = 54 := by decide +kernel

theorem l28511 : P.leaf 18 28511 = 140 := by decide +kernel

theorem l28519 : P.leaf 18 28519 = 54 := by decide +kernel

theorem l28527 : P.leaf 18 28527 = 140 := by decide +kernel

theorem l28535 : P.leaf 18 28535 = 204 := by decide +kernel

theorem segOK : checkSeg 20 perms 27453 28540 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 235536 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 27453 28540 7368 235536 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l27453 (.cons l27455 (.cons l27463 (.cons l27471 (.cons l27479 (.cons l27485 (.cons l27487 (.cons l27495 (.cons l27502 (.cons l27503 (.cons l27511 (.cons l27516 (.cons l27517 (.cons l27518 (.cons l27519 (.cons l27587 (.cons l27591 (.cons l27599 (.cons l27603 (.cons l27607 (.cons l27611 (.cons l27613 (.cons l27615 (.cons l27635 (.cons l27639 (.cons l27644 (.cons l27645 (.cons l27647 (.cons l28416 (.cons l28431 (.cons l28445 (.cons l28447 (.cons l28476 (.cons l28477 (.cons l28479 (.cons l28503 (.cons l28511 (.cons l28519 (.cons l28527 (.cons l28535 (.nil))))))))))))))))))))))))))))))))))))))))))

end S7

end RACert.S0N3.C0
