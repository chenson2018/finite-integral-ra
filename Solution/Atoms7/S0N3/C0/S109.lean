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

namespace S109

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(455377, 48), (455378, 48), (455379, 48), (455380, 48), (455381, 48), (455382, 48), (455383, 48), (455384, 48), (455385, 48), (455386, 48), (455387, 48), (455388, 48), (455389, 48), (455390, 48), (455391, 48), (455408, 24), (455409, 48), (455411, 24), (455412, 48), (455413, 48), (455414, 48), (455415, 48), (455420, 24), (455421, 48), (455423, 24), (455424, 24), (455425, 48), (455427, 24), (455428, 48), (455429, 48), (455430, 48), (455431, 48), (455436, 24), (455437, 48), (455439, 24), (455440, 48), (455441, 48), (455442, 48), (455443, 48), (455444, 48), (455445, 48), (455446, 48), (455447, 48), (455448, 48), (455449, 48), (455450, 48), (455451, 48), (455452, 48), (455453, 48), (455454, 48), (455455, 48), (455472, 24), (455473, 48), (455475, 24), (455476, 48), (455477, 48), (455478, 48), (455479, 48), (455484, 24), (455485, 48), (455487, 24), (455488, 48), (455489, 48), (455490, 48), (455491, 48), (455492, 48), (455493, 48), (455494, 48), (455495, 48), (455496, 48), (455497, 48), (455498, 48), (455499, 48), (455500, 48), (455501, 48), (455502, 48), (455503, 48), (455504, 48), (455505, 48), (455506, 48), (455507, 48), (455508, 48), (455509, 48), (455510, 48), (455511, 48), (455512, 48), (455513, 48), (455514, 48), (455515, 48), (455516, 48), (455517, 48), (455518, 48), (455519, 48), (455520, 48), (455521, 48), (455522, 48), (455523, 48), (455524, 48), (455525, 48), (455526, 48), (455527, 48), (455528, 48), (455529, 48), (455530, 48), (455531, 48), (455532, 48), (455533, 48), (455534, 48), (455535, 48), (455536, 48), (455537, 48), (455538, 48), (455539, 48), (455540, 48), (455541, 48), (455542, 48), (455543, 48), (455544, 48), (455545, 48), (455546, 48), (455547, 48), (455548, 48), (455549, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 434, 434, 502, 502, 431, 602, 502, 502, 0, 434, 434, 431, 434, 550, 602, 431, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 434, 434, 602, 602, 602, 602, 0, 0, 0, 418, 439, 550, 650, 502, 502, 550, 0, 502, 439, 550, 650, 502, 502, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 502, 439, 650, 650, 502, 502, 0, 0, 502, 439, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(455377, 32), (455379, 237), (455381, 209), (455383, 662), (455385, 126), (455387, 741), (455389, 648), (455391, 2001), (455408, 19), (455409, 122), (455411, 746), (455412, 148), (455413, 806), (455414, 381), (455415, 2060), (455420, 844), (455421, 2202), (455423, 6942), (455439, 146), (455453, 85), (455455, 174), (455484, 80), (455485, 138), (455487, 236), (455495, 223), (455503, 367), (455509, 150), (455511, 322), (455517, 300), (455519, 538), (455526, 172), (455527, 322), (455534, 300), (455535, 538), (455540, 40), (455541, 210), (455542, 236), (455543, 450), (455548, 330), (455549, 420)]

theorem l455377 : P.leaf 18 455377 = 32 := by decide +kernel

theorem l455379 : P.leaf 18 455379 = 237 := by decide +kernel

theorem l455381 : P.leaf 18 455381 = 209 := by decide +kernel

theorem l455383 : P.leaf 18 455383 = 662 := by decide +kernel

theorem l455385 : P.leaf 18 455385 = 126 := by decide +kernel

theorem l455387 : P.leaf 18 455387 = 741 := by decide +kernel

theorem l455389 : P.leaf 18 455389 = 648 := by decide +kernel

theorem l455391 : P.leaf 18 455391 = 2001 := by decide +kernel

theorem l455408 : P.leaf 18 455408 = 19 := by decide +kernel

theorem l455409 : P.leaf 18 455409 = 122 := by decide +kernel

theorem l455411 : P.leaf 18 455411 = 746 := by decide +kernel

theorem l455412 : P.leaf 18 455412 = 148 := by decide +kernel

theorem l455413 : P.leaf 18 455413 = 806 := by decide +kernel

theorem l455414 : P.leaf 18 455414 = 381 := by decide +kernel

theorem l455415 : P.leaf 18 455415 = 2060 := by decide +kernel

theorem l455420 : P.leaf 18 455420 = 844 := by decide +kernel

theorem l455421 : P.leaf 18 455421 = 2202 := by decide +kernel

theorem l455423 : P.leaf 18 455423 = 6942 := by decide +kernel

theorem l455439 : P.leaf 18 455439 = 146 := by decide +kernel

theorem l455453 : P.leaf 18 455453 = 85 := by decide +kernel

theorem l455455 : P.leaf 18 455455 = 174 := by decide +kernel

theorem l455484 : P.leaf 18 455484 = 80 := by decide +kernel

theorem l455485 : P.leaf 18 455485 = 138 := by decide +kernel

theorem l455487 : P.leaf 18 455487 = 236 := by decide +kernel

theorem l455495 : P.leaf 18 455495 = 223 := by decide +kernel

theorem l455503 : P.leaf 18 455503 = 367 := by decide +kernel

theorem l455509 : P.leaf 18 455509 = 150 := by decide +kernel

theorem l455511 : P.leaf 18 455511 = 322 := by decide +kernel

theorem l455517 : P.leaf 18 455517 = 300 := by decide +kernel

theorem l455519 : P.leaf 18 455519 = 538 := by decide +kernel

theorem l455526 : P.leaf 18 455526 = 172 := by decide +kernel

theorem l455527 : P.leaf 18 455527 = 322 := by decide +kernel

theorem l455534 : P.leaf 18 455534 = 300 := by decide +kernel

theorem l455535 : P.leaf 18 455535 = 538 := by decide +kernel

theorem l455540 : P.leaf 18 455540 = 40 := by decide +kernel

theorem l455541 : P.leaf 18 455541 = 210 := by decide +kernel

theorem l455542 : P.leaf 18 455542 = 236 := by decide +kernel

theorem l455543 : P.leaf 18 455543 = 450 := by decide +kernel

theorem l455548 : P.leaf 18 455548 = 330 := by decide +kernel

theorem l455549 : P.leaf 18 455549 = 420 := by decide +kernel

theorem segOK : checkSeg 20 perms 455377 455550 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 969432 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 455377 455550 5616 969432 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l455377 (.cons l455379 (.cons l455381 (.cons l455383 (.cons l455385 (.cons l455387 (.cons l455389 (.cons l455391 (.cons l455408 (.cons l455409 (.cons l455411 (.cons l455412 (.cons l455413 (.cons l455414 (.cons l455415 (.cons l455420 (.cons l455421 (.cons l455423 (.cons l455439 (.cons l455453 (.cons l455455 (.cons l455484 (.cons l455485 (.cons l455487 (.cons l455495 (.cons l455503 (.cons l455509 (.cons l455511 (.cons l455517 (.cons l455519 (.cons l455526 (.cons l455527 (.cons l455534 (.cons l455535 (.cons l455540 (.cons l455541 (.cons l455542 (.cons l455543 (.cons l455548 (.cons l455549 (.nil))))))))))))))))))))))))))))))))))))))))))

end S109

end RACert.S0N3.C0
