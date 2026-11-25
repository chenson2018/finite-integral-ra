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

namespace S114

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(457200, 12), (457201, 48), (457203, 24), (457205, 24), (457206, 24), (457207, 48), (457215, 12), (457472, 24), (457473, 48), (457475, 24), (457476, 48), (457477, 48), (457478, 48), (457479, 48), (457484, 24), (457485, 48), (457487, 24), (457488, 48), (457489, 48), (457490, 48), (457491, 48), (457492, 48), (457493, 48), (457494, 48), (457495, 48), (457496, 48), (457497, 48), (457498, 48), (457499, 48), (457500, 48), (457501, 48), (457502, 48), (457503, 48), (457520, 24), (457521, 48), (457523, 24), (457524, 48), (457525, 48), (457526, 48), (457527, 48), (457532, 24), (457533, 48), (457535, 24), (457536, 48), (457537, 48), (457538, 48), (457539, 48), (457540, 48), (457541, 48), (457542, 48), (457543, 48), (457544, 48), (457545, 48), (457546, 48), (457547, 48), (457548, 48), (457549, 48), (457550, 48), (457551, 48), (457552, 48), (457553, 48), (457554, 48), (457555, 48), (457556, 48), (457557, 48), (457558, 48), (457559, 48), (457560, 48), (457561, 48), (457562, 48), (457563, 48), (457564, 48), (457565, 48), (457566, 48), (457567, 48), (457568, 48), (457569, 48), (457570, 48), (457571, 48), (457572, 48), (457573, 48), (457574, 48), (457575, 48), (457576, 48), (457577, 48), (457578, 48), (457579, 48), (457580, 48), (457581, 48), (457582, 48), (457583, 48), (457584, 48), (457585, 48), (457586, 48), (457587, 48), (457588, 48), (457589, 48), (457590, 48), (457591, 48), (457592, 48), (457593, 48), (457594, 48), (457595, 48), (457596, 48), (457597, 48), (457598, 48), (457599, 48), (457664, 24), (457665, 48), (457667, 24), (457668, 48), (457669, 48), (457670, 48), (457671, 48), (457676, 24), (457677, 48), (457679, 24), (457680, 48), (457681, 48), (457682, 48), (457683, 48), (457684, 48), (457685, 48), (457686, 48), (457687, 48), (457688, 48), (457689, 48), (457690, 48), (457691, 48), (457692, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 418, 434, 602, 431, 502, 431, 602, 502, 502, 0, 434, 434, 431, 602, 431, 602, 431, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 434, 602, 602, 602, 602, 602, 0, 0, 0, 418, 439, 550, 650, 502, 502, 550, 0, 439, 439, 550, 650, 502, 502, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 502, 439, 650, 650, 502, 502, 0, 0, 439, 439, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 418, 502, 0, 502, 502, 550, 0, 502, 502, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(457200, 169), (457201, 480), (457203, 3122), (457205, 2264), (457206, 2348), (457207, 5479), (457215, 14968), (457487, 880), (457501, 720), (457503, 960), (457532, 664), (457533, 1072), (457535, 1528), (457543, 1844), (457551, 3126), (457557, 1683), (457559, 3115), (457565, 3464), (457567, 5859), (457574, 1548), (457575, 3135), (457582, 3440), (457583, 5805), (457588, 394), (457589, 2533), (457590, 2348), (457591, 6351), (457596, 2482), (457597, 5403), (457598, 5433), (457599, 13644), (457667, 1744), (457671, 3199), (457679, 5808), (457681, 468), (457683, 2538), (457685, 2800), (457687, 4791), (457689, 2589), (457691, 4811)]

theorem l457200 : P.leaf 18 457200 = 169 := by decide +kernel

theorem l457201 : P.leaf 18 457201 = 480 := by decide +kernel

theorem l457203 : P.leaf 18 457203 = 3122 := by decide +kernel

theorem l457205 : P.leaf 18 457205 = 2264 := by decide +kernel

theorem l457206 : P.leaf 18 457206 = 2348 := by decide +kernel

theorem l457207 : P.leaf 18 457207 = 5479 := by decide +kernel

theorem l457215 : P.leaf 18 457215 = 14968 := by decide +kernel

theorem l457487 : P.leaf 18 457487 = 880 := by decide +kernel

theorem l457501 : P.leaf 18 457501 = 720 := by decide +kernel

theorem l457503 : P.leaf 18 457503 = 960 := by decide +kernel

theorem l457532 : P.leaf 18 457532 = 664 := by decide +kernel

theorem l457533 : P.leaf 18 457533 = 1072 := by decide +kernel

theorem l457535 : P.leaf 18 457535 = 1528 := by decide +kernel

theorem l457543 : P.leaf 18 457543 = 1844 := by decide +kernel

theorem l457551 : P.leaf 18 457551 = 3126 := by decide +kernel

theorem l457557 : P.leaf 18 457557 = 1683 := by decide +kernel

theorem l457559 : P.leaf 18 457559 = 3115 := by decide +kernel

theorem l457565 : P.leaf 18 457565 = 3464 := by decide +kernel

theorem l457567 : P.leaf 18 457567 = 5859 := by decide +kernel

theorem l457574 : P.leaf 18 457574 = 1548 := by decide +kernel

theorem l457575 : P.leaf 18 457575 = 3135 := by decide +kernel

theorem l457582 : P.leaf 18 457582 = 3440 := by decide +kernel

theorem l457583 : P.leaf 18 457583 = 5805 := by decide +kernel

theorem l457588 : P.leaf 18 457588 = 394 := by decide +kernel

theorem l457589 : P.leaf 18 457589 = 2533 := by decide +kernel

theorem l457590 : P.leaf 18 457590 = 2348 := by decide +kernel

theorem l457591 : P.leaf 18 457591 = 6351 := by decide +kernel

theorem l457596 : P.leaf 18 457596 = 2482 := by decide +kernel

theorem l457597 : P.leaf 18 457597 = 5403 := by decide +kernel

theorem l457598 : P.leaf 18 457598 = 5433 := by decide +kernel

theorem l457599 : P.leaf 18 457599 = 13644 := by decide +kernel

theorem l457667 : P.leaf 18 457667 = 1744 := by decide +kernel

theorem l457671 : P.leaf 18 457671 = 3199 := by decide +kernel

theorem l457679 : P.leaf 18 457679 = 5808 := by decide +kernel

theorem l457681 : P.leaf 18 457681 = 468 := by decide +kernel

theorem l457683 : P.leaf 18 457683 = 2538 := by decide +kernel

theorem l457685 : P.leaf 18 457685 = 2800 := by decide +kernel

theorem l457687 : P.leaf 18 457687 = 4791 := by decide +kernel

theorem l457689 : P.leaf 18 457689 = 2589 := by decide +kernel

theorem l457691 : P.leaf 18 457691 = 4811 := by decide +kernel

theorem segOK : checkSeg 20 perms 457200 457693 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 5494908 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 457200 457693 5808 5494908 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l457200 (.cons l457201 (.cons l457203 (.cons l457205 (.cons l457206 (.cons l457207 (.cons l457215 (.cons l457487 (.cons l457501 (.cons l457503 (.cons l457532 (.cons l457533 (.cons l457535 (.cons l457543 (.cons l457551 (.cons l457557 (.cons l457559 (.cons l457565 (.cons l457567 (.cons l457574 (.cons l457575 (.cons l457582 (.cons l457583 (.cons l457588 (.cons l457589 (.cons l457590 (.cons l457591 (.cons l457596 (.cons l457597 (.cons l457598 (.cons l457599 (.cons l457667 (.cons l457671 (.cons l457679 (.cons l457681 (.cons l457683 (.cons l457685 (.cons l457687 (.cons l457689 (.cons l457691 (.nil))))))))))))))))))))))))))))))))))))))))))

end S114

end RACert.S0N3.C0
