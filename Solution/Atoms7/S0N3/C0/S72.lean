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

namespace S72

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(239209, 12), (239211, 24), (239213, 24), (239215, 24), (239217, 24), (239218, 24), (239219, 24), (239221, 24), (239222, 24), (239223, 24), (239225, 24), (239226, 24), (239227, 24), (239229, 24), (239230, 24), (239231, 24), (239235, 24), (239239, 24), (239243, 24), (239247, 24), (239251, 24), (239254, 12), (239255, 24), (239259, 24), (239262, 24), (239263, 24), (239267, 24), (239269, 12), (239271, 24), (239275, 24), (239277, 24), (239279, 24), (239281, 24), (239282, 24), (239283, 24), (239285, 24), (239286, 24), (239287, 24), (239289, 24), (239290, 24), (239291, 24), (239293, 24), (239294, 24), (239295, 24), (239299, 24), (239303, 24), (239307, 24), (239311, 24), (239315, 24), (239319, 24), (239323, 24), (239326, 12), (239327, 24), (239331, 24), (239335, 24), (239339, 24), (239341, 12), (239343, 24), (239345, 24), (239346, 24), (239347, 24), (239349, 24), (239350, 24), (239351, 24), (239353, 24), (239354, 24), (239355, 24), (239357, 24), (239358, 24), (239359, 24), (239363, 24), (239367, 24), (239371, 24), (239375, 24), (239379, 24), (239383, 24), (239387, 24), (239391, 24), (239395, 24), (239399, 24), (239403, 24), (239407, 24), (239409, 12), (239410, 12), (239411, 24), (239413, 24), (239414, 24), (239415, 24), (239417, 24), (239418, 24), (239419, 24), (239421, 24), (239422, 24), (239423, 24), (239427, 24), (239431, 24), (239435, 24), (239439, 24), (239443, 24), (239447, 24), (239451, 24), (239455, 24), (239459, 24), (239463, 24), (239467, 24), (239471, 24), (239475, 24), (239477, 24), (239478, 24), (239479, 24), (239481, 12), (239482, 12), (239483, 24), (239485, 24), (239486, 24), (239487, 24), (239491, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 440, 418, 0, 538, 426, 440, 1224, 1224, 1224, 538, 426, 440, 1224, 1224, 1224, 0, 0, 0, 0, 0, 0, 0, 0, 424, 0, 1224, 418, 1224, 1224, 418, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 1224, 1224, 1224, 424, 1224, 1224, 1224, 1224, 418, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 419, 426, 440, 0, 0, 0, 419, 426, 440, 0, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 0, 0, 419, 426, 440, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(239209, 132), (239215, 199), (239235, 5), (239239, 34), (239243, 10), (239247, 40), (239251, 13), (239254, 0), (239255, 180), (239259, 37), (239263, 408), (239299, 10), (239303, 80), (239307, 20), (239311, 92), (239367, 129), (239375, 172), (239383, 168), (239391, 224), (239399, 132), (239407, 176), (239413, 96), (239414, 48), (239415, 402), (239421, 128), (239422, 128), (239423, 488), (239431, 309), (239439, 412), (239447, 483), (239455, 593), (239463, 462), (239471, 572), (239477, 160), (239478, 160), (239479, 954), (239485, 212), (239486, 212), (239487, 1108), (239491, 56)]

theorem l239209 : P.leaf 18 239209 = 132 := by decide +kernel

theorem l239215 : P.leaf 18 239215 = 199 := by decide +kernel

theorem l239235 : P.leaf 18 239235 = 5 := by decide +kernel

theorem l239239 : P.leaf 18 239239 = 34 := by decide +kernel

theorem l239243 : P.leaf 18 239243 = 10 := by decide +kernel

theorem l239247 : P.leaf 18 239247 = 40 := by decide +kernel

theorem l239251 : P.leaf 18 239251 = 13 := by decide +kernel

theorem l239254 : P.leaf 18 239254 = 0 := by decide +kernel

theorem l239255 : P.leaf 18 239255 = 180 := by decide +kernel

theorem l239259 : P.leaf 18 239259 = 37 := by decide +kernel

theorem l239263 : P.leaf 18 239263 = 408 := by decide +kernel

theorem l239299 : P.leaf 18 239299 = 10 := by decide +kernel

theorem l239303 : P.leaf 18 239303 = 80 := by decide +kernel

theorem l239307 : P.leaf 18 239307 = 20 := by decide +kernel

theorem l239311 : P.leaf 18 239311 = 92 := by decide +kernel

theorem l239367 : P.leaf 18 239367 = 129 := by decide +kernel

theorem l239375 : P.leaf 18 239375 = 172 := by decide +kernel

theorem l239383 : P.leaf 18 239383 = 168 := by decide +kernel

theorem l239391 : P.leaf 18 239391 = 224 := by decide +kernel

theorem l239399 : P.leaf 18 239399 = 132 := by decide +kernel

theorem l239407 : P.leaf 18 239407 = 176 := by decide +kernel

theorem l239413 : P.leaf 18 239413 = 96 := by decide +kernel

theorem l239414 : P.leaf 18 239414 = 48 := by decide +kernel

theorem l239415 : P.leaf 18 239415 = 402 := by decide +kernel

theorem l239421 : P.leaf 18 239421 = 128 := by decide +kernel

theorem l239422 : P.leaf 18 239422 = 128 := by decide +kernel

theorem l239423 : P.leaf 18 239423 = 488 := by decide +kernel

theorem l239431 : P.leaf 18 239431 = 309 := by decide +kernel

theorem l239439 : P.leaf 18 239439 = 412 := by decide +kernel

theorem l239447 : P.leaf 18 239447 = 483 := by decide +kernel

theorem l239455 : P.leaf 18 239455 = 593 := by decide +kernel

theorem l239463 : P.leaf 18 239463 = 462 := by decide +kernel

theorem l239471 : P.leaf 18 239471 = 572 := by decide +kernel

theorem l239477 : P.leaf 18 239477 = 160 := by decide +kernel

theorem l239478 : P.leaf 18 239478 = 160 := by decide +kernel

theorem l239479 : P.leaf 18 239479 = 954 := by decide +kernel

theorem l239485 : P.leaf 18 239485 = 212 := by decide +kernel

theorem l239486 : P.leaf 18 239486 = 212 := by decide +kernel

theorem l239487 : P.leaf 18 239487 = 1108 := by decide +kernel

theorem l239491 : P.leaf 18 239491 = 56 := by decide +kernel

theorem segOK : checkSeg 20 perms 239209 239495 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 220272 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 239209 239495 2700 220272 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l239209 (.cons l239215 (.cons l239235 (.cons l239239 (.cons l239243 (.cons l239247 (.cons l239251 (.cons l239254 (.cons l239255 (.cons l239259 (.cons l239263 (.cons l239299 (.cons l239303 (.cons l239307 (.cons l239311 (.cons l239367 (.cons l239375 (.cons l239383 (.cons l239391 (.cons l239399 (.cons l239407 (.cons l239413 (.cons l239414 (.cons l239415 (.cons l239421 (.cons l239422 (.cons l239423 (.cons l239431 (.cons l239439 (.cons l239447 (.cons l239455 (.cons l239463 (.cons l239471 (.cons l239477 (.cons l239478 (.cons l239479 (.cons l239485 (.cons l239486 (.cons l239487 (.cons l239491 (.nil))))))))))))))))))))))))))))))))))))))))))

end S72

end RACert.S0N3.C0
