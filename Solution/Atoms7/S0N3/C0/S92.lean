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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 259445 259547 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2221176 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 259445 259547 2544 2221176 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S92

end RACert.S0N3.C0
