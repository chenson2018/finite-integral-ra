/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S2

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(2417, 20), (2419, 30), (2423, 20), (2431, 5), (2432, 30), (2433, 60), (2435, 30), (2436, 60), (2437, 120), (2439, 60), (2444, 30), (2445, 60), (2447, 30), (2448, 30), (2449, 60), (2451, 30), (2452, 60), (2453, 120), (2455, 60), (2460, 30), (2461, 60), (2463, 30), (2464, 60), (2465, 120), (2467, 60), (2468, 60), (2469, 120), (2471, 60), (2472, 60), (2473, 120), (2475, 60), (2476, 60), (2477, 120), (2479, 60), (2480, 60), (2481, 120), (2483, 60), (2484, 60), (2485, 120), (2487, 60)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(2417, 1741), (2419, 2577), (2423, 4097), (2431, 6753), (2432, 2), (2433, 5), (2435, 5), (2436, 2), (2437, 4), (2439, 4), (2444, 2), (2445, 8), (2447, 8), (2448, 8), (2449, 13), (2451, 29), (2452, 7), (2453, 10), (2455, 22), (2460, 11), (2461, 22), (2463, 50), (2464, 20), (2465, 20), (2467, 20), (2468, 23), (2469, 24), (2471, 24), (2472, 20), (2473, 20), (2475, 20), (2476, 22), (2477, 24), (2479, 24), (2480, 32), (2481, 28), (2483, 44), (2484, 45), (2485, 40), (2487, 72)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 2417 2488 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 278625 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 2417 2488 2475 278625 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S2

end RACert.S5N0.C0
