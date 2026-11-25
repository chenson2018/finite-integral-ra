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

theorem l2417 : P.leaf 20 2417 = 1741 := by decide +kernel

theorem l2419 : P.leaf 20 2419 = 2577 := by decide +kernel

theorem l2423 : P.leaf 20 2423 = 4097 := by decide +kernel

theorem l2431 : P.leaf 20 2431 = 6753 := by decide +kernel

theorem l2432 : P.leaf 20 2432 = 2 := by decide +kernel

theorem l2433 : P.leaf 20 2433 = 5 := by decide +kernel

theorem l2435 : P.leaf 20 2435 = 5 := by decide +kernel

theorem l2436 : P.leaf 20 2436 = 2 := by decide +kernel

theorem l2437 : P.leaf 20 2437 = 4 := by decide +kernel

theorem l2439 : P.leaf 20 2439 = 4 := by decide +kernel

theorem l2444 : P.leaf 20 2444 = 2 := by decide +kernel

theorem l2445 : P.leaf 20 2445 = 8 := by decide +kernel

theorem l2447 : P.leaf 20 2447 = 8 := by decide +kernel

theorem l2448 : P.leaf 20 2448 = 8 := by decide +kernel

theorem l2449 : P.leaf 20 2449 = 13 := by decide +kernel

theorem l2451 : P.leaf 20 2451 = 29 := by decide +kernel

theorem l2452 : P.leaf 20 2452 = 7 := by decide +kernel

theorem l2453 : P.leaf 20 2453 = 10 := by decide +kernel

theorem l2455 : P.leaf 20 2455 = 22 := by decide +kernel

theorem l2460 : P.leaf 20 2460 = 11 := by decide +kernel

theorem l2461 : P.leaf 20 2461 = 22 := by decide +kernel

theorem l2463 : P.leaf 20 2463 = 50 := by decide +kernel

theorem l2464 : P.leaf 20 2464 = 20 := by decide +kernel

theorem l2465 : P.leaf 20 2465 = 20 := by decide +kernel

theorem l2467 : P.leaf 20 2467 = 20 := by decide +kernel

theorem l2468 : P.leaf 20 2468 = 23 := by decide +kernel

theorem l2469 : P.leaf 20 2469 = 24 := by decide +kernel

theorem l2471 : P.leaf 20 2471 = 24 := by decide +kernel

theorem l2472 : P.leaf 20 2472 = 20 := by decide +kernel

theorem l2473 : P.leaf 20 2473 = 20 := by decide +kernel

theorem l2475 : P.leaf 20 2475 = 20 := by decide +kernel

theorem l2476 : P.leaf 20 2476 = 22 := by decide +kernel

theorem l2477 : P.leaf 20 2477 = 24 := by decide +kernel

theorem l2479 : P.leaf 20 2479 = 24 := by decide +kernel

theorem l2480 : P.leaf 20 2480 = 32 := by decide +kernel

theorem l2481 : P.leaf 20 2481 = 28 := by decide +kernel

theorem l2483 : P.leaf 20 2483 = 44 := by decide +kernel

theorem l2484 : P.leaf 20 2484 = 45 := by decide +kernel

theorem l2485 : P.leaf 20 2485 = 40 := by decide +kernel

theorem l2487 : P.leaf 20 2487 = 72 := by decide +kernel

theorem segOK : checkSeg 15 perms 2417 2488 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 278625 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 2417 2488 2475 278625 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l2417 (.cons l2419 (.cons l2423 (.cons l2431 (.cons l2432 (.cons l2433 (.cons l2435 (.cons l2436 (.cons l2437 (.cons l2439 (.cons l2444 (.cons l2445 (.cons l2447 (.cons l2448 (.cons l2449 (.cons l2451 (.cons l2452 (.cons l2453 (.cons l2455 (.cons l2460 (.cons l2461 (.cons l2463 (.cons l2464 (.cons l2465 (.cons l2467 (.cons l2468 (.cons l2469 (.cons l2471 (.cons l2472 (.cons l2473 (.cons l2475 (.cons l2476 (.cons l2477 (.cons l2479 (.cons l2480 (.cons l2481 (.cons l2483 (.cons l2484 (.cons l2485 (.cons l2487 (.nil))))))))))))))))))))))))))))))))))))))))))

end S2

end RACert.S5N0.C0
