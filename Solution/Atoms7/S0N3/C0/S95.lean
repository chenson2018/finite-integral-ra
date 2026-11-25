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

namespace S95

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(260094, 24), (260095, 48), (261123, 12), (261127, 24), (261131, 24), (261135, 24), (261139, 48), (261143, 48), (261147, 48), (261151, 48), (261171, 24), (261175, 24), (261179, 24), (261183, 24), (261191, 24), (261195, 12), (261199, 24), (261203, 48), (261207, 48), (261211, 48), (261215, 48), (261235, 24), (261239, 24), (261243, 24), (261247, 24), (261255, 12), (261263, 24), (261267, 48), (261271, 48), (261275, 48), (261279, 48), (261299, 24), (261303, 24), (261307, 24), (261311, 24), (261327, 12), (261331, 48), (261335, 48), (261339, 48), (261343, 48), (261363, 24), (261367, 24), (261371, 24), (261375, 24), (261395, 24), (261399, 48), (261403, 48), (261407, 48), (261411, 24), (261415, 48), (261419, 48), (261423, 48), (261427, 48), (261431, 48), (261435, 48), (261439, 48), (261463, 48), (261467, 24), (261471, 48), (261479, 48), (261483, 24), (261487, 48), (261491, 48), (261495, 48), (261499, 48), (261503, 48), (261527, 24), (261535, 48), (261543, 24), (261551, 48), (261555, 48), (261559, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 440, 663, 440, 663, 440, 0, 440, 0, 440, 0, 440, 0, 663, 440, 663, 440, 0, 440, 0, 440, 0, 440, 0, 663, 663, 669, 0, 669, 0, 0, 0, 0, 0, 663, 669, 0, 669, 0, 0, 0, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 0, 440, 0, 0, 440, 0, 440, 0, 440, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(260094, 3240), (260095, 8778), (261143, 64), (261151, 128), (261175, 386), (261183, 844), (261207, 312), (261215, 376), (261239, 2536), (261247, 3501), (261271, 336), (261279, 504), (261299, 654), (261303, 2791), (261307, 2622), (261311, 6865), (261335, 396), (261343, 504), (261363, 1284), (261367, 4705), (261371, 3177), (261375, 9573), (261399, 402), (261407, 912), (261415, 378), (261423, 920), (261431, 620), (261439, 1216), (261463, 2372), (261471, 3199), (261479, 2400), (261487, 3137), (261495, 3708), (261503, 5222), (261527, 2429), (261535, 5329), (261543, 2347), (261551, 5733), (261555, 670), (261559, 4405)]

theorem l260094 : P.leaf 18 260094 = 3240 := by decide +kernel

theorem l260095 : P.leaf 18 260095 = 8778 := by decide +kernel

theorem l261143 : P.leaf 18 261143 = 64 := by decide +kernel

theorem l261151 : P.leaf 18 261151 = 128 := by decide +kernel

theorem l261175 : P.leaf 18 261175 = 386 := by decide +kernel

theorem l261183 : P.leaf 18 261183 = 844 := by decide +kernel

theorem l261207 : P.leaf 18 261207 = 312 := by decide +kernel

theorem l261215 : P.leaf 18 261215 = 376 := by decide +kernel

theorem l261239 : P.leaf 18 261239 = 2536 := by decide +kernel

theorem l261247 : P.leaf 18 261247 = 3501 := by decide +kernel

theorem l261271 : P.leaf 18 261271 = 336 := by decide +kernel

theorem l261279 : P.leaf 18 261279 = 504 := by decide +kernel

theorem l261299 : P.leaf 18 261299 = 654 := by decide +kernel

theorem l261303 : P.leaf 18 261303 = 2791 := by decide +kernel

theorem l261307 : P.leaf 18 261307 = 2622 := by decide +kernel

theorem l261311 : P.leaf 18 261311 = 6865 := by decide +kernel

theorem l261335 : P.leaf 18 261335 = 396 := by decide +kernel

theorem l261343 : P.leaf 18 261343 = 504 := by decide +kernel

theorem l261363 : P.leaf 18 261363 = 1284 := by decide +kernel

theorem l261367 : P.leaf 18 261367 = 4705 := by decide +kernel

theorem l261371 : P.leaf 18 261371 = 3177 := by decide +kernel

theorem l261375 : P.leaf 18 261375 = 9573 := by decide +kernel

theorem l261399 : P.leaf 18 261399 = 402 := by decide +kernel

theorem l261407 : P.leaf 18 261407 = 912 := by decide +kernel

theorem l261415 : P.leaf 18 261415 = 378 := by decide +kernel

theorem l261423 : P.leaf 18 261423 = 920 := by decide +kernel

theorem l261431 : P.leaf 18 261431 = 620 := by decide +kernel

theorem l261439 : P.leaf 18 261439 = 1216 := by decide +kernel

theorem l261463 : P.leaf 18 261463 = 2372 := by decide +kernel

theorem l261471 : P.leaf 18 261471 = 3199 := by decide +kernel

theorem l261479 : P.leaf 18 261479 = 2400 := by decide +kernel

theorem l261487 : P.leaf 18 261487 = 3137 := by decide +kernel

theorem l261495 : P.leaf 18 261495 = 3708 := by decide +kernel

theorem l261503 : P.leaf 18 261503 = 5222 := by decide +kernel

theorem l261527 : P.leaf 18 261527 = 2429 := by decide +kernel

theorem l261535 : P.leaf 18 261535 = 5329 := by decide +kernel

theorem l261543 : P.leaf 18 261543 = 2347 := by decide +kernel

theorem l261551 : P.leaf 18 261551 = 5733 := by decide +kernel

theorem l261555 : P.leaf 18 261555 = 670 := by decide +kernel

theorem l261559 : P.leaf 18 261559 = 4405 := by decide +kernel

theorem segOK : checkSeg 20 perms 260094 261563 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 3623904 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 260094 261563 2616 3623904 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l260094 (.cons l260095 (.cons l261143 (.cons l261151 (.cons l261175 (.cons l261183 (.cons l261207 (.cons l261215 (.cons l261239 (.cons l261247 (.cons l261271 (.cons l261279 (.cons l261299 (.cons l261303 (.cons l261307 (.cons l261311 (.cons l261335 (.cons l261343 (.cons l261363 (.cons l261367 (.cons l261371 (.cons l261375 (.cons l261399 (.cons l261407 (.cons l261415 (.cons l261423 (.cons l261431 (.cons l261439 (.cons l261463 (.cons l261471 (.cons l261479 (.cons l261487 (.cons l261495 (.cons l261503 (.cons l261527 (.cons l261535 (.cons l261543 (.cons l261551 (.cons l261555 (.cons l261559 (.nil))))))))))))))))))))))))))))))))))))))))))

end S95

end RACert.S0N3.C0
