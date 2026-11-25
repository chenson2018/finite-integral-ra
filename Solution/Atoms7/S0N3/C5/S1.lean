/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C5.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

namespace S1

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(120, 12), (121, 24), (123, 12), (124, 12), (125, 24), (127, 12), (240, 3), (241, 12), (243, 6), (245, 12), (247, 12), (255, 3), (261, 24), (262, 24), (263, 24), (269, 24), (271, 12), (277, 24), (278, 12), (279, 24), (282, 12), (283, 24), (284, 24), (285, 24), (286, 24), (287, 24), (311, 12), (316, 12), (317, 24), (319, 12), (321, 8), (322, 8), (323, 24), (325, 24), (326, 24), (327, 24), (329, 24), (330, 24), (331, 24), (333, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(120, 262), (121, 291), (123, 400), (124, 394), (125, 428), (127, 659), (240, 172), (241, 398), (243, 548), (245, 468), (247, 611), (255, 994), (261, 73), (262, 65), (263, 140), (269, 71), (271, 153), (277, 117), (278, 133), (279, 232), (282, 80), (283, 187), (284, 109), (285, 197), (286, 127), (287, 238), (311, 387), (316, 243), (317, 284), (319, 395), (321, 17), (322, 37), (323, 74), (325, 104), (326, 131), (327, 244), (329, 99), (330, 115), (331, 197), (333, 190)]

theorem l120 : P.leaf 16 120 = 262 := by decide +kernel

theorem l121 : P.leaf 16 121 = 291 := by decide +kernel

theorem l123 : P.leaf 16 123 = 400 := by decide +kernel

theorem l124 : P.leaf 16 124 = 394 := by decide +kernel

theorem l125 : P.leaf 16 125 = 428 := by decide +kernel

theorem l127 : P.leaf 16 127 = 659 := by decide +kernel

theorem l240 : P.leaf 16 240 = 172 := by decide +kernel

theorem l241 : P.leaf 16 241 = 398 := by decide +kernel

theorem l243 : P.leaf 16 243 = 548 := by decide +kernel

theorem l245 : P.leaf 16 245 = 468 := by decide +kernel

theorem l247 : P.leaf 16 247 = 611 := by decide +kernel

theorem l255 : P.leaf 16 255 = 994 := by decide +kernel

theorem l261 : P.leaf 16 261 = 73 := by decide +kernel

theorem l262 : P.leaf 16 262 = 65 := by decide +kernel

theorem l263 : P.leaf 16 263 = 140 := by decide +kernel

theorem l269 : P.leaf 16 269 = 71 := by decide +kernel

theorem l271 : P.leaf 16 271 = 153 := by decide +kernel

theorem l277 : P.leaf 16 277 = 117 := by decide +kernel

theorem l278 : P.leaf 16 278 = 133 := by decide +kernel

theorem l279 : P.leaf 16 279 = 232 := by decide +kernel

theorem l282 : P.leaf 16 282 = 80 := by decide +kernel

theorem l283 : P.leaf 16 283 = 187 := by decide +kernel

theorem l284 : P.leaf 16 284 = 109 := by decide +kernel

theorem l285 : P.leaf 16 285 = 197 := by decide +kernel

theorem l286 : P.leaf 16 286 = 127 := by decide +kernel

theorem l287 : P.leaf 16 287 = 238 := by decide +kernel

theorem l311 : P.leaf 16 311 = 387 := by decide +kernel

theorem l316 : P.leaf 16 316 = 243 := by decide +kernel

theorem l317 : P.leaf 16 317 = 284 := by decide +kernel

theorem l319 : P.leaf 16 319 = 395 := by decide +kernel

theorem l321 : P.leaf 16 321 = 17 := by decide +kernel

theorem l322 : P.leaf 16 322 = 37 := by decide +kernel

theorem l323 : P.leaf 16 323 = 74 := by decide +kernel

theorem l325 : P.leaf 16 325 = 104 := by decide +kernel

theorem l326 : P.leaf 16 326 = 131 := by decide +kernel

theorem l327 : P.leaf 16 327 = 244 := by decide +kernel

theorem l329 : P.leaf 16 329 = 99 := by decide +kernel

theorem l330 : P.leaf 16 330 = 115 := by decide +kernel

theorem l331 : P.leaf 16 331 = 197 := by decide +kernel

theorem l333 : P.leaf 16 333 = 190 := by decide +kernel

theorem segOK : checkSeg 12 perms 120 334 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 151326 = true := by decide +kernel

theorem total : OrbitSeg 12 perms (P.leaf 16) 120 334 712 151326 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l120 (.cons l121 (.cons l123 (.cons l124 (.cons l125 (.cons l127 (.cons l240 (.cons l241 (.cons l243 (.cons l245 (.cons l247 (.cons l255 (.cons l261 (.cons l262 (.cons l263 (.cons l269 (.cons l271 (.cons l277 (.cons l278 (.cons l279 (.cons l282 (.cons l283 (.cons l284 (.cons l285 (.cons l286 (.cons l287 (.cons l311 (.cons l316 (.cons l317 (.cons l319 (.cons l321 (.cons l322 (.cons l323 (.cons l325 (.cons l326 (.cons l327 (.cons l329 (.cons l330 (.cons l331 (.cons l333 (.nil))))))))))))))))))))))))))))))))))))))))))

end S1

end RACert.S0N3.C5
