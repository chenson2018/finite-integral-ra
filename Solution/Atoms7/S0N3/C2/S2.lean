/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C2.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C2

open RACert RACert.Problem

namespace S2

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(369, 4), (371, 2), (372, 4), (373, 4), (374, 4), (375, 4), (380, 2), (381, 4), (383, 2), (384, 2), (385, 4), (387, 2), (388, 4), (389, 4), (390, 4), (391, 4), (396, 2), (397, 4), (399, 2), (400, 4), (401, 4), (402, 4), (403, 4), (404, 4), (405, 4), (406, 4), (407, 4), (408, 4), (409, 4), (410, 4), (411, 4), (412, 4), (413, 4), (414, 4), (415, 4), (432, 2), (433, 4), (435, 2), (436, 4), (437, 4), (438, 4), (439, 4), (444, 2), (445, 4), (447, 2), (448, 4), (449, 8), (451, 4), (452, 8), (453, 8), (454, 8), (455, 8), (460, 4), (461, 8), (463, 4), (464, 8), (465, 8), (466, 8), (467, 8), (468, 8), (469, 8), (470, 8), (471, 8), (472, 8), (473, 8), (474, 8)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 420, 0, 0, 0, 420, 0, 0, 418, 0, 0, 418, 0, 0, 0, 418, 0, 0, 417, 0, 0, 0, 434, 0, 0, 0, 417, 0, 0, 0, 434, 0, 0, 0, 417, 0, 0, 433, 0, 0, 0, 0, 0, 0, 417, 602, 0, 418, 602, 502, 0, 418, 602, 0, 417, 602, 502, 0, 433, 602, 0, 0, 417, 602, 502]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(369, 8), (371, 640), (373, 22), (374, 1512), (375, 2566), (381, 4596), (383, 6388), (385, 0), (387, 12), (389, 0), (390, 37), (391, 142), (397, 340), (399, 852), (401, 0), (402, 50), (403, 248), (405, 0), (406, 452), (407, 748), (409, 252), (410, 273), (411, 1330), (413, 1088), (414, 2287), (415, 3118), (433, 582), (435, 1900), (437, 1663), (438, 2662), (439, 6445), (444, 793), (445, 8739), (447, 23580), (451, 16), (455, 256), (463, 1784), (467, 472), (470, 524), (471, 1072)]

theorem l369 : P.leaf 16 369 = 8 := by decide +kernel

theorem l371 : P.leaf 16 371 = 640 := by decide +kernel

theorem l373 : P.leaf 16 373 = 22 := by decide +kernel

theorem l374 : P.leaf 16 374 = 1512 := by decide +kernel

theorem l375 : P.leaf 16 375 = 2566 := by decide +kernel

theorem l381 : P.leaf 16 381 = 4596 := by decide +kernel

theorem l383 : P.leaf 16 383 = 6388 := by decide +kernel

theorem l385 : P.leaf 16 385 = 0 := by decide +kernel

theorem l387 : P.leaf 16 387 = 12 := by decide +kernel

theorem l389 : P.leaf 16 389 = 0 := by decide +kernel

theorem l390 : P.leaf 16 390 = 37 := by decide +kernel

theorem l391 : P.leaf 16 391 = 142 := by decide +kernel

theorem l397 : P.leaf 16 397 = 340 := by decide +kernel

theorem l399 : P.leaf 16 399 = 852 := by decide +kernel

theorem l401 : P.leaf 16 401 = 0 := by decide +kernel

theorem l402 : P.leaf 16 402 = 50 := by decide +kernel

theorem l403 : P.leaf 16 403 = 248 := by decide +kernel

theorem l405 : P.leaf 16 405 = 0 := by decide +kernel

theorem l406 : P.leaf 16 406 = 452 := by decide +kernel

theorem l407 : P.leaf 16 407 = 748 := by decide +kernel

theorem l409 : P.leaf 16 409 = 252 := by decide +kernel

theorem l410 : P.leaf 16 410 = 273 := by decide +kernel

theorem l411 : P.leaf 16 411 = 1330 := by decide +kernel

theorem l413 : P.leaf 16 413 = 1088 := by decide +kernel

theorem l414 : P.leaf 16 414 = 2287 := by decide +kernel

theorem l415 : P.leaf 16 415 = 3118 := by decide +kernel

theorem l433 : P.leaf 16 433 = 582 := by decide +kernel

theorem l435 : P.leaf 16 435 = 1900 := by decide +kernel

theorem l437 : P.leaf 16 437 = 1663 := by decide +kernel

theorem l438 : P.leaf 16 438 = 2662 := by decide +kernel

theorem l439 : P.leaf 16 439 = 6445 := by decide +kernel

theorem l444 : P.leaf 16 444 = 793 := by decide +kernel

theorem l445 : P.leaf 16 445 = 8739 := by decide +kernel

theorem l447 : P.leaf 16 447 = 23580 := by decide +kernel

theorem l451 : P.leaf 16 451 = 16 := by decide +kernel

theorem l455 : P.leaf 16 455 = 256 := by decide +kernel

theorem l463 : P.leaf 16 463 = 1784 := by decide +kernel

theorem l467 : P.leaf 16 467 = 472 := by decide +kernel

theorem l470 : P.leaf 16 470 = 524 := by decide +kernel

theorem l471 : P.leaf 16 471 = 1072 := by decide +kernel

theorem segOK : checkSeg 10 perms 369 475 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 250762 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 16) 369 475 310 250762 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l369 (.cons l371 (.cons l373 (.cons l374 (.cons l375 (.cons l381 (.cons l383 (.cons l385 (.cons l387 (.cons l389 (.cons l390 (.cons l391 (.cons l397 (.cons l399 (.cons l401 (.cons l402 (.cons l403 (.cons l405 (.cons l406 (.cons l407 (.cons l409 (.cons l410 (.cons l411 (.cons l413 (.cons l414 (.cons l415 (.cons l433 (.cons l435 (.cons l437 (.cons l438 (.cons l439 (.cons l444 (.cons l445 (.cons l447 (.cons l451 (.cons l455 (.cons l463 (.cons l467 (.cons l470 (.cons l471 (.nil))))))))))))))))))))))))))))))))))))))))))

end S2

end RACert.S0N3.C2
