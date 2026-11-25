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

namespace S131

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(521135, 48), (521140, 24), (521141, 48), (521142, 48), (521143, 48), (521145, 48), (521146, 48), (521147, 48), (521148, 48), (521149, 48), (521150, 48), (521151, 48), (521155, 16), (521159, 48), (521163, 48), (521167, 48), (521173, 48), (521174, 48), (521175, 48), (521177, 48), (521178, 48), (521179, 48), (521181, 48), (521182, 48), (521183, 48), (521189, 48), (521190, 48), (521191, 48), (521193, 48), (521194, 48), (521195, 48), (521197, 48), (521198, 48), (521199, 48), (521205, 48), (521206, 48), (521207, 48), (521209, 48), (521210, 48), (521211, 48), (521212, 24), (521213, 48), (521214, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(521135, 2524), (521140, 404), (521141, 940), (521142, 1318), (521143, 1432), (521145, 998), (521146, 1394), (521147, 1550), (521148, 1640), (521149, 1760), (521150, 2404), (521151, 3316), (521155, 1452), (521159, 2931), (521163, 2048), (521167, 3656), (521173, 3135), (521174, 3988), (521175, 6051), (521177, 2190), (521178, 2686), (521179, 4262), (521181, 4263), (521182, 5267), (521183, 11490), (521190, 3617), (521191, 4031), (521194, 2650), (521195, 2886), (521198, 5235), (521199, 6884), (521205, 3342), (521206, 5524), (521207, 6646), (521209, 2320), (521210, 3768), (521211, 4636), (521212, 3560), (521213, 4586), (521214, 7218)]

theorem l521135 : P.leaf 18 521135 = 2524 := by decide +kernel

theorem l521140 : P.leaf 18 521140 = 404 := by decide +kernel

theorem l521141 : P.leaf 18 521141 = 940 := by decide +kernel

theorem l521142 : P.leaf 18 521142 = 1318 := by decide +kernel

theorem l521143 : P.leaf 18 521143 = 1432 := by decide +kernel

theorem l521145 : P.leaf 18 521145 = 998 := by decide +kernel

theorem l521146 : P.leaf 18 521146 = 1394 := by decide +kernel

theorem l521147 : P.leaf 18 521147 = 1550 := by decide +kernel

theorem l521148 : P.leaf 18 521148 = 1640 := by decide +kernel

theorem l521149 : P.leaf 18 521149 = 1760 := by decide +kernel

theorem l521150 : P.leaf 18 521150 = 2404 := by decide +kernel

theorem l521151 : P.leaf 18 521151 = 3316 := by decide +kernel

theorem l521155 : P.leaf 18 521155 = 1452 := by decide +kernel

theorem l521159 : P.leaf 18 521159 = 2931 := by decide +kernel

theorem l521163 : P.leaf 18 521163 = 2048 := by decide +kernel

theorem l521167 : P.leaf 18 521167 = 3656 := by decide +kernel

theorem l521173 : P.leaf 18 521173 = 3135 := by decide +kernel

theorem l521174 : P.leaf 18 521174 = 3988 := by decide +kernel

theorem l521175 : P.leaf 18 521175 = 6051 := by decide +kernel

theorem l521177 : P.leaf 18 521177 = 2190 := by decide +kernel

theorem l521178 : P.leaf 18 521178 = 2686 := by decide +kernel

theorem l521179 : P.leaf 18 521179 = 4262 := by decide +kernel

theorem l521181 : P.leaf 18 521181 = 4263 := by decide +kernel

theorem l521182 : P.leaf 18 521182 = 5267 := by decide +kernel

theorem l521183 : P.leaf 18 521183 = 11490 := by decide +kernel

theorem l521190 : P.leaf 18 521190 = 3617 := by decide +kernel

theorem l521191 : P.leaf 18 521191 = 4031 := by decide +kernel

theorem l521194 : P.leaf 18 521194 = 2650 := by decide +kernel

theorem l521195 : P.leaf 18 521195 = 2886 := by decide +kernel

theorem l521198 : P.leaf 18 521198 = 5235 := by decide +kernel

theorem l521199 : P.leaf 18 521199 = 6884 := by decide +kernel

theorem l521205 : P.leaf 18 521205 = 3342 := by decide +kernel

theorem l521206 : P.leaf 18 521206 = 5524 := by decide +kernel

theorem l521207 : P.leaf 18 521207 = 6646 := by decide +kernel

theorem l521209 : P.leaf 18 521209 = 2320 := by decide +kernel

theorem l521210 : P.leaf 18 521210 = 3768 := by decide +kernel

theorem l521211 : P.leaf 18 521211 = 4636 := by decide +kernel

theorem l521212 : P.leaf 18 521212 = 3560 := by decide +kernel

theorem l521213 : P.leaf 18 521213 = 4586 := by decide +kernel

theorem l521214 : P.leaf 18 521214 = 7218 := by decide +kernel

theorem segOK : checkSeg 20 perms 521135 521215 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 6578496 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 521135 521215 1984 6578496 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l521135 (.cons l521140 (.cons l521141 (.cons l521142 (.cons l521143 (.cons l521145 (.cons l521146 (.cons l521147 (.cons l521148 (.cons l521149 (.cons l521150 (.cons l521151 (.cons l521155 (.cons l521159 (.cons l521163 (.cons l521167 (.cons l521173 (.cons l521174 (.cons l521175 (.cons l521177 (.cons l521178 (.cons l521179 (.cons l521181 (.cons l521182 (.cons l521183 (.cons l521190 (.cons l521191 (.cons l521194 (.cons l521195 (.cons l521198 (.cons l521199 (.cons l521205 (.cons l521206 (.cons l521207 (.cons l521209 (.cons l521210 (.cons l521211 (.cons l521212 (.cons l521213 (.cons l521214 (.nil))))))))))))))))))))))))))))))))))))))))))

end S131

end RACert.S0N3.C0
