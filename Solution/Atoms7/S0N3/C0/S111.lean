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

namespace S111

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(456053, 48), (456054, 48), (456055, 48), (456056, 48), (456057, 48), (456058, 48), (456059, 48), (456060, 48), (456061, 48), (456062, 48), (456063, 48), (456128, 24), (456129, 48), (456131, 24), (456132, 48), (456133, 48), (456134, 48), (456135, 48), (456140, 24), (456141, 48), (456143, 24), (456144, 48), (456145, 48), (456146, 48), (456147, 48), (456148, 48), (456149, 48), (456150, 48), (456151, 48), (456152, 48), (456153, 48), (456154, 48), (456155, 48), (456156, 48), (456157, 48), (456158, 48), (456159, 48), (456176, 24), (456177, 48), (456179, 24), (456180, 48), (456181, 48), (456182, 48), (456183, 48), (456188, 24), (456189, 48), (456191, 24), (456192, 12), (456193, 48), (456195, 24), (456197, 24), (456198, 24), (456199, 48), (456207, 12), (456208, 48), (456209, 48), (456210, 48), (456211, 48), (456212, 48), (456213, 48), (456214, 48), (456215, 48), (456216, 48), (456217, 48), (456218, 48), (456219, 48), (456220, 48), (456221, 48), (456222, 48), (456223, 48), (456240, 24), (456241, 48), (456243, 24), (456244, 48), (456245, 48), (456246, 48), (456247, 48), (456252, 24), (456253, 48), (456255, 24), (456272, 24), (456273, 48), (456274, 48), (456275, 48), (456277, 24), (456278, 48), (456279, 48), (456282, 24), (456283, 48), (456287, 24), (456288, 24), (456289, 48), (456290, 48), (456291, 48), (456293, 48), (456294, 24), (456295, 48), (456297, 24), (456299, 48), (456303, 24), (456304, 48), (456305, 48), (456306, 48), (456307, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 418, 502, 0, 418, 502, 550, 0, 502, 502, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 440, 602, 502, 550, 602, 0, 434, 440, 434, 602, 550, 602, 550, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 440, 602, 602, 602, 602, 602, 0, 0, 0, 550, 650, 550, 650, 0, 550, 0, 550, 650, 0, 502, 502, 650, 650, 502, 0, 0, 502, 650, 0, 650, 650, 650, 650]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(456053, 1251), (456054, 1262), (456055, 3139), (456060, 1072), (456061, 2633), (456062, 2583), (456063, 6180), (456131, 352), (456135, 538), (456143, 742), (456145, 210), (456147, 1408), (456149, 1153), (456151, 2285), (456153, 1129), (456155, 2317), (456157, 2601), (456159, 4717), (456176, 113), (456177, 352), (456179, 2494), (456180, 380), (456181, 2052), (456182, 2276), (456183, 4757), (456188, 1832), (456189, 4601), (456191, 11248), (456207, 64), (456221, 76), (456223, 168), (456252, 130), (456253, 250), (456255, 538), (456277, 79), (456279, 240), (456287, 608), (456294, 49), (456295, 285), (456303, 592)]

theorem l456053 : P.leaf 18 456053 = 1251 := by decide +kernel

theorem l456054 : P.leaf 18 456054 = 1262 := by decide +kernel

theorem l456055 : P.leaf 18 456055 = 3139 := by decide +kernel

theorem l456060 : P.leaf 18 456060 = 1072 := by decide +kernel

theorem l456061 : P.leaf 18 456061 = 2633 := by decide +kernel

theorem l456062 : P.leaf 18 456062 = 2583 := by decide +kernel

theorem l456063 : P.leaf 18 456063 = 6180 := by decide +kernel

theorem l456131 : P.leaf 18 456131 = 352 := by decide +kernel

theorem l456135 : P.leaf 18 456135 = 538 := by decide +kernel

theorem l456143 : P.leaf 18 456143 = 742 := by decide +kernel

theorem l456145 : P.leaf 18 456145 = 210 := by decide +kernel

theorem l456147 : P.leaf 18 456147 = 1408 := by decide +kernel

theorem l456149 : P.leaf 18 456149 = 1153 := by decide +kernel

theorem l456151 : P.leaf 18 456151 = 2285 := by decide +kernel

theorem l456153 : P.leaf 18 456153 = 1129 := by decide +kernel

theorem l456155 : P.leaf 18 456155 = 2317 := by decide +kernel

theorem l456157 : P.leaf 18 456157 = 2601 := by decide +kernel

theorem l456159 : P.leaf 18 456159 = 4717 := by decide +kernel

theorem l456176 : P.leaf 18 456176 = 113 := by decide +kernel

theorem l456177 : P.leaf 18 456177 = 352 := by decide +kernel

theorem l456179 : P.leaf 18 456179 = 2494 := by decide +kernel

theorem l456180 : P.leaf 18 456180 = 380 := by decide +kernel

theorem l456181 : P.leaf 18 456181 = 2052 := by decide +kernel

theorem l456182 : P.leaf 18 456182 = 2276 := by decide +kernel

theorem l456183 : P.leaf 18 456183 = 4757 := by decide +kernel

theorem l456188 : P.leaf 18 456188 = 1832 := by decide +kernel

theorem l456189 : P.leaf 18 456189 = 4601 := by decide +kernel

theorem l456191 : P.leaf 18 456191 = 11248 := by decide +kernel

theorem l456207 : P.leaf 18 456207 = 64 := by decide +kernel

theorem l456221 : P.leaf 18 456221 = 76 := by decide +kernel

theorem l456223 : P.leaf 18 456223 = 168 := by decide +kernel

theorem l456252 : P.leaf 18 456252 = 130 := by decide +kernel

theorem l456253 : P.leaf 18 456253 = 250 := by decide +kernel

theorem l456255 : P.leaf 18 456255 = 538 := by decide +kernel

theorem l456277 : P.leaf 18 456277 = 79 := by decide +kernel

theorem l456279 : P.leaf 18 456279 = 240 := by decide +kernel

theorem l456287 : P.leaf 18 456287 = 608 := by decide +kernel

theorem l456294 : P.leaf 18 456294 = 49 := by decide +kernel

theorem l456295 : P.leaf 18 456295 = 285 := by decide +kernel

theorem l456303 : P.leaf 18 456303 = 592 := by decide +kernel

theorem segOK : checkSeg 20 perms 456053 456308 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2847336 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 456053 456308 4368 2847336 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l456053 (.cons l456054 (.cons l456055 (.cons l456060 (.cons l456061 (.cons l456062 (.cons l456063 (.cons l456131 (.cons l456135 (.cons l456143 (.cons l456145 (.cons l456147 (.cons l456149 (.cons l456151 (.cons l456153 (.cons l456155 (.cons l456157 (.cons l456159 (.cons l456176 (.cons l456177 (.cons l456179 (.cons l456180 (.cons l456181 (.cons l456182 (.cons l456183 (.cons l456188 (.cons l456189 (.cons l456191 (.cons l456207 (.cons l456221 (.cons l456223 (.cons l456252 (.cons l456253 (.cons l456255 (.cons l456277 (.cons l456279 (.cons l456287 (.cons l456294 (.cons l456295 (.cons l456303 (.nil))))))))))))))))))))))))))))))))))))))))))

end S111

end RACert.S0N3.C0
