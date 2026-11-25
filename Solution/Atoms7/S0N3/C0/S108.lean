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

namespace S108

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(455131, 48), (455132, 48), (455133, 48), (455134, 48), (455135, 48), (455152, 24), (455153, 48), (455155, 24), (455156, 48), (455157, 48), (455158, 48), (455159, 48), (455164, 24), (455165, 48), (455167, 24), (455168, 24), (455169, 48), (455171, 24), (455172, 48), (455173, 48), (455174, 48), (455175, 48), (455180, 24), (455181, 48), (455183, 24), (455184, 48), (455185, 48), (455186, 48), (455187, 48), (455188, 48), (455189, 48), (455190, 48), (455191, 48), (455192, 48), (455193, 48), (455194, 48), (455195, 48), (455196, 48), (455197, 48), (455198, 48), (455199, 48), (455216, 24), (455217, 48), (455219, 24), (455220, 48), (455221, 48), (455222, 48), (455223, 48), (455228, 24), (455229, 48), (455231, 24), (455232, 48), (455233, 48), (455234, 48), (455235, 48), (455236, 48), (455237, 48), (455238, 48), (455239, 48), (455240, 48), (455241, 48), (455242, 48), (455243, 48), (455244, 48), (455245, 48), (455246, 48), (455247, 48), (455248, 48), (455249, 48), (455250, 48), (455251, 48), (455252, 48), (455253, 48), (455254, 48), (455255, 48), (455256, 48), (455257, 48), (455258, 48), (455259, 48), (455260, 48), (455261, 48), (455262, 48), (455263, 48), (455264, 48), (455265, 48), (455266, 48), (455267, 48), (455268, 48), (455269, 48), (455270, 48), (455271, 48), (455272, 48), (455273, 48), (455274, 48), (455275, 48), (455276, 48), (455277, 48), (455278, 48), (455279, 48), (455280, 48), (455281, 48), (455282, 48), (455283, 48), (455284, 48), (455285, 48), (455286, 48), (455287, 48), (455288, 48), (455289, 48), (455290, 48), (455291, 48), (455292, 48), (455293, 48), (455294, 48), (455295, 48), (455360, 24), (455361, 48), (455363, 24), (455364, 48), (455365, 48), (455366, 48), (455367, 48), (455372, 24), (455373, 48), (455375, 24), (455376, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 550, 0, 550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 434, 434, 424, 502, 550, 602, 502, 502, 0, 434, 434, 434, 434, 550, 602, 550, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 434, 434, 602, 602, 602, 602, 0, 0, 0, 418, 502, 550, 650, 424, 502, 550, 0, 418, 502, 550, 650, 502, 502, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 502, 502, 650, 650, 502, 502, 0, 0, 502, 502, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 418, 502, 0, 424, 502, 550, 0, 502, 502, 0, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(455131, 1479), (455133, 1730), (455135, 3649), (455152, 83), (455153, 272), (455155, 1648), (455156, 302), (455157, 1050), (455158, 1178), (455159, 2742), (455164, 1395), (455165, 2632), (455167, 7954), (455183, 20), (455197, 33), (455199, 80), (455228, 70), (455229, 102), (455231, 224), (455239, 38), (455247, 78), (455253, 51), (455255, 152), (455261, 102), (455263, 313), (455270, 25), (455271, 153), (455278, 102), (455279, 285), (455284, 24), (455285, 198), (455286, 82), (455287, 431), (455292, 184), (455293, 382), (455294, 422), (455295, 990), (455363, 34), (455367, 64), (455375, 152)]

theorem l455131 : P.leaf 18 455131 = 1479 := by decide +kernel

theorem l455133 : P.leaf 18 455133 = 1730 := by decide +kernel

theorem l455135 : P.leaf 18 455135 = 3649 := by decide +kernel

theorem l455152 : P.leaf 18 455152 = 83 := by decide +kernel

theorem l455153 : P.leaf 18 455153 = 272 := by decide +kernel

theorem l455155 : P.leaf 18 455155 = 1648 := by decide +kernel

theorem l455156 : P.leaf 18 455156 = 302 := by decide +kernel

theorem l455157 : P.leaf 18 455157 = 1050 := by decide +kernel

theorem l455158 : P.leaf 18 455158 = 1178 := by decide +kernel

theorem l455159 : P.leaf 18 455159 = 2742 := by decide +kernel

theorem l455164 : P.leaf 18 455164 = 1395 := by decide +kernel

theorem l455165 : P.leaf 18 455165 = 2632 := by decide +kernel

theorem l455167 : P.leaf 18 455167 = 7954 := by decide +kernel

theorem l455183 : P.leaf 18 455183 = 20 := by decide +kernel

theorem l455197 : P.leaf 18 455197 = 33 := by decide +kernel

theorem l455199 : P.leaf 18 455199 = 80 := by decide +kernel

theorem l455228 : P.leaf 18 455228 = 70 := by decide +kernel

theorem l455229 : P.leaf 18 455229 = 102 := by decide +kernel

theorem l455231 : P.leaf 18 455231 = 224 := by decide +kernel

theorem l455239 : P.leaf 18 455239 = 38 := by decide +kernel

theorem l455247 : P.leaf 18 455247 = 78 := by decide +kernel

theorem l455253 : P.leaf 18 455253 = 51 := by decide +kernel

theorem l455255 : P.leaf 18 455255 = 152 := by decide +kernel

theorem l455261 : P.leaf 18 455261 = 102 := by decide +kernel

theorem l455263 : P.leaf 18 455263 = 313 := by decide +kernel

theorem l455270 : P.leaf 18 455270 = 25 := by decide +kernel

theorem l455271 : P.leaf 18 455271 = 153 := by decide +kernel

theorem l455278 : P.leaf 18 455278 = 102 := by decide +kernel

theorem l455279 : P.leaf 18 455279 = 285 := by decide +kernel

theorem l455284 : P.leaf 18 455284 = 24 := by decide +kernel

theorem l455285 : P.leaf 18 455285 = 198 := by decide +kernel

theorem l455286 : P.leaf 18 455286 = 82 := by decide +kernel

theorem l455287 : P.leaf 18 455287 = 431 := by decide +kernel

theorem l455292 : P.leaf 18 455292 = 184 := by decide +kernel

theorem l455293 : P.leaf 18 455293 = 382 := by decide +kernel

theorem l455294 : P.leaf 18 455294 = 422 := by decide +kernel

theorem l455295 : P.leaf 18 455295 = 990 := by decide +kernel

theorem l455363 : P.leaf 18 455363 = 34 := by decide +kernel

theorem l455367 : P.leaf 18 455367 = 64 := by decide +kernel

theorem l455375 : P.leaf 18 455375 = 152 := by decide +kernel

theorem segOK : checkSeg 20 perms 455131 455377 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1205520 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 455131 455377 5664 1205520 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l455131 (.cons l455133 (.cons l455135 (.cons l455152 (.cons l455153 (.cons l455155 (.cons l455156 (.cons l455157 (.cons l455158 (.cons l455159 (.cons l455164 (.cons l455165 (.cons l455167 (.cons l455183 (.cons l455197 (.cons l455199 (.cons l455228 (.cons l455229 (.cons l455231 (.cons l455239 (.cons l455247 (.cons l455253 (.cons l455255 (.cons l455261 (.cons l455263 (.cons l455270 (.cons l455271 (.cons l455278 (.cons l455279 (.cons l455284 (.cons l455285 (.cons l455286 (.cons l455287 (.cons l455292 (.cons l455293 (.cons l455294 (.cons l455295 (.cons l455363 (.cons l455367 (.cons l455375 (.nil))))))))))))))))))))))))))))))))))))))))))

end S108

end RACert.S0N3.C0
