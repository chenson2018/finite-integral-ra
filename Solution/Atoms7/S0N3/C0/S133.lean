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

namespace S133

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(521695, 48), (521701, 48), (521703, 48), (521705, 48), (521707, 48), (521709, 48), (521711, 48), (521717, 48), (521718, 48), (521719, 48), (521721, 48), (521722, 48), (521723, 48), (521725, 48), (521726, 48), (521727, 48), (521818, 24), (521819, 48), (521822, 48), (521823, 48), (521833, 8), (521835, 48), (521839, 24), (521851, 24), (521853, 48), (521854, 48), (521855, 48), (521878, 24), (521879, 48), (521887, 24), (521909, 48), (521910, 48), (521911, 48), (521917, 48), (521918, 48), (521919, 48), (521973, 48), (521974, 24), (521975, 48), (521977, 24), (521979, 48), (521983, 24), (522078, 24), (522079, 48), (522095, 48), (522111, 24), (522134, 48), (522135, 48), (522142, 48), (522143, 48), (522151, 48), (522159, 48), (522165, 24), (522166, 48), (522167, 48), (522173, 48), (522174, 48), (522175, 48), (522198, 48), (522199, 48), (522203, 48), (522206, 48), (522207, 48), (522219, 16), (522223, 48), (522230, 48), (522231, 48), (522237, 24), (522238, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 502, 0, 502, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650, 650, 1350, 1350, 502, 650, 1350, 650, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 1350, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(521695, 11337), (521703, 4977), (521707, 3555), (521711, 7932), (521717, 5181), (521718, 7835), (521719, 10127), (521721, 3537), (521722, 5245), (521723, 6917), (521725, 6873), (521726, 10235), (521727, 17154), (522078, 2965), (522079, 6520), (522095, 4412), (522111, 11517), (522134, 2703), (522135, 5643), (522142, 4641), (522143, 10625), (522151, 3657), (522159, 6676), (522165, 4544), (522166, 6937), (522167, 10214), (522173, 6514), (522174, 10470), (522175, 17437), (522198, 5623), (522199, 8661), (522203, 5859), (522206, 6919), (522207, 14429), (522219, 4035), (522223, 8977), (522230, 11025), (522231, 13921), (522237, 8540), (522238, 13644)]

theorem l521695 : P.leaf 18 521695 = 11337 := by decide +kernel

theorem l521703 : P.leaf 18 521703 = 4977 := by decide +kernel

theorem l521707 : P.leaf 18 521707 = 3555 := by decide +kernel

theorem l521711 : P.leaf 18 521711 = 7932 := by decide +kernel

theorem l521717 : P.leaf 18 521717 = 5181 := by decide +kernel

theorem l521718 : P.leaf 18 521718 = 7835 := by decide +kernel

theorem l521719 : P.leaf 18 521719 = 10127 := by decide +kernel

theorem l521721 : P.leaf 18 521721 = 3537 := by decide +kernel

theorem l521722 : P.leaf 18 521722 = 5245 := by decide +kernel

theorem l521723 : P.leaf 18 521723 = 6917 := by decide +kernel

theorem l521725 : P.leaf 18 521725 = 6873 := by decide +kernel

theorem l521726 : P.leaf 18 521726 = 10235 := by decide +kernel

theorem l521727 : P.leaf 18 521727 = 17154 := by decide +kernel

theorem l522078 : P.leaf 18 522078 = 2965 := by decide +kernel

theorem l522079 : P.leaf 18 522079 = 6520 := by decide +kernel

theorem l522095 : P.leaf 18 522095 = 4412 := by decide +kernel

theorem l522111 : P.leaf 18 522111 = 11517 := by decide +kernel

theorem l522134 : P.leaf 18 522134 = 2703 := by decide +kernel

theorem l522135 : P.leaf 18 522135 = 5643 := by decide +kernel

theorem l522142 : P.leaf 18 522142 = 4641 := by decide +kernel

theorem l522143 : P.leaf 18 522143 = 10625 := by decide +kernel

theorem l522151 : P.leaf 18 522151 = 3657 := by decide +kernel

theorem l522159 : P.leaf 18 522159 = 6676 := by decide +kernel

theorem l522165 : P.leaf 18 522165 = 4544 := by decide +kernel

theorem l522166 : P.leaf 18 522166 = 6937 := by decide +kernel

theorem l522167 : P.leaf 18 522167 = 10214 := by decide +kernel

theorem l522173 : P.leaf 18 522173 = 6514 := by decide +kernel

theorem l522174 : P.leaf 18 522174 = 10470 := by decide +kernel

theorem l522175 : P.leaf 18 522175 = 17437 := by decide +kernel

theorem l522198 : P.leaf 18 522198 = 5623 := by decide +kernel

theorem l522199 : P.leaf 18 522199 = 8661 := by decide +kernel

theorem l522203 : P.leaf 18 522203 = 5859 := by decide +kernel

theorem l522206 : P.leaf 18 522206 = 6919 := by decide +kernel

theorem l522207 : P.leaf 18 522207 = 14429 := by decide +kernel

theorem l522219 : P.leaf 18 522219 = 4035 := by decide +kernel

theorem l522223 : P.leaf 18 522223 = 8977 := by decide +kernel

theorem l522230 : P.leaf 18 522230 = 11025 := by decide +kernel

theorem l522231 : P.leaf 18 522231 = 13921 := by decide +kernel

theorem l522237 : P.leaf 18 522237 = 8540 := by decide +kernel

theorem l522238 : P.leaf 18 522238 = 13644 := by decide +kernel

theorem segOK : checkSeg 20 perms 521695 522239 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 14473920 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 521695 522239 2952 14473920 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l521695 (.cons l521703 (.cons l521707 (.cons l521711 (.cons l521717 (.cons l521718 (.cons l521719 (.cons l521721 (.cons l521722 (.cons l521723 (.cons l521725 (.cons l521726 (.cons l521727 (.cons l522078 (.cons l522079 (.cons l522095 (.cons l522111 (.cons l522134 (.cons l522135 (.cons l522142 (.cons l522143 (.cons l522151 (.cons l522159 (.cons l522165 (.cons l522166 (.cons l522167 (.cons l522173 (.cons l522174 (.cons l522175 (.cons l522198 (.cons l522199 (.cons l522203 (.cons l522206 (.cons l522207 (.cons l522219 (.cons l522223 (.cons l522230 (.cons l522231 (.cons l522237 (.cons l522238 (.nil))))))))))))))))))))))))))))))))))))))))))

end S133

end RACert.S0N3.C0
