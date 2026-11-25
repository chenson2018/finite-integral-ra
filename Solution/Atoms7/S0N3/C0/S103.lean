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

namespace S103

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439150, 48), (439151, 48), (439156, 48), (439157, 48), (439158, 48), (439159, 48), (439160, 24), (439161, 48), (439162, 48), (439163, 48), (439164, 48), (439165, 48), (439166, 48), (439167, 48), (439175, 48), (439179, 48), (439183, 48), (439189, 48), (439190, 48), (439191, 48), (439193, 48), (439194, 48), (439195, 48), (439197, 48), (439198, 48), (439199, 48), (439205, 48), (439206, 48), (439207, 48), (439209, 48), (439210, 48), (439211, 48), (439213, 48), (439214, 48), (439215, 48), (439220, 24), (439221, 48), (439222, 48), (439223, 48), (439225, 48), (439226, 48), (439227, 48), (439228, 48), (439229, 48), (439230, 48), (439231, 48), (439235, 16), (439239, 48), (439243, 48), (439247, 48), (439253, 48), (439254, 48), (439255, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 602, 0, 0, 602, 431, 602, 0, 0, 0, 0, 0, 0, 502, 602, 602, 502, 0, 0, 502, 0, 0, 602, 602, 602, 602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439150, 134), (439151, 300), (439156, 12), (439157, 122), (439158, 100), (439159, 228), (439160, 12), (439161, 72), (439162, 56), (439163, 240), (439164, 180), (439165, 238), (439166, 214), (439167, 396), (439179, 89), (439183, 156), (439193, 60), (439194, 12), (439195, 134), (439197, 148), (439198, 88), (439199, 264), (439210, 80), (439211, 184), (439214, 156), (439215, 300), (439225, 140), (439226, 128), (439227, 244), (439228, 188), (439229, 264), (439230, 236), (439231, 396), (439235, 729), (439239, 1022), (439243, 962), (439247, 1564), (439253, 677), (439254, 246), (439255, 1369)]

theorem l439150 : P.leaf 18 439150 = 134 := by decide +kernel

theorem l439151 : P.leaf 18 439151 = 300 := by decide +kernel

theorem l439156 : P.leaf 18 439156 = 12 := by decide +kernel

theorem l439157 : P.leaf 18 439157 = 122 := by decide +kernel

theorem l439158 : P.leaf 18 439158 = 100 := by decide +kernel

theorem l439159 : P.leaf 18 439159 = 228 := by decide +kernel

theorem l439160 : P.leaf 18 439160 = 12 := by decide +kernel

theorem l439161 : P.leaf 18 439161 = 72 := by decide +kernel

theorem l439162 : P.leaf 18 439162 = 56 := by decide +kernel

theorem l439163 : P.leaf 18 439163 = 240 := by decide +kernel

theorem l439164 : P.leaf 18 439164 = 180 := by decide +kernel

theorem l439165 : P.leaf 18 439165 = 238 := by decide +kernel

theorem l439166 : P.leaf 18 439166 = 214 := by decide +kernel

theorem l439167 : P.leaf 18 439167 = 396 := by decide +kernel

theorem l439179 : P.leaf 18 439179 = 89 := by decide +kernel

theorem l439183 : P.leaf 18 439183 = 156 := by decide +kernel

theorem l439193 : P.leaf 18 439193 = 60 := by decide +kernel

theorem l439194 : P.leaf 18 439194 = 12 := by decide +kernel

theorem l439195 : P.leaf 18 439195 = 134 := by decide +kernel

theorem l439197 : P.leaf 18 439197 = 148 := by decide +kernel

theorem l439198 : P.leaf 18 439198 = 88 := by decide +kernel

theorem l439199 : P.leaf 18 439199 = 264 := by decide +kernel

theorem l439210 : P.leaf 18 439210 = 80 := by decide +kernel

theorem l439211 : P.leaf 18 439211 = 184 := by decide +kernel

theorem l439214 : P.leaf 18 439214 = 156 := by decide +kernel

theorem l439215 : P.leaf 18 439215 = 300 := by decide +kernel

theorem l439225 : P.leaf 18 439225 = 140 := by decide +kernel

theorem l439226 : P.leaf 18 439226 = 128 := by decide +kernel

theorem l439227 : P.leaf 18 439227 = 244 := by decide +kernel

theorem l439228 : P.leaf 18 439228 = 188 := by decide +kernel

theorem l439229 : P.leaf 18 439229 = 264 := by decide +kernel

theorem l439230 : P.leaf 18 439230 = 236 := by decide +kernel

theorem l439231 : P.leaf 18 439231 = 396 := by decide +kernel

theorem l439235 : P.leaf 18 439235 = 729 := by decide +kernel

theorem l439239 : P.leaf 18 439239 = 1022 := by decide +kernel

theorem l439243 : P.leaf 18 439243 = 962 := by decide +kernel

theorem l439247 : P.leaf 18 439247 = 1564 := by decide +kernel

theorem l439253 : P.leaf 18 439253 = 677 := by decide +kernel

theorem l439254 : P.leaf 18 439254 = 246 := by decide +kernel

theorem l439255 : P.leaf 18 439255 = 1369 := by decide +kernel

theorem segOK : checkSeg 20 perms 439150 439257 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 559104 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439150 439257 2464 559104 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l439150 (.cons l439151 (.cons l439156 (.cons l439157 (.cons l439158 (.cons l439159 (.cons l439160 (.cons l439161 (.cons l439162 (.cons l439163 (.cons l439164 (.cons l439165 (.cons l439166 (.cons l439167 (.cons l439179 (.cons l439183 (.cons l439193 (.cons l439194 (.cons l439195 (.cons l439197 (.cons l439198 (.cons l439199 (.cons l439210 (.cons l439211 (.cons l439214 (.cons l439215 (.cons l439225 (.cons l439226 (.cons l439227 (.cons l439228 (.cons l439229 (.cons l439230 (.cons l439231 (.cons l439235 (.cons l439239 (.cons l439243 (.cons l439247 (.cons l439253 (.cons l439254 (.cons l439255 (.nil))))))))))))))))))))))))))))))))))))))))))

end S103

end RACert.S0N3.C0
