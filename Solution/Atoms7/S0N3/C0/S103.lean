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

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 439150 439257 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 559104 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439150 439257 2464 559104 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S103

end RACert.S0N3.C0
