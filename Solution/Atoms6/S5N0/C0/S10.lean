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

namespace S10

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(8138, 120), (8139, 120), (8142, 60), (8143, 60), (8152, 30), (8153, 30), (8154, 60), (8155, 60), (8158, 30), (8159, 30), (8160, 30), (8161, 30), (8162, 60), (8163, 60), (8166, 30), (8167, 30), (8168, 60), (8169, 60), (8170, 120), (8171, 120), (8174, 60), (8175, 60), (8184, 30), (8185, 30), (8186, 60), (8187, 60), (8190, 30), (8191, 30), (16224, 15), (16225, 60), (16227, 30), (16229, 60), (16231, 60), (16239, 15), (16240, 15), (16241, 60), (16243, 30), (16245, 60), (16247, 60), (16255, 15)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(8138, 37788), (8139, 67209), (8142, 46621), (8143, 81504), (8152, 36532), (8153, 67012), (8154, 44702), (8155, 80524), (8158, 55209), (8159, 97659), (8160, 50379), (8161, 114236), (8162, 68278), (8163, 155112), (8166, 94980), (8167, 216568), (8168, 54790), (8169, 127481), (8170, 74862), (8171, 174338), (8174, 104784), (8175, 244720), (8184, 59473), (8185, 141673), (8186, 81940), (8187, 195092), (8190, 115524), (8191, 275312), (16224, 54855), (16225, 75598), (16227, 100791), (16229, 107824), (16231, 148456), (16239, 209065), (16240, 63623), (16241, 87654), (16243, 117057), (16245, 124780), (16247, 171954), (16255, 242153)]

theorem leavesOK : P.checkLeaves 20 live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 8138 16352 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 217430070 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 8138 16352 2040 217430070 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S10

end RACert.S5N0.C0
