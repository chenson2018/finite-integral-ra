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

namespace S80

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(243103, 48), (243105, 48), (243106, 48), (243107, 48), (243109, 48), (243110, 48), (243111, 48), (243113, 48), (243114, 48), (243115, 48), (243117, 48), (243118, 48), (243119, 48), (243121, 48), (243122, 48), (243123, 48), (243125, 48), (243126, 48), (243127, 48), (243129, 48), (243130, 48), (243131, 48), (243133, 48), (243134, 48), (243135, 48), (243138, 48), (243139, 48), (243142, 48), (243143, 48), (243146, 48), (243147, 48), (243150, 48), (243151, 48), (243154, 48), (243155, 48), (243158, 48), (243159, 48), (243162, 48), (243163, 48), (243165, 24), (243166, 48), (243167, 48), (243169, 48), (243170, 48), (243171, 48), (243173, 48), (243174, 48), (243175, 48), (243177, 48), (243178, 48), (243179, 48), (243181, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 424, 0, 0, 0, 424, 0, 0, 0, 424, 0, 0, 0, 0, 424, 0, 502, 0, 0, 502, 0, 0, 502, 0, 0, 502]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(243103, 840), (243106, 30), (243107, 120), (243110, 207), (243111, 712), (243114, 133), (243115, 480), (243118, 446), (243119, 1390), (243121, 84), (243122, 72), (243123, 198), (243125, 808), (243126, 441), (243127, 1356), (243129, 480), (243130, 263), (243131, 804), (243133, 1318), (243134, 746), (243135, 2448), (243138, 2), (243139, 22), (243143, 160), (243146, 18), (243147, 66), (243151, 168), (243154, 0), (243155, 95), (243159, 944), (243162, 30), (243163, 331), (243165, 816), (243167, 1237), (243170, 52), (243171, 173), (243174, 453), (243175, 1616), (243178, 210), (243179, 621)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 243103 243182 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 959136 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 243103 243182 2472 959136 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S80

end RACert.S0N3.C0
