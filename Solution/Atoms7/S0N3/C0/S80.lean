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

theorem l243103 : P.leaf 18 243103 = 840 := by decide +kernel

theorem l243106 : P.leaf 18 243106 = 30 := by decide +kernel

theorem l243107 : P.leaf 18 243107 = 120 := by decide +kernel

theorem l243110 : P.leaf 18 243110 = 207 := by decide +kernel

theorem l243111 : P.leaf 18 243111 = 712 := by decide +kernel

theorem l243114 : P.leaf 18 243114 = 133 := by decide +kernel

theorem l243115 : P.leaf 18 243115 = 480 := by decide +kernel

theorem l243118 : P.leaf 18 243118 = 446 := by decide +kernel

theorem l243119 : P.leaf 18 243119 = 1390 := by decide +kernel

theorem l243121 : P.leaf 18 243121 = 84 := by decide +kernel

theorem l243122 : P.leaf 18 243122 = 72 := by decide +kernel

theorem l243123 : P.leaf 18 243123 = 198 := by decide +kernel

theorem l243125 : P.leaf 18 243125 = 808 := by decide +kernel

theorem l243126 : P.leaf 18 243126 = 441 := by decide +kernel

theorem l243127 : P.leaf 18 243127 = 1356 := by decide +kernel

theorem l243129 : P.leaf 18 243129 = 480 := by decide +kernel

theorem l243130 : P.leaf 18 243130 = 263 := by decide +kernel

theorem l243131 : P.leaf 18 243131 = 804 := by decide +kernel

theorem l243133 : P.leaf 18 243133 = 1318 := by decide +kernel

theorem l243134 : P.leaf 18 243134 = 746 := by decide +kernel

theorem l243135 : P.leaf 18 243135 = 2448 := by decide +kernel

theorem l243138 : P.leaf 18 243138 = 2 := by decide +kernel

theorem l243139 : P.leaf 18 243139 = 22 := by decide +kernel

theorem l243143 : P.leaf 18 243143 = 160 := by decide +kernel

theorem l243146 : P.leaf 18 243146 = 18 := by decide +kernel

theorem l243147 : P.leaf 18 243147 = 66 := by decide +kernel

theorem l243151 : P.leaf 18 243151 = 168 := by decide +kernel

theorem l243154 : P.leaf 18 243154 = 0 := by decide +kernel

theorem l243155 : P.leaf 18 243155 = 95 := by decide +kernel

theorem l243159 : P.leaf 18 243159 = 944 := by decide +kernel

theorem l243162 : P.leaf 18 243162 = 30 := by decide +kernel

theorem l243163 : P.leaf 18 243163 = 331 := by decide +kernel

theorem l243165 : P.leaf 18 243165 = 816 := by decide +kernel

theorem l243167 : P.leaf 18 243167 = 1237 := by decide +kernel

theorem l243170 : P.leaf 18 243170 = 52 := by decide +kernel

theorem l243171 : P.leaf 18 243171 = 173 := by decide +kernel

theorem l243174 : P.leaf 18 243174 = 453 := by decide +kernel

theorem l243175 : P.leaf 18 243175 = 1616 := by decide +kernel

theorem l243178 : P.leaf 18 243178 = 210 := by decide +kernel

theorem l243179 : P.leaf 18 243179 = 621 := by decide +kernel

theorem segOK : checkSeg 20 perms 243103 243182 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 959136 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 243103 243182 2472 959136 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l243103 (.cons l243106 (.cons l243107 (.cons l243110 (.cons l243111 (.cons l243114 (.cons l243115 (.cons l243118 (.cons l243119 (.cons l243121 (.cons l243122 (.cons l243123 (.cons l243125 (.cons l243126 (.cons l243127 (.cons l243129 (.cons l243130 (.cons l243131 (.cons l243133 (.cons l243134 (.cons l243135 (.cons l243138 (.cons l243139 (.cons l243143 (.cons l243146 (.cons l243147 (.cons l243151 (.cons l243154 (.cons l243155 (.cons l243159 (.cons l243162 (.cons l243163 (.cons l243165 (.cons l243167 (.cons l243170 (.cons l243171 (.cons l243174 (.cons l243175 (.cons l243178 (.cons l243179 (.nil))))))))))))))))))))))))))))))))))))))))))

end S80

end RACert.S0N3.C0
