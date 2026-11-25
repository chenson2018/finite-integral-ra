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

namespace S79

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(242967, 48), (242969, 48), (242970, 48), (242971, 48), (242973, 48), (242974, 48), (242975, 48), (242977, 48), (242978, 48), (242979, 48), (242981, 48), (242982, 48), (242983, 48), (242985, 48), (242986, 48), (242987, 48), (242989, 48), (242990, 48), (242991, 48), (242993, 48), (242994, 48), (242995, 48), (242997, 48), (242998, 48), (242999, 48), (243001, 48), (243002, 48), (243003, 48), (243005, 48), (243006, 48), (243007, 48), (243010, 48), (243011, 48), (243014, 48), (243015, 48), (243018, 48), (243019, 48), (243022, 48), (243023, 48), (243026, 48), (243027, 48), (243029, 48), (243030, 48), (243031, 48), (243033, 24), (243034, 48), (243035, 48), (243037, 48), (243038, 48), (243039, 48), (243041, 48), (243042, 48), (243043, 48), (243045, 48), (243046, 48), (243047, 48), (243049, 48), (243050, 48), (243051, 48), (243053, 48), (243054, 48), (243055, 48), (243057, 48), (243058, 48), (243059, 48), (243061, 48), (243062, 48), (243063, 48), (243065, 48), (243066, 48), (243067, 48), (243069, 48), (243070, 48), (243071, 48), (243074, 48), (243075, 48), (243078, 48), (243079, 48), (243082, 48), (243083, 48), (243086, 48), (243087, 48), (243090, 48), (243091, 48), (243093, 24), (243094, 48), (243095, 48), (243098, 48), (243099, 48), (243101, 48), (243102, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 439, 426, 440, 0, 424, 0, 439, 434, 440, 502, 0, 0, 439, 438, 440, 502, 0, 0, 439, 434, 440, 0, 0, 0, 439, 438, 440, 0, 0, 0, 440, 440, 424, 669, 426, 440, 424, 669, 440, 440, 0, 424, 0, 439, 426, 440, 0, 424, 0, 439, 440, 440, 502, 0, 0, 439, 438, 440, 502, 0, 0, 439, 440, 440, 0, 0, 0, 439, 438, 440, 0, 0, 0, 0, 0, 424, 0, 0, 0, 424, 0, 0, 0, 0, 424, 0, 0, 0, 0, 424]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(242967, 48), (242973, 40), (242975, 64), (242982, 14), (242983, 78), (242990, 24), (242991, 120), (242997, 72), (242998, 18), (242999, 132), (243005, 96), (243006, 24), (243007, 176), (243029, 129), (243031, 252), (243037, 192), (243039, 330), (243046, 77), (243047, 415), (243054, 127), (243055, 540), (243061, 336), (243062, 112), (243063, 766), (243069, 436), (243070, 146), (243071, 936), (243074, 2), (243075, 18), (243079, 108), (243082, 18), (243083, 58), (243087, 132), (243090, 0), (243091, 49), (243093, 236), (243095, 403), (243098, 24), (243099, 249), (243101, 568)]

theorem l242967 : P.leaf 18 242967 = 48 := by decide +kernel

theorem l242973 : P.leaf 18 242973 = 40 := by decide +kernel

theorem l242975 : P.leaf 18 242975 = 64 := by decide +kernel

theorem l242982 : P.leaf 18 242982 = 14 := by decide +kernel

theorem l242983 : P.leaf 18 242983 = 78 := by decide +kernel

theorem l242990 : P.leaf 18 242990 = 24 := by decide +kernel

theorem l242991 : P.leaf 18 242991 = 120 := by decide +kernel

theorem l242997 : P.leaf 18 242997 = 72 := by decide +kernel

theorem l242998 : P.leaf 18 242998 = 18 := by decide +kernel

theorem l242999 : P.leaf 18 242999 = 132 := by decide +kernel

theorem l243005 : P.leaf 18 243005 = 96 := by decide +kernel

theorem l243006 : P.leaf 18 243006 = 24 := by decide +kernel

theorem l243007 : P.leaf 18 243007 = 176 := by decide +kernel

theorem l243029 : P.leaf 18 243029 = 129 := by decide +kernel

theorem l243031 : P.leaf 18 243031 = 252 := by decide +kernel

theorem l243037 : P.leaf 18 243037 = 192 := by decide +kernel

theorem l243039 : P.leaf 18 243039 = 330 := by decide +kernel

theorem l243046 : P.leaf 18 243046 = 77 := by decide +kernel

theorem l243047 : P.leaf 18 243047 = 415 := by decide +kernel

theorem l243054 : P.leaf 18 243054 = 127 := by decide +kernel

theorem l243055 : P.leaf 18 243055 = 540 := by decide +kernel

theorem l243061 : P.leaf 18 243061 = 336 := by decide +kernel

theorem l243062 : P.leaf 18 243062 = 112 := by decide +kernel

theorem l243063 : P.leaf 18 243063 = 766 := by decide +kernel

theorem l243069 : P.leaf 18 243069 = 436 := by decide +kernel

theorem l243070 : P.leaf 18 243070 = 146 := by decide +kernel

theorem l243071 : P.leaf 18 243071 = 936 := by decide +kernel

theorem l243074 : P.leaf 18 243074 = 2 := by decide +kernel

theorem l243075 : P.leaf 18 243075 = 18 := by decide +kernel

theorem l243079 : P.leaf 18 243079 = 108 := by decide +kernel

theorem l243082 : P.leaf 18 243082 = 18 := by decide +kernel

theorem l243083 : P.leaf 18 243083 = 58 := by decide +kernel

theorem l243087 : P.leaf 18 243087 = 132 := by decide +kernel

theorem l243090 : P.leaf 18 243090 = 0 := by decide +kernel

theorem l243091 : P.leaf 18 243091 = 49 := by decide +kernel

theorem l243093 : P.leaf 18 243093 = 236 := by decide +kernel

theorem l243095 : P.leaf 18 243095 = 403 := by decide +kernel

theorem l243098 : P.leaf 18 243098 = 24 := by decide +kernel

theorem l243099 : P.leaf 18 243099 = 249 := by decide +kernel

theorem l243101 : P.leaf 18 243101 = 568 := by decide +kernel

theorem segOK : checkSeg 20 perms 242967 243103 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 357456 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 242967 243103 4320 357456 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l242967 (.cons l242973 (.cons l242975 (.cons l242982 (.cons l242983 (.cons l242990 (.cons l242991 (.cons l242997 (.cons l242998 (.cons l242999 (.cons l243005 (.cons l243006 (.cons l243007 (.cons l243029 (.cons l243031 (.cons l243037 (.cons l243039 (.cons l243046 (.cons l243047 (.cons l243054 (.cons l243055 (.cons l243061 (.cons l243062 (.cons l243063 (.cons l243069 (.cons l243070 (.cons l243071 (.cons l243074 (.cons l243075 (.cons l243079 (.cons l243082 (.cons l243083 (.cons l243087 (.cons l243090 (.cons l243091 (.cons l243093 (.cons l243095 (.cons l243098 (.cons l243099 (.cons l243101 (.nil))))))))))))))))))))))))))))))))))))))))))

end S79

end RACert.S0N3.C0
