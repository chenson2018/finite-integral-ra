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

namespace S70

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(238967, 24), (238969, 24), (238970, 24), (238971, 24), (238973, 24), (238974, 24), (238975, 24), (238979, 24), (238983, 24), (238987, 24), (238991, 24), (238994, 24), (238995, 24), (238997, 12), (238998, 24), (238999, 24), (239002, 24), (239003, 24), (239005, 24), (239006, 24), (239007, 24), (239009, 24), (239011, 24), (239013, 24), (239014, 12), (239015, 24), (239017, 24), (239019, 24), (239021, 24), (239022, 24), (239023, 24), (239025, 24), (239026, 24), (239027, 24), (239029, 24), (239030, 24), (239031, 24), (239033, 24), (239034, 24), (239035, 24), (239037, 24), (239038, 24), (239039, 24), (239043, 24), (239047, 24), (239051, 24), (239055, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 419, 426, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 424, 0, 0, 0, 0, 424, 0, 0, 0, 0, 0, 0, 418, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(238967, 306), (238973, 56), (238974, 56), (238975, 400), (238979, 10), (238983, 50), (238987, 20), (238991, 50), (238994, 0), (238995, 46), (238997, 116), (238999, 320), (239002, 16), (239003, 112), (239005, 152), (239007, 536), (239009, 9), (239011, 52), (239013, 35), (239014, 92), (239015, 310), (239019, 128), (239022, 172), (239023, 616), (239025, 78), (239026, 42), (239027, 132), (239029, 286), (239030, 265), (239031, 909), (239033, 120), (239034, 132), (239035, 315), (239037, 360), (239038, 372), (239039, 1224), (239043, 12), (239047, 60), (239051, 24), (239055, 60)]

theorem l238967 : P.leaf 18 238967 = 306 := by decide +kernel

theorem l238973 : P.leaf 18 238973 = 56 := by decide +kernel

theorem l238974 : P.leaf 18 238974 = 56 := by decide +kernel

theorem l238975 : P.leaf 18 238975 = 400 := by decide +kernel

theorem l238979 : P.leaf 18 238979 = 10 := by decide +kernel

theorem l238983 : P.leaf 18 238983 = 50 := by decide +kernel

theorem l238987 : P.leaf 18 238987 = 20 := by decide +kernel

theorem l238991 : P.leaf 18 238991 = 50 := by decide +kernel

theorem l238994 : P.leaf 18 238994 = 0 := by decide +kernel

theorem l238995 : P.leaf 18 238995 = 46 := by decide +kernel

theorem l238997 : P.leaf 18 238997 = 116 := by decide +kernel

theorem l238999 : P.leaf 18 238999 = 320 := by decide +kernel

theorem l239002 : P.leaf 18 239002 = 16 := by decide +kernel

theorem l239003 : P.leaf 18 239003 = 112 := by decide +kernel

theorem l239005 : P.leaf 18 239005 = 152 := by decide +kernel

theorem l239007 : P.leaf 18 239007 = 536 := by decide +kernel

theorem l239009 : P.leaf 18 239009 = 9 := by decide +kernel

theorem l239011 : P.leaf 18 239011 = 52 := by decide +kernel

theorem l239013 : P.leaf 18 239013 = 35 := by decide +kernel

theorem l239014 : P.leaf 18 239014 = 92 := by decide +kernel

theorem l239015 : P.leaf 18 239015 = 310 := by decide +kernel

theorem l239019 : P.leaf 18 239019 = 128 := by decide +kernel

theorem l239022 : P.leaf 18 239022 = 172 := by decide +kernel

theorem l239023 : P.leaf 18 239023 = 616 := by decide +kernel

theorem l239025 : P.leaf 18 239025 = 78 := by decide +kernel

theorem l239026 : P.leaf 18 239026 = 42 := by decide +kernel

theorem l239027 : P.leaf 18 239027 = 132 := by decide +kernel

theorem l239029 : P.leaf 18 239029 = 286 := by decide +kernel

theorem l239030 : P.leaf 18 239030 = 265 := by decide +kernel

theorem l239031 : P.leaf 18 239031 = 909 := by decide +kernel

theorem l239033 : P.leaf 18 239033 = 120 := by decide +kernel

theorem l239034 : P.leaf 18 239034 = 132 := by decide +kernel

theorem l239035 : P.leaf 18 239035 = 315 := by decide +kernel

theorem l239037 : P.leaf 18 239037 = 360 := by decide +kernel

theorem l239038 : P.leaf 18 239038 = 372 := by decide +kernel

theorem l239039 : P.leaf 18 239039 = 1224 := by decide +kernel

theorem l239043 : P.leaf 18 239043 = 12 := by decide +kernel

theorem l239047 : P.leaf 18 239047 = 60 := by decide +kernel

theorem l239051 : P.leaf 18 239051 = 24 := by decide +kernel

theorem l239055 : P.leaf 18 239055 = 60 := by decide +kernel

theorem segOK : checkSeg 20 perms 238967 239058 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 190728 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 238967 239058 1104 190728 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l238967 (.cons l238973 (.cons l238974 (.cons l238975 (.cons l238979 (.cons l238983 (.cons l238987 (.cons l238991 (.cons l238994 (.cons l238995 (.cons l238997 (.cons l238999 (.cons l239002 (.cons l239003 (.cons l239005 (.cons l239007 (.cons l239009 (.cons l239011 (.cons l239013 (.cons l239014 (.cons l239015 (.cons l239019 (.cons l239022 (.cons l239023 (.cons l239025 (.cons l239026 (.cons l239027 (.cons l239029 (.cons l239030 (.cons l239031 (.cons l239033 (.cons l239034 (.cons l239035 (.cons l239037 (.cons l239038 (.cons l239039 (.cons l239043 (.cons l239047 (.cons l239051 (.cons l239055 (.nil))))))))))))))))))))))))))))))))))))))))))

end S70

end RACert.S0N3.C0
