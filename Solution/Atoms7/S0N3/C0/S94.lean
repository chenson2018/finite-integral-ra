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

namespace S94

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(259959, 48), (259961, 24), (259962, 24), (259963, 48), (259965, 48), (259966, 48), (259967, 48), (259971, 48), (259975, 48), (259979, 48), (259983, 48), (259987, 48), (259991, 48), (259995, 48), (259999, 48), (260003, 48), (260007, 48), (260011, 48), (260015, 48), (260019, 48), (260021, 24), (260022, 24), (260023, 48), (260027, 48), (260029, 48), (260030, 48), (260031, 48), (260035, 48), (260039, 48), (260043, 48), (260047, 48), (260051, 48), (260055, 48), (260059, 48), (260063, 48), (260067, 48), (260071, 48), (260075, 48), (260079, 48), (260083, 48), (260087, 48), (260091, 48), (260093, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 439, 438, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(259959, 2782), (259965, 1580), (259966, 1380), (259967, 3916), (259971, 168), (259975, 1420), (259979, 1098), (259983, 2508), (259987, 272), (259991, 2248), (259995, 1600), (259999, 4243), (260003, 292), (260007, 2348), (260011, 1656), (260015, 4230), (260019, 428), (260021, 2264), (260022, 1712), (260023, 4150), (260027, 2228), (260029, 2916), (260030, 2548), (260031, 6534), (260035, 400), (260039, 2584), (260043, 1278), (260047, 3400), (260051, 616), (260055, 3730), (260059, 2012), (260063, 6158), (260067, 632), (260071, 3792), (260075, 2074), (260079, 6158), (260083, 856), (260087, 5182), (260091, 2858), (260093, 3752)]

theorem l259959 : P.leaf 18 259959 = 2782 := by decide +kernel

theorem l259965 : P.leaf 18 259965 = 1580 := by decide +kernel

theorem l259966 : P.leaf 18 259966 = 1380 := by decide +kernel

theorem l259967 : P.leaf 18 259967 = 3916 := by decide +kernel

theorem l259971 : P.leaf 18 259971 = 168 := by decide +kernel

theorem l259975 : P.leaf 18 259975 = 1420 := by decide +kernel

theorem l259979 : P.leaf 18 259979 = 1098 := by decide +kernel

theorem l259983 : P.leaf 18 259983 = 2508 := by decide +kernel

theorem l259987 : P.leaf 18 259987 = 272 := by decide +kernel

theorem l259991 : P.leaf 18 259991 = 2248 := by decide +kernel

theorem l259995 : P.leaf 18 259995 = 1600 := by decide +kernel

theorem l259999 : P.leaf 18 259999 = 4243 := by decide +kernel

theorem l260003 : P.leaf 18 260003 = 292 := by decide +kernel

theorem l260007 : P.leaf 18 260007 = 2348 := by decide +kernel

theorem l260011 : P.leaf 18 260011 = 1656 := by decide +kernel

theorem l260015 : P.leaf 18 260015 = 4230 := by decide +kernel

theorem l260019 : P.leaf 18 260019 = 428 := by decide +kernel

theorem l260021 : P.leaf 18 260021 = 2264 := by decide +kernel

theorem l260022 : P.leaf 18 260022 = 1712 := by decide +kernel

theorem l260023 : P.leaf 18 260023 = 4150 := by decide +kernel

theorem l260027 : P.leaf 18 260027 = 2228 := by decide +kernel

theorem l260029 : P.leaf 18 260029 = 2916 := by decide +kernel

theorem l260030 : P.leaf 18 260030 = 2548 := by decide +kernel

theorem l260031 : P.leaf 18 260031 = 6534 := by decide +kernel

theorem l260035 : P.leaf 18 260035 = 400 := by decide +kernel

theorem l260039 : P.leaf 18 260039 = 2584 := by decide +kernel

theorem l260043 : P.leaf 18 260043 = 1278 := by decide +kernel

theorem l260047 : P.leaf 18 260047 = 3400 := by decide +kernel

theorem l260051 : P.leaf 18 260051 = 616 := by decide +kernel

theorem l260055 : P.leaf 18 260055 = 3730 := by decide +kernel

theorem l260059 : P.leaf 18 260059 = 2012 := by decide +kernel

theorem l260063 : P.leaf 18 260063 = 6158 := by decide +kernel

theorem l260067 : P.leaf 18 260067 = 632 := by decide +kernel

theorem l260071 : P.leaf 18 260071 = 3792 := by decide +kernel

theorem l260075 : P.leaf 18 260075 = 2074 := by decide +kernel

theorem l260079 : P.leaf 18 260079 = 6158 := by decide +kernel

theorem l260083 : P.leaf 18 260083 = 856 := by decide +kernel

theorem l260087 : P.leaf 18 260087 = 5182 := by decide +kernel

theorem l260091 : P.leaf 18 260091 = 2858 := by decide +kernel

theorem l260093 : P.leaf 18 260093 = 3752 := by decide +kernel

theorem segOK : checkSeg 20 perms 259959 260094 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4614672 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 259959 260094 1944 4614672 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l259959 (.cons l259965 (.cons l259966 (.cons l259967 (.cons l259971 (.cons l259975 (.cons l259979 (.cons l259983 (.cons l259987 (.cons l259991 (.cons l259995 (.cons l259999 (.cons l260003 (.cons l260007 (.cons l260011 (.cons l260015 (.cons l260019 (.cons l260021 (.cons l260022 (.cons l260023 (.cons l260027 (.cons l260029 (.cons l260030 (.cons l260031 (.cons l260035 (.cons l260039 (.cons l260043 (.cons l260047 (.cons l260051 (.cons l260055 (.cons l260059 (.cons l260063 (.cons l260067 (.cons l260071 (.cons l260075 (.cons l260079 (.cons l260083 (.cons l260087 (.cons l260091 (.cons l260093 (.nil))))))))))))))))))))))))))))))))))))))))))

end S94

end RACert.S0N3.C0
