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

namespace S122

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516939, 24), (516943, 24), (516949, 24), (516950, 24), (516951, 24), (516953, 24), (516954, 24), (516955, 24), (516957, 24), (516958, 24), (516959, 24), (516965, 24), (516966, 24), (516967, 24), (516969, 24), (516970, 24), (516971, 24), (516973, 24), (516974, 24), (516975, 24), (516980, 24), (516981, 24), (516982, 24), (516983, 24), (516984, 12), (516985, 24), (516986, 24), (516987, 24), (516988, 24), (516989, 24), (516990, 24), (516991, 24), (516999, 24), (517003, 24), (517007, 24), (517013, 24), (517014, 24), (517015, 24), (517017, 24), (517018, 24), (517019, 24), (517021, 24), (517022, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516939, 98), (516943, 460), (516949, 229), (516950, 413), (516951, 659), (516953, 0), (516954, 220), (516955, 428), (516957, 243), (516958, 688), (516959, 1147), (516966, 314), (516967, 344), (516970, 78), (516971, 122), (516974, 617), (516975, 713), (516980, 44), (516981, 242), (516982, 630), (516983, 740), (516984, 0), (516985, 0), (516986, 454), (516987, 633), (516988, 204), (516989, 256), (516990, 1129), (516991, 1301), (516999, 195), (517003, 232), (517007, 488), (517013, 172), (517014, 384), (517015, 460), (517017, 136), (517018, 368), (517019, 400), (517021, 312), (517022, 728)]

theorem l516939 : P.leaf 18 516939 = 98 := by decide +kernel

theorem l516943 : P.leaf 18 516943 = 460 := by decide +kernel

theorem l516949 : P.leaf 18 516949 = 229 := by decide +kernel

theorem l516950 : P.leaf 18 516950 = 413 := by decide +kernel

theorem l516951 : P.leaf 18 516951 = 659 := by decide +kernel

theorem l516953 : P.leaf 18 516953 = 0 := by decide +kernel

theorem l516954 : P.leaf 18 516954 = 220 := by decide +kernel

theorem l516955 : P.leaf 18 516955 = 428 := by decide +kernel

theorem l516957 : P.leaf 18 516957 = 243 := by decide +kernel

theorem l516958 : P.leaf 18 516958 = 688 := by decide +kernel

theorem l516959 : P.leaf 18 516959 = 1147 := by decide +kernel

theorem l516966 : P.leaf 18 516966 = 314 := by decide +kernel

theorem l516967 : P.leaf 18 516967 = 344 := by decide +kernel

theorem l516970 : P.leaf 18 516970 = 78 := by decide +kernel

theorem l516971 : P.leaf 18 516971 = 122 := by decide +kernel

theorem l516974 : P.leaf 18 516974 = 617 := by decide +kernel

theorem l516975 : P.leaf 18 516975 = 713 := by decide +kernel

theorem l516980 : P.leaf 18 516980 = 44 := by decide +kernel

theorem l516981 : P.leaf 18 516981 = 242 := by decide +kernel

theorem l516982 : P.leaf 18 516982 = 630 := by decide +kernel

theorem l516983 : P.leaf 18 516983 = 740 := by decide +kernel

theorem l516984 : P.leaf 18 516984 = 0 := by decide +kernel

theorem l516985 : P.leaf 18 516985 = 0 := by decide +kernel

theorem l516986 : P.leaf 18 516986 = 454 := by decide +kernel

theorem l516987 : P.leaf 18 516987 = 633 := by decide +kernel

theorem l516988 : P.leaf 18 516988 = 204 := by decide +kernel

theorem l516989 : P.leaf 18 516989 = 256 := by decide +kernel

theorem l516990 : P.leaf 18 516990 = 1129 := by decide +kernel

theorem l516991 : P.leaf 18 516991 = 1301 := by decide +kernel

theorem l516999 : P.leaf 18 516999 = 195 := by decide +kernel

theorem l517003 : P.leaf 18 517003 = 232 := by decide +kernel

theorem l517007 : P.leaf 18 517007 = 488 := by decide +kernel

theorem l517013 : P.leaf 18 517013 = 172 := by decide +kernel

theorem l517014 : P.leaf 18 517014 = 384 := by decide +kernel

theorem l517015 : P.leaf 18 517015 = 460 := by decide +kernel

theorem l517017 : P.leaf 18 517017 = 136 := by decide +kernel

theorem l517018 : P.leaf 18 517018 = 368 := by decide +kernel

theorem l517019 : P.leaf 18 517019 = 400 := by decide +kernel

theorem l517021 : P.leaf 18 517021 = 312 := by decide +kernel

theorem l517022 : P.leaf 18 517022 = 728 := by decide +kernel

theorem segOK : checkSeg 20 perms 516939 517023 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 390744 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516939 517023 1020 390744 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l516939 (.cons l516943 (.cons l516949 (.cons l516950 (.cons l516951 (.cons l516953 (.cons l516954 (.cons l516955 (.cons l516957 (.cons l516958 (.cons l516959 (.cons l516966 (.cons l516967 (.cons l516970 (.cons l516971 (.cons l516974 (.cons l516975 (.cons l516980 (.cons l516981 (.cons l516982 (.cons l516983 (.cons l516984 (.cons l516985 (.cons l516986 (.cons l516987 (.cons l516988 (.cons l516989 (.cons l516990 (.cons l516991 (.cons l516999 (.cons l517003 (.cons l517007 (.cons l517013 (.cons l517014 (.cons l517015 (.cons l517017 (.cons l517018 (.cons l517019 (.cons l517021 (.cons l517022 (.nil))))))))))))))))))))))))))))))))))))))))))

end S122

end RACert.S0N3.C0
