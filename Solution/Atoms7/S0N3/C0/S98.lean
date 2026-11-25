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

namespace S98

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(430559, 48), (430576, 24), (430577, 48), (430579, 24), (430580, 48), (430581, 48), (430582, 48), (430583, 48), (430588, 24), (430589, 48), (430591, 24), (430863, 12), (430877, 12), (430878, 12), (430879, 24), (430911, 6), (430919, 24), (430923, 24), (430927, 24), (430933, 48), (430934, 48), (430935, 48), (430937, 48), (430938, 48), (430939, 48), (430941, 48), (430942, 48), (430943, 48), (430964, 12), (430965, 48), (430967, 24), (430968, 12), (430969, 48), (430971, 24), (430972, 24), (430973, 48), (430975, 24), (431043, 4), (431047, 24), (431055, 12), (431061, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 426, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(430559, 683), (430576, 19), (430577, 25), (430579, 434), (430580, 52), (430581, 70), (430582, 163), (430583, 641), (430588, 509), (430589, 593), (430591, 2646), (430863, 98), (430877, 69), (430878, 25), (430879, 122), (430911, 196), (430919, 119), (430923, 65), (430927, 184), (430933, 44), (430934, 8), (430935, 148), (430937, 9), (430939, 65), (430941, 184), (430942, 52), (430943, 312), (430964, 20), (430965, 102), (430967, 280), (430968, 12), (430969, 56), (430971, 216), (430972, 316), (430973, 324), (430975, 558), (431043, 918), (431047, 1106), (431055, 1964), (431061, 606)]

theorem l430559 : P.leaf 18 430559 = 683 := by decide +kernel

theorem l430576 : P.leaf 18 430576 = 19 := by decide +kernel

theorem l430577 : P.leaf 18 430577 = 25 := by decide +kernel

theorem l430579 : P.leaf 18 430579 = 434 := by decide +kernel

theorem l430580 : P.leaf 18 430580 = 52 := by decide +kernel

theorem l430581 : P.leaf 18 430581 = 70 := by decide +kernel

theorem l430582 : P.leaf 18 430582 = 163 := by decide +kernel

theorem l430583 : P.leaf 18 430583 = 641 := by decide +kernel

theorem l430588 : P.leaf 18 430588 = 509 := by decide +kernel

theorem l430589 : P.leaf 18 430589 = 593 := by decide +kernel

theorem l430591 : P.leaf 18 430591 = 2646 := by decide +kernel

theorem l430863 : P.leaf 18 430863 = 98 := by decide +kernel

theorem l430877 : P.leaf 18 430877 = 69 := by decide +kernel

theorem l430878 : P.leaf 18 430878 = 25 := by decide +kernel

theorem l430879 : P.leaf 18 430879 = 122 := by decide +kernel

theorem l430911 : P.leaf 18 430911 = 196 := by decide +kernel

theorem l430919 : P.leaf 18 430919 = 119 := by decide +kernel

theorem l430923 : P.leaf 18 430923 = 65 := by decide +kernel

theorem l430927 : P.leaf 18 430927 = 184 := by decide +kernel

theorem l430933 : P.leaf 18 430933 = 44 := by decide +kernel

theorem l430934 : P.leaf 18 430934 = 8 := by decide +kernel

theorem l430935 : P.leaf 18 430935 = 148 := by decide +kernel

theorem l430937 : P.leaf 18 430937 = 9 := by decide +kernel

theorem l430939 : P.leaf 18 430939 = 65 := by decide +kernel

theorem l430941 : P.leaf 18 430941 = 184 := by decide +kernel

theorem l430942 : P.leaf 18 430942 = 52 := by decide +kernel

theorem l430943 : P.leaf 18 430943 = 312 := by decide +kernel

theorem l430964 : P.leaf 18 430964 = 20 := by decide +kernel

theorem l430965 : P.leaf 18 430965 = 102 := by decide +kernel

theorem l430967 : P.leaf 18 430967 = 280 := by decide +kernel

theorem l430968 : P.leaf 18 430968 = 12 := by decide +kernel

theorem l430969 : P.leaf 18 430969 = 56 := by decide +kernel

theorem l430971 : P.leaf 18 430971 = 216 := by decide +kernel

theorem l430972 : P.leaf 18 430972 = 316 := by decide +kernel

theorem l430973 : P.leaf 18 430973 = 324 := by decide +kernel

theorem l430975 : P.leaf 18 430975 = 558 := by decide +kernel

theorem l431043 : P.leaf 18 431043 = 918 := by decide +kernel

theorem l431047 : P.leaf 18 431047 = 1106 := by decide +kernel

theorem l431055 : P.leaf 18 431055 = 1964 := by decide +kernel

theorem l431061 : P.leaf 18 431061 = 606 := by decide +kernel

theorem segOK : checkSeg 20 perms 430559 431062 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 387456 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 430559 431062 1354 387456 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l430559 (.cons l430576 (.cons l430577 (.cons l430579 (.cons l430580 (.cons l430581 (.cons l430582 (.cons l430583 (.cons l430588 (.cons l430589 (.cons l430591 (.cons l430863 (.cons l430877 (.cons l430878 (.cons l430879 (.cons l430911 (.cons l430919 (.cons l430923 (.cons l430927 (.cons l430933 (.cons l430934 (.cons l430935 (.cons l430937 (.cons l430939 (.cons l430941 (.cons l430942 (.cons l430943 (.cons l430964 (.cons l430965 (.cons l430967 (.cons l430968 (.cons l430969 (.cons l430971 (.cons l430972 (.cons l430973 (.cons l430975 (.cons l431043 (.cons l431047 (.cons l431055 (.cons l431061 (.nil))))))))))))))))))))))))))))))))))))))))))

end S98

end RACert.S0N3.C0
