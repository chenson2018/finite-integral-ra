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

namespace S101

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(438905, 48), (438906, 48), (438907, 48), (438908, 48), (438909, 48), (438910, 48), (438911, 48), (438919, 48), (438923, 48), (438927, 48), (438932, 24), (438933, 48), (438934, 48), (438935, 48), (438937, 48), (438938, 48), (438939, 48), (438940, 48), (438941, 48), (438942, 48), (438943, 48), (438949, 48), (438950, 48), (438951, 48), (438953, 48), (438954, 48), (438955, 48), (438957, 48), (438958, 48), (438959, 48), (438964, 48), (438965, 48), (438966, 48), (438967, 48), (438968, 48), (438969, 48), (438970, 48), (438971, 48), (438972, 48), (438973, 48), (438974, 48), (438975, 48), (438979, 48), (438983, 48), (438987, 48), (438991, 48), (438993, 48), (438994, 48), (438995, 48), (438997, 48), (438998, 48), (438999, 48), (439001, 48), (439002, 48), (439003, 48), (439004, 24), (439005, 48), (439006, 48), (439007, 48), (439009, 48), (439010, 48), (439011, 48), (439013, 48), (439014, 48), (439015, 48), (439017, 48), (439018, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 684, 684, 0, 0, 0, 0, 602, 0, 0, 602, 602, 602, 602, 0, 620, 0, 620, 0, 620, 0, 502, 602, 602, 502, 0, 0, 502, 0, 0, 602, 602, 602, 602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 620, 0, 0, 620, 0, 0, 620, 0, 620, 0, 620, 0, 502, 0, 0, 502, 0, 0, 502, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(438905, 0), (438908, 142), (438909, 284), (438910, 142), (438911, 426), (438923, 6), (438927, 18), (438937, 8), (438939, 42), (438941, 54), (438943, 108), (438954, 18), (438955, 84), (438958, 56), (438959, 205), (438968, 8), (438969, 50), (438970, 61), (438971, 200), (438972, 156), (438973, 346), (438974, 160), (438975, 506), (438979, 9), (438983, 24), (438987, 10), (438991, 46), (438993, 11), (438995, 139), (438997, 131), (438999, 340), (439001, 50), (439003, 222), (439005, 325), (439007, 749), (439010, 10), (439011, 202), (439014, 56), (439015, 557), (439018, 55)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 438905 439019 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 288768 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 438905 439019 3168 288768 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S101

end RACert.S0N3.C0
