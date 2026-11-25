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

namespace S88

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(244903, 48), (244907, 48), (244911, 48), (244915, 48), (244919, 48), (244923, 48), (244927, 48), (244943, 24), (244947, 48), (244951, 48), (244955, 48), (244959, 48), (244963, 48), (244967, 48), (244971, 48), (244975, 48), (244979, 48), (244983, 48), (244987, 48), (244991, 48), (245011, 24), (245015, 48), (245019, 48), (245023, 48), (245027, 48), (245031, 48), (245035, 48), (245039, 48), (245043, 48), (245047, 48), (245051, 48), (245055, 48), (245079, 48), (245083, 24), (245087, 48), (245091, 48), (245095, 48), (245099, 48), (245103, 48), (245107, 48), (245111, 48), (245115, 48), (245119, 48), (245143, 24), (245151, 48), (245155, 48), (245159, 48), (245163, 48), (245167, 48), (245171, 48), (245175, 48), (245179, 48), (245183, 48), (245215, 24), (245219, 48), (245223, 48), (245227, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 663, 0, 0, 0, 0, 0, 663, 669, 0, 669, 0, 663, 0, 663, 0, 0, 0, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 0, 440, 0, 440, 0, 440, 0, 440, 0, 440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(244903, 176), (244911, 240), (244915, 279), (244919, 1507), (244923, 699), (244927, 3233), (244951, 398), (244959, 520), (244967, 192), (244975, 240), (244979, 372), (244983, 2506), (244987, 926), (244991, 4232), (245015, 101), (245023, 184), (245031, 141), (245039, 266), (245047, 244), (245055, 396), (245079, 457), (245087, 620), (245095, 701), (245103, 894), (245111, 1286), (245119, 1524), (245143, 672), (245151, 1535), (245155, 192), (245159, 1087), (245163, 757), (245167, 2348), (245171, 330), (245175, 1985), (245179, 1242), (245183, 4094), (245215, 2396), (245219, 300), (245223, 2351), (245227, 968)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 244903 245231 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1970736 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 244903 245231 2616 1970736 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S88

end RACert.S0N3.C0
