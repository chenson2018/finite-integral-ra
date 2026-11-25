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

namespace S27

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(99207, 24), (99211, 24), (99215, 24), (99221, 24), (99222, 24), (99223, 24), (99225, 24), (99226, 24), (99227, 24), (99229, 24), (99230, 24), (99231, 24), (99237, 24), (99238, 24), (99239, 24), (99241, 24), (99242, 24), (99243, 24), (99245, 24), (99246, 24), (99247, 24), (99252, 12), (99253, 24), (99254, 24), (99255, 24), (99257, 24), (99258, 24), (99259, 24), (99260, 24), (99261, 24), (99262, 24), (99263, 24), (99267, 8), (99271, 24), (99275, 24), (99279, 24), (99285, 24), (99286, 24), (99287, 24), (99289, 24), (99290, 24), (99291, 24), (99293, 24), (99294, 24), (99295, 24), (99301, 24), (99302, 24), (99303, 24), (99305, 24), (99306, 24), (99307, 24), (99309, 24), (99310, 24), (99311, 24), (99317, 24), (99318, 24), (99319, 24), (99321, 24), (99322, 24), (99323, 24), (99324, 12), (99325, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 532, 424, 0, 419, 424, 0, 532, 424, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 420, 532, 0, 0, 419, 0, 0, 532, 532, 0, 0, 0, 0, 0, 0, 0, 424, 0, 419, 424, 0, 0, 424, 0, 418, 0, 0, 418, 0, 0, 418, 0, 0, 0, 0, 0, 419, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(99207, 4), (99211, 12), (99215, 16), (99223, 8), (99227, 24), (99231, 32), (99238, 4), (99239, 8), (99242, 20), (99243, 24), (99246, 24), (99247, 32), (99254, 20), (99255, 32), (99258, 20), (99259, 60), (99262, 32), (99263, 80), (99267, 8), (99271, 14), (99275, 14), (99279, 40), (99285, 18), (99287, 76), (99291, 28), (99293, 24), (99295, 80), (99302, 24), (99303, 28), (99306, 24), (99307, 28), (99310, 72), (99311, 80), (99317, 28), (99318, 100), (99319, 166), (99322, 28), (99323, 70), (99324, 16), (99325, 32)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 99207 99326 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 34480 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 99207 99326 1448 34480 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S27

end RACert.S0N3.C0
