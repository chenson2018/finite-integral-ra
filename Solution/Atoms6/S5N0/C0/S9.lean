/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S9

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(7594, 120), (7595, 120), (7596, 120), (7597, 120), (7598, 120), (7599, 120), (7608, 60), (7609, 60), (7610, 120), (7611, 120), (7614, 60), (7615, 60), (7648, 60), (7649, 120), (7651, 60), (7652, 120), (7653, 120), (7654, 120), (7655, 120), (7660, 60), (7661, 120), (7663, 60), (7664, 60), (7665, 120), (7667, 60), (7668, 120), (7669, 120), (7670, 120), (7671, 120), (7676, 60), (7677, 120), (7679, 60), (8128, 30), (8129, 30), (8130, 60), (8131, 60), (8134, 30), (8135, 30), (8136, 60), (8137, 60)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(7594, 5898), (7595, 7578), (7596, 5919), (7597, 7591), (7598, 8970), (7599, 11498), (7608, 4107), (7609, 5252), (7610, 6138), (7611, 7875), (7614, 9319), (7615, 11937), (7648, 12472), (7649, 19438), (7651, 30988), (7652, 15866), (7653, 24613), (7654, 25542), (7655, 40306), (7660, 20772), (7661, 33196), (7663, 53364), (7664, 12720), (7665, 19942), (7667, 31922), (7668, 16160), (7669, 25251), (7670, 26088), (7671, 41299), (7676, 21120), (7677, 33874), (7679, 54416), (8128, 25688), (8129, 45506), (8130, 31344), (8131, 54662), (8134, 38737), (8135, 66373), (8136, 30952), (8137, 55967)]

theorem leavesOK : P.checkLeavesR 20 qm live = true := by decide +kernel

theorem segOK : checkSeg 15 perms 7594 8138 seg = true := by decide +kernel

theorem evOK : P.checkEv 20 seg ev live 0 77733000 = true := by decide +kernel

theorem total : OrbitSeg 15 perms (P.leaf 20) 7594 8138 3480 77733000 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeavesR_spec rows qmOK leavesOK))

end S9

end RACert.S5N0.C0
