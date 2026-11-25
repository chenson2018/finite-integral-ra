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

namespace S119

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516515, 24), (516516, 24), (516517, 24), (516518, 24), (516519, 24), (516520, 24), (516521, 24), (516522, 24), (516523, 24), (516524, 24), (516525, 24), (516526, 24), (516527, 24), (516531, 24), (516532, 24), (516533, 24), (516534, 24), (516535, 24), (516536, 24), (516537, 24), (516538, 24), (516539, 24), (516540, 24), (516541, 24), (516542, 24), (516543, 24), (516545, 24), (516547, 24), (516549, 24), (516551, 24), (516553, 24), (516555, 24), (516557, 24), (516559, 24), (516561, 24), (516562, 24), (516563, 24), (516565, 24), (516566, 24), (516567, 24), (516569, 24), (516570, 24), (516571, 24), (516572, 12), (516573, 24), (516574, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516515, 23), (516516, 15), (516517, 13), (516518, 73), (516519, 87), (516522, 136), (516523, 146), (516526, 280), (516527, 280), (516531, 110), (516532, 47), (516533, 140), (516534, 422), (516535, 431), (516536, 42), (516537, 115), (516538, 364), (516539, 391), (516540, 254), (516541, 278), (516542, 768), (516543, 856), (516545, 18), (516547, 45), (516549, 49), (516551, 117), (516555, 53), (516559, 118), (516561, 169), (516562, 134), (516563, 867), (516565, 658), (516566, 1314), (516567, 2427), (516569, 250), (516570, 502), (516571, 1113), (516572, 543), (516573, 909), (516574, 1773)]

theorem leavesOK : P.checkLeaves 18 live = true := by decide +kernel

theorem segOK : checkSeg 20 perms 516515 516575 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 385404 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516515 516575 1092 385404 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (checkLeaves_spec rows leavesOK))

end S119

end RACert.S0N3.C0
