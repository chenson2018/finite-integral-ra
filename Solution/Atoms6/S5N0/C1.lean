/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C1.Defs
public import Solution.Atoms6.S5N0.C1.S0

/-! Generated certificate (see `certgen`): symmetry class 1 of type (5, 0). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C1

open RACert RACert.Problem

theorem total : OrbitSeg 4 perms (P.leaf 20) 0 16 16 652971 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 5 0 [0, 1, 2, 3, 5, 4] = 652971 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S5N0.C1
