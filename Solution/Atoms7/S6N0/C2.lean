/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C2.Defs
public import Solution.Atoms7.S6N0.C2.S0

/-! Generated certificate (see `certgen`): symmetry class 2 of type (6, 0). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C2

open RACert RACert.Problem

theorem total : OrbitSeg 0 perms (P.leaf (22 + 4)) 0 1 1 3216325 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 6 0 [0, 1, 2, 3, 5, 6, 4] = 3216325 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S6N0.C2
