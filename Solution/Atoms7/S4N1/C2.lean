/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C2.Defs
public import Solution.Atoms7.S4N1.C2.S0

/-! Generated certificate (see `certgen`): symmetry class 2 of type (4, 1). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C2

open RACert RACert.Problem

theorem total : OrbitSeg 11 perms (P.leaf (20 + 3)) 0 2048 2048 124588184 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 4 1 [0, 1, 2, 4, 3, 5, 6] = 124588184 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S4N1.C2
