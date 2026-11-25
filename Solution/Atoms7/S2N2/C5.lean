/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C5.Defs
public import Solution.Atoms7.S2N2.C5.S0

/-! Generated certificate (see `certgen`): symmetry class 5 of type (2, 2). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C5

open RACert RACert.Problem

theorem total : OrbitSeg 8 perms (P.leaf 20) 0 256 256 1296088 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 2 [0, 2, 1, 3, 4, 5, 6] = 1296088 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S2N2.C5
