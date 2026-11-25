/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C7.Defs
public import Solution.Atoms7.S6N0.C7.S0

/-! Generated certificate (see `certgen`): symmetry class 7 of type (6, 0). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C7

open RACert RACert.Problem

theorem total : OrbitSeg 6 perms (P.leaf (19 + 3)) 0 64 64 4202168 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 6 0 [0, 2, 1, 4, 3, 6, 5] = 4202168 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S6N0.C7
