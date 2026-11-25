/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C5.Defs
public import Solution.Atoms7.S0N3.C5.S0
public import Solution.Atoms7.S0N3.C5.S1
public import Solution.Atoms7.S0N3.C5.S2

/-! Generated certificate (see `certgen`): symmetry class 5 of type (0, 3). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

theorem total : OrbitSeg 10 perms (P.leaf 18) 0 1024 1024 4287373 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append (S2.total)))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 3 [0, 2, 1, 4, 3, 6, 5] = 4287373 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S0N3.C5
