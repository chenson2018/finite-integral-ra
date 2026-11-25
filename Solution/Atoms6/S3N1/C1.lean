/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S3N1.C1.Defs
public import Solution.Atoms6.S3N1.C1.S0

/-! Generated certificate (see `certgen`): symmetry class 1 of type (3, 1). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S3N1.C1

open RACert RACert.Problem

theorem total : OrbitSeg 3 perms (P.leaf 21) 0 8 8 680611 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 3 1 [0, 1, 2, 3, 5, 4] = 680611 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S3N1.C1
