/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C2.Defs
public import Solution.Atoms7.S0N3.C2.S0
public import Solution.Atoms7.S0N3.C2.S1
public import Solution.Atoms7.S0N3.C2.S2
public import Solution.Atoms7.S0N3.C2.S3

/-! Generated certificate (see `certgen`): symmetry class 2 of type (0, 3). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C2

open RACert RACert.Problem

theorem total : OrbitSeg 10 perms (P.leaf 16) 0 1024 1024 1083289 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append ((S2.total).append (S3.total))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 3 [0, 1, 2, 4, 3, 6, 5] = 1083289 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S0N3.C2
