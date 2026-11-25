/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Defs
public import Solution.Atoms7.S4N1.C0.G0x0
public import Solution.Atoms7.S4N1.C0.G0x1
public import Solution.Atoms7.S4N1.C0.G0x2
public import Solution.Atoms7.S4N1.C0.G0x3

/-! Generated certificate (see `certgen`): symmetry class 0 of type (4, 1). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0

open RACert RACert.Problem

theorem total : OrbitSeg 26 perms (P.leaf (20 + 4)) 0 67108864 67108864 2400445740454 :=
  OrbitSeg.cast ((G0x0.total).append ((G0x1.total).append ((G0x2.total).append (G0x3.total))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 4 1 [0, 1, 2, 3, 4, 5, 6] = 2400445740454 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S4N1.C0
