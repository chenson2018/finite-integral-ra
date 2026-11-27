/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs
public import Solution.Atoms7.S6N0.C0.G0x0
public import Solution.Atoms7.S6N0.C0.G0x1
public import Solution.Atoms7.S6N0.C0.G0x2

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0

open RACert RACert.Problem

theorem total : OrbitSeg 20 perms (P.leaf 36) 0 1048576 1048576 210329506874380 :=
  OrbitSeg.cast ((G0x0.total).append ((G0x1.total).append (G0x2.total)))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 6 0 [0, 1, 2, 3, 4, 5, 6] = 210329506874380 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S6N0.C0
