/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S5N0.C0.Defs
public import Solution.Atoms6.S5N0.C0.S0
public import Solution.Atoms6.S5N0.C0.S1
public import Solution.Atoms6.S5N0.C0.S2
public import Solution.Atoms6.S5N0.C0.S3
public import Solution.Atoms6.S5N0.C0.S4
public import Solution.Atoms6.S5N0.C0.S5
public import Solution.Atoms6.S5N0.C0.S6
public import Solution.Atoms6.S5N0.C0.S7
public import Solution.Atoms6.S5N0.C0.S8
public import Solution.Atoms6.S5N0.C0.S9
public import Solution.Atoms6.S5N0.C0.S10
public import Solution.Atoms6.S5N0.C0.S11

/-! Generated certificate (see `certgen`): symmetry class 0 of type (5, 0). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

theorem total : OrbitSeg 15 perms (P.leaf 20) 0 32768 32768 454897503 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append ((S2.total).append ((S3.total).append ((S4.total).append ((S5.total).append ((S6.total).append ((S7.total).append ((S8.total).append ((S9.total).append ((S10.total).append (S11.total))))))))))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 5 0 [0, 1, 2, 3, 4, 5] = 454897503 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S5N0.C0
