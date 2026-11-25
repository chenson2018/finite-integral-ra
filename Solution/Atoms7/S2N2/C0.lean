/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C0.Defs
public import Solution.Atoms7.S2N2.C0.S0
public import Solution.Atoms7.S2N2.C0.S1
public import Solution.Atoms7.S2N2.C0.S2
public import Solution.Atoms7.S2N2.C0.S3
public import Solution.Atoms7.S2N2.C0.S4
public import Solution.Atoms7.S2N2.C0.S5
public import Solution.Atoms7.S2N2.C0.S6
public import Solution.Atoms7.S2N2.C0.S7
public import Solution.Atoms7.S2N2.C0.S8
public import Solution.Atoms7.S2N2.C0.S9
public import Solution.Atoms7.S2N2.C0.S10
public import Solution.Atoms7.S2N2.C0.S11
public import Solution.Atoms7.S2N2.C0.S12
public import Solution.Atoms7.S2N2.C0.S13
public import Solution.Atoms7.S2N2.C0.S14
public import Solution.Atoms7.S2N2.C0.S15
public import Solution.Atoms7.S2N2.C0.S16
public import Solution.Atoms7.S2N2.C0.S17
public import Solution.Atoms7.S2N2.C0.S18
public import Solution.Atoms7.S2N2.C0.S19
public import Solution.Atoms7.S2N2.C0.S20
public import Solution.Atoms7.S2N2.C0.S21
public import Solution.Atoms7.S2N2.C0.S22
public import Solution.Atoms7.S2N2.C0.S23
public import Solution.Atoms7.S2N2.C0.S24
public import Solution.Atoms7.S2N2.C0.S25
public import Solution.Atoms7.S2N2.C0.S26
public import Solution.Atoms7.S2N2.C0.S27
public import Solution.Atoms7.S2N2.C0.S28
public import Solution.Atoms7.S2N2.C0.S29
public import Solution.Atoms7.S2N2.C0.S30
public import Solution.Atoms7.S2N2.C0.S31
public import Solution.Atoms7.S2N2.C0.S32
public import Solution.Atoms7.S2N2.C0.S33
public import Solution.Atoms7.S2N2.C0.S34
public import Solution.Atoms7.S2N2.C0.S35
public import Solution.Atoms7.S2N2.C0.S36
public import Solution.Atoms7.S2N2.C0.S37
public import Solution.Atoms7.S2N2.C0.S38

/-! Generated certificate (see `certgen`): symmetry class 0 of type (2, 2). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C0

open RACert RACert.Problem

theorem total : OrbitSeg 22 perms (P.leaf (20 + 2)) 0 4194304 4194304 34608025790 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append ((S2.total).append ((S3.total).append ((S4.total).append ((S5.total).append ((S6.total).append ((S7.total).append ((S8.total).append ((S9.total).append ((S10.total).append ((S11.total).append ((S12.total).append ((S13.total).append ((S14.total).append ((S15.total).append ((S16.total).append ((S17.total).append ((S18.total).append ((S19.total).append ((S20.total).append ((S21.total).append ((S22.total).append ((S23.total).append ((S24.total).append ((S25.total).append ((S26.total).append ((S27.total).append ((S28.total).append ((S29.total).append ((S30.total).append ((S31.total).append ((S32.total).append ((S33.total).append ((S34.total).append ((S35.total).append ((S36.total).append ((S37.total).append (S38.total)))))))))))))))))))))))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 2 [0, 1, 2, 3, 4, 5, 6] = 34608025790 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    symsOK grpOK total

end RACert.S2N2.C0
