/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Group
public import Solution.Atoms5.S2N1.C0
public import Solution.Atoms5.S2N1.C1
public import Solution.Atoms5.S2N1.C2
public import Solution.Atoms5.S2N1.C3

/-! Generated certificate (see `certgen`): Burnside count for type (2, 1). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N1

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 2, 1, 3, 4], [0, 2, 1, 4, 3]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4], 0, [0, 1, 2, 3, 4]),
   ([0, 1, 2, 4, 3], 1, [0, 1, 2, 3, 4]),
   ([0, 2, 1, 3, 4], 2, [0, 1, 2, 3, 4]),
   ([0, 2, 1, 4, 3], 3, [0, 1, 2, 3, 4])]

theorem groupCert : checkGroup 2 1 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (2, 1). -/
theorem count : (Cslib.RelationAlgebra.IntegralAlgebra.IsoClass.ofSymmNsymm 2 1).encard = (1316 : ℕ) :=
  encard_ofSymmNsymm_of_groupCert' 2 1 1316 reps elems [3720, 1318, 92, 134] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.nil)))))
    (by decide +kernel)

end RACert.S2N1
