/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Group
public import Solution.Atoms6.S1N2.C0
public import Solution.Atoms6.S1N2.C1
public import Solution.Atoms6.S1N2.C2
public import Solution.Atoms6.S1N2.C3
public import Solution.Atoms6.S1N2.C4

/-! Generated certificate (see `certgen`): Burnside count for type (1, 2). -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S1N2

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 5, 4], [0, 1, 3, 2, 5, 4], [0, 1, 4, 5, 2, 3], [0, 1, 4, 5, 3, 2]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4, 5], 0, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 2, 3, 5, 4], 1, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 3, 2, 4, 5], 1, [0, 1, 4, 5, 2, 3]),
   ([0, 1, 3, 2, 5, 4], 2, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 4, 5, 2, 3], 3, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 4, 5, 3, 2], 4, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 5, 4, 2, 3], 4, [0, 1, 2, 3, 5, 4]),
   ([0, 1, 5, 4, 3, 2], 3, [0, 1, 2, 3, 5, 4])]

theorem groupCert : checkGroup 1 2 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (1, 2). -/
theorem count : (Cslib.RelationAlgebra.IntegralAlgebra.IsoClass.ofSymmNsymm 1 2).encard = (47965 : ℕ) :=
  encard_ofSymmNsymm_of_groupCert' 1 2 47965 reps elems [312508, 18438, 32020, 902, 256] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.cons C4.count (.nil))))))
    (by decide +kernel)

end RACert.S1N2
