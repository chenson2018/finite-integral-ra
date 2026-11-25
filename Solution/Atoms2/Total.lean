/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms2.Symm1Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofAtoms_two : (ofAtoms 2).encard = 2 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm] using encard_ofSymmNsymm_one_zero

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
