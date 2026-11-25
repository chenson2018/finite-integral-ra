/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms1.Symm0Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofAtoms_one : (ofAtoms 1).encard = 1 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm] using encard_ofSymmNsymm_zero_zero

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
