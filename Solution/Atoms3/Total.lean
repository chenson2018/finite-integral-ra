/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms3.Symm0Nsymm1
public import Solution.Atoms3.Symm2Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofAtoms_three : (ofAtoms 3).encard = 10 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_zero_one) + $(encard_ofSymmNsymm_two_zero))

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
