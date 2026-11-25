/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms5.Symm0Nsymm2
public import Solution.Atoms5.Symm2Nsymm1
public import Solution.Atoms5.Symm4Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofAtoms_five : (ofAtoms 5).encard = 4412 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_zero_two) + $(encard_ofSymmNsymm_two_one) +
      $(encard_ofSymmNsymm_four_zero))

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
