/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.Symm1Nsymm2
public import Solution.Atoms6.Symm3Nsymm1
public import Solution.Atoms6.Symm5Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofAtoms_six : (ofAtoms 6).encard = 4886349 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_one_two) + $(encard_ofSymmNsymm_three_one) +
      $(encard_ofSymmNsymm_five_zero))

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
