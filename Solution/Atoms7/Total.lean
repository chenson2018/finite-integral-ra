/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.Symm0Nsymm3
public import Solution.Atoms7.Symm2Nsymm2
public import Solution.Atoms7.Symm4Nsymm1
public import Solution.Atoms7.Symm6Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofAtoms_seven : (ofAtoms 7).encard = 344809166311 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_zero_three) + $(encard_ofSymmNsymm_two_two) +
      $(encard_ofSymmNsymm_four_one) + $(encard_ofSymmNsymm_six_zero))

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
