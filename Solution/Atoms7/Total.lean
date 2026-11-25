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

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_seven : Nat.card (ofAtoms 7) = 344809166311 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_six_zero) + $(card_ofSymmNsymm_four_one) +
      $(card_ofSymmNsymm_two_two) + $(card_ofSymmNsymm_zero_three))

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
