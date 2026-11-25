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

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_five : Nat.card (ofAtoms 5) = 4412 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_four_zero) + $(card_ofSymmNsymm_two_one) +
      $(card_ofSymmNsymm_zero_two))

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
