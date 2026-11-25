/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms4.Symm1Nsymm1
public import Solution.Atoms4.Symm3Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_four : Nat.card (ofAtoms 4) = 102 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_three_zero) + $(card_ofSymmNsymm_one_one))

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
