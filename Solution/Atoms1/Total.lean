/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms1.Symm0Nsymm0

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_one : Nat.card (ofAtoms 1) = 1 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm] using card_ofSymmNsymm_zero_zero

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
