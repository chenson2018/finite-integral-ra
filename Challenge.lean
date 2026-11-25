/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_zero_zero : Nat.card (ofSymmNsymm 0 0) = 1 := by
  sorry

theorem card_ofAtoms_one : Nat.card (ofAtoms 1) = 1 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm] using card_ofSymmNsymm_zero_zero

theorem card_ofSymmNsymm_one_zero : Nat.card (ofSymmNsymm 1 0) = 2 := by
  sorry

theorem card_ofAtoms_two : Nat.card (ofAtoms 2) = 2 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm] using card_ofSymmNsymm_one_zero

theorem card_ofSymmNsymm_zero_one : Nat.card (ofSymmNsymm 0 1) = 3 := by
  sorry

theorem card_ofSymmNsymm_two_zero : Nat.card (ofSymmNsymm 2 0) = 7 := by
  sorry

theorem card_ofAtoms_three : Nat.card (ofAtoms 3) = 10 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_two_zero) + $(card_ofSymmNsymm_zero_one))

theorem card_ofSymmNsymm_one_one : Nat.card (ofSymmNsymm 1 1) = 37 := by
  sorry

theorem card_ofSymmNsymm_three_zero : Nat.card (ofSymmNsymm 3 0) = 65 := by
  sorry

theorem card_ofAtoms_four : Nat.card (ofAtoms 4) = 102 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_three_zero) + $(card_ofSymmNsymm_one_one))

theorem card_ofSymmNsymm_zero_two : Nat.card (ofSymmNsymm 0 2) = 83 := by
  sorry

theorem card_ofSymmNsymm_two_one : Nat.card (ofSymmNsymm 2 1) = 1316 := by
  sorry

theorem card_ofSymmNsymm_four_zero : Nat.card (ofSymmNsymm 4 0) = 3013 := by
  sorry

theorem card_ofAtoms_five : Nat.card (ofAtoms 5) = 4412 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_four_zero) + $(card_ofSymmNsymm_two_one) +
      $(card_ofSymmNsymm_zero_two))

theorem card_ofSymmNsymm_one_two : Nat.card (ofSymmNsymm 1 2) = 47965 := by
  sorry

theorem card_ofSymmNsymm_three_one : Nat.card (ofSymmNsymm 3 1) = 988464 := by
  sorry

theorem card_ofSymmNsymm_five_zero : Nat.card (ofSymmNsymm 5 0) = 3849920 := by
  sorry

theorem card_ofAtoms_six : Nat.card (ofAtoms 6) = 4886349 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_five_zero) + $(card_ofSymmNsymm_three_one) +
      $(card_ofSymmNsymm_one_two))

theorem card_ofSymmNsymm_zero_three : Nat.card (ofSymmNsymm 0 3) = 4492953 := by
  sorry

theorem card_ofSymmNsymm_two_two : Nat.card (ofSymmNsymm 2 2) = 2186435732 := by
  sorry

theorem card_ofSymmNsymm_four_one : Nat.card (ofSymmNsymm 4 1) = 50265788140 := by
  sorry

theorem card_ofSymmNsymm_six_zero : Nat.card (ofSymmNsymm 6 0) = 292352449486 := by
  sorry

theorem card_ofAtoms_seven : Nat.card (ofAtoms 7) = 344809166311 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_six_zero) + $(card_ofSymmNsymm_four_one) +
      $(card_ofSymmNsymm_two_two) + $(card_ofSymmNsymm_zero_three))

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
