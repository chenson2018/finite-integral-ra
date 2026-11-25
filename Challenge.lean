/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_zero_zero : (ofSymmNsymm 0 0).encard = 1 := by
  sorry

theorem encard_ofAtoms_one : (ofAtoms 1).encard = 1 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm] using encard_ofSymmNsymm_zero_zero

theorem encard_ofSymmNsymm_one_zero : (ofSymmNsymm 1 0).encard = 2 := by
  sorry

theorem encard_ofAtoms_two : (ofAtoms 2).encard = 2 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm] using encard_ofSymmNsymm_one_zero

theorem encard_ofSymmNsymm_zero_one : (ofSymmNsymm 0 1).encard = 3 := by
  sorry

theorem encard_ofSymmNsymm_two_zero : (ofSymmNsymm 2 0).encard = 7 := by
  sorry

theorem encard_ofAtoms_three : (ofAtoms 3).encard = 10 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_zero_one) + $(encard_ofSymmNsymm_two_zero))

theorem encard_ofSymmNsymm_one_one : (ofSymmNsymm 1 1).encard = 37 := by
  sorry

theorem encard_ofSymmNsymm_three_zero : (ofSymmNsymm 3 0).encard = 65 := by
  sorry

theorem encard_ofAtoms_four : (ofAtoms 4).encard = 102 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_one_one) + $(encard_ofSymmNsymm_three_zero))

theorem encard_ofSymmNsymm_zero_two : (ofSymmNsymm 0 2).encard = 83 := by
  sorry

theorem encard_ofSymmNsymm_two_one : (ofSymmNsymm 2 1).encard = 1316 := by
  sorry

theorem encard_ofSymmNsymm_four_zero : (ofSymmNsymm 4 0).encard = 3013 := by
  sorry

theorem encard_ofAtoms_five : (ofAtoms 5).encard = 4412 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_zero_two) + $(encard_ofSymmNsymm_two_one) +
      $(encard_ofSymmNsymm_four_zero))

theorem encard_ofSymmNsymm_one_two : (ofSymmNsymm 1 2).encard = 47965 := by
  sorry

theorem encard_ofSymmNsymm_three_one : (ofSymmNsymm 3 1).encard = 988464 := by
  sorry

theorem encard_ofSymmNsymm_five_zero : (ofSymmNsymm 5 0).encard = 3849920 := by
  sorry

theorem encard_ofAtoms_six : (ofAtoms 6).encard = 4886349 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_one_two) + $(encard_ofSymmNsymm_three_one) +
      $(encard_ofSymmNsymm_five_zero))

theorem encard_ofSymmNsymm_zero_three : (ofSymmNsymm 0 3).encard = 4492953 := by
  sorry

theorem encard_ofSymmNsymm_two_two : (ofSymmNsymm 2 2).encard = 2186435732 := by
  sorry

theorem encard_ofSymmNsymm_four_one : (ofSymmNsymm 4 1).encard = 50265788140 := by
  sorry

theorem encard_ofSymmNsymm_six_zero : (ofSymmNsymm 6 0).encard = 292352449486 := by
  sorry

theorem encard_ofAtoms_seven : (ofAtoms 7).encard = 344809166311 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(encard_ofSymmNsymm_zero_three) + $(encard_ofSymmNsymm_two_two) +
      $(encard_ofSymmNsymm_four_one) + $(encard_ofSymmNsymm_six_zero))

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
