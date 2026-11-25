/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S3N1.C0.Defs

/-! Generated certificate chunk; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000

@[expose] public section

namespace RACert.S3N1.C0

open RACert RACert.Problem

namespace K832

theorem c832 : P.sumLeaves 20 832 1 = 844 := by decide +kernel

theorem c833 : P.sumLeaves 20 833 1 = 1542 := by decide +kernel

theorem c834 : P.sumLeaves 20 834 1 = 6155 := by decide +kernel

theorem c835 : P.sumLeaves 20 835 1 = 7426 := by decide +kernel

theorem c836 : P.sumLeaves 20 836 1 = 1542 := by decide +kernel

theorem c837 : P.sumLeaves 20 837 1 = 4931 := by decide +kernel

theorem c838 : P.sumLeaves 20 838 1 = 7426 := by decide +kernel

theorem c839 : P.sumLeaves 20 839 1 = 11422 := by decide +kernel

theorem c840 : P.sumLeaves 20 840 1 = 2540 := by decide +kernel

theorem c841 : P.sumLeaves 20 841 1 = 5230 := by decide +kernel

theorem c842 : P.sumLeaves 20 842 1 = 13038 := by decide +kernel

theorem c843 : P.sumLeaves 20 843 1 = 16292 := by decide +kernel

theorem c844 : P.sumLeaves 20 844 1 = 5230 := by decide +kernel

theorem c845 : P.sumLeaves 20 845 1 = 17086 := by decide +kernel

theorem c846 : P.sumLeaves 20 846 1 = 16292 := by decide +kernel

theorem c847 : P.sumLeaves 20 847 1 = 25580 := by decide +kernel

theorem total : P.sumLeaves 20 832 16 = 142576 :=
  sumLeaves_of_chunks (cs := [(1, 844), (1, 1542), (1, 6155), (1, 7426), (1, 1542), (1, 4931), (1, 7426), (1, 11422), (1, 2540), (1, 5230), (1, 13038), (1, 16292), (1, 5230), (1, 17086), (1, 16292), (1, 25580)])
    (.cons c832 (.cons c833 (.cons c834 (.cons c835 (.cons c836 (.cons c837 (.cons c838 (.cons c839 (.cons c840 (.cons c841 (.cons c842 (.cons c843 (.cons c844 (.cons c845 (.cons c846 (.cons c847 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K832

end RACert.S3N1.C0
