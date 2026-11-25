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

namespace K800

theorem c800 : P.sumLeaves 20 800 1 = 304 := by decide +kernel

theorem c801 : P.sumLeaves 20 801 1 = 668 := by decide +kernel

theorem c802 : P.sumLeaves 20 802 1 = 1080 := by decide +kernel

theorem c803 : P.sumLeaves 20 803 1 = 2106 := by decide +kernel

theorem c804 : P.sumLeaves 20 804 1 = 674 := by decide +kernel

theorem c805 : P.sumLeaves 20 805 1 = 1770 := by decide +kernel

theorem c806 : P.sumLeaves 20 806 1 = 2070 := by decide +kernel

theorem c807 : P.sumLeaves 20 807 1 = 4593 := by decide +kernel

theorem c808 : P.sumLeaves 20 808 1 = 382 := by decide +kernel

theorem c809 : P.sumLeaves 20 809 1 = 876 := by decide +kernel

theorem c810 : P.sumLeaves 20 810 1 = 1669 := by decide +kernel

theorem c811 : P.sumLeaves 20 811 1 = 3255 := by decide +kernel

theorem c812 : P.sumLeaves 20 812 1 = 893 := by decide +kernel

theorem c813 : P.sumLeaves 20 813 1 = 2464 := by decide +kernel

theorem c814 : P.sumLeaves 20 814 1 = 3191 := by decide +kernel

theorem c815 : P.sumLeaves 20 815 1 = 6987 := by decide +kernel

theorem total : P.sumLeaves 20 800 16 = 32982 :=
  sumLeaves_of_chunks (cs := [(1, 304), (1, 668), (1, 1080), (1, 2106), (1, 674), (1, 1770), (1, 2070), (1, 4593), (1, 382), (1, 876), (1, 1669), (1, 3255), (1, 893), (1, 2464), (1, 3191), (1, 6987)])
    (.cons c800 (.cons c801 (.cons c802 (.cons c803 (.cons c804 (.cons c805 (.cons c806 (.cons c807 (.cons c808 (.cons c809 (.cons c810 (.cons c811 (.cons c812 (.cons c813 (.cons c814 (.cons c815 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K800

end RACert.S3N1.C0
