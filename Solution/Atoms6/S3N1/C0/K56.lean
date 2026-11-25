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

namespace K896

theorem c896 : P.sumLeaves 20 896 1 = 304 := by decide +kernel

theorem c897 : P.sumLeaves 20 897 1 = 674 := by decide +kernel

theorem c898 : P.sumLeaves 20 898 1 = 1080 := by decide +kernel

theorem c899 : P.sumLeaves 20 899 1 = 2070 := by decide +kernel

theorem c900 : P.sumLeaves 20 900 1 = 668 := by decide +kernel

theorem c901 : P.sumLeaves 20 901 1 = 1770 := by decide +kernel

theorem c902 : P.sumLeaves 20 902 1 = 2106 := by decide +kernel

theorem c903 : P.sumLeaves 20 903 1 = 4593 := by decide +kernel

theorem c904 : P.sumLeaves 20 904 1 = 382 := by decide +kernel

theorem c905 : P.sumLeaves 20 905 1 = 893 := by decide +kernel

theorem c906 : P.sumLeaves 20 906 1 = 1669 := by decide +kernel

theorem c907 : P.sumLeaves 20 907 1 = 3191 := by decide +kernel

theorem c908 : P.sumLeaves 20 908 1 = 876 := by decide +kernel

theorem c909 : P.sumLeaves 20 909 1 = 2464 := by decide +kernel

theorem c910 : P.sumLeaves 20 910 1 = 3255 := by decide +kernel

theorem c911 : P.sumLeaves 20 911 1 = 6987 := by decide +kernel

theorem total : P.sumLeaves 20 896 16 = 32982 :=
  sumLeaves_of_chunks (cs := [(1, 304), (1, 674), (1, 1080), (1, 2070), (1, 668), (1, 1770), (1, 2106), (1, 4593), (1, 382), (1, 893), (1, 1669), (1, 3191), (1, 876), (1, 2464), (1, 3255), (1, 6987)])
    (.cons c896 (.cons c897 (.cons c898 (.cons c899 (.cons c900 (.cons c901 (.cons c902 (.cons c903 (.cons c904 (.cons c905 (.cons c906 (.cons c907 (.cons c908 (.cons c909 (.cons c910 (.cons c911 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K896

end RACert.S3N1.C0
