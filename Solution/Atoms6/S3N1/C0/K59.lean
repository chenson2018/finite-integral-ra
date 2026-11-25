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

namespace K944

theorem c944 : P.sumLeaves 20 944 1 = 5975 := by decide +kernel

theorem c945 : P.sumLeaves 20 945 1 = 10045 := by decide +kernel

theorem c946 : P.sumLeaves 20 946 1 = 44698 := by decide +kernel

theorem c947 : P.sumLeaves 20 947 1 = 53108 := by decide +kernel

theorem c948 : P.sumLeaves 20 948 1 = 10045 := by decide +kernel

theorem c949 : P.sumLeaves 20 949 1 = 31908 := by decide +kernel

theorem c950 : P.sumLeaves 20 950 1 = 53108 := by decide +kernel

theorem c951 : P.sumLeaves 20 951 1 = 66234 := by decide +kernel

theorem c952 : P.sumLeaves 20 952 1 = 7459 := by decide +kernel

theorem c953 : P.sumLeaves 20 953 1 = 12624 := by decide +kernel

theorem c954 : P.sumLeaves 20 954 1 = 46969 := by decide +kernel

theorem c955 : P.sumLeaves 20 955 1 = 55612 := by decide +kernel

theorem c956 : P.sumLeaves 20 956 1 = 12624 := by decide +kernel

theorem c957 : P.sumLeaves 20 957 1 = 32322 := by decide +kernel

theorem c958 : P.sumLeaves 20 958 1 = 55612 := by decide +kernel

theorem c959 : P.sumLeaves 20 959 1 = 69421 := by decide +kernel

theorem total : P.sumLeaves 20 944 16 = 567764 :=
  sumLeaves_of_chunks (cs := [(1, 5975), (1, 10045), (1, 44698), (1, 53108), (1, 10045), (1, 31908), (1, 53108), (1, 66234), (1, 7459), (1, 12624), (1, 46969), (1, 55612), (1, 12624), (1, 32322), (1, 55612), (1, 69421)])
    (.cons c944 (.cons c945 (.cons c946 (.cons c947 (.cons c948 (.cons c949 (.cons c950 (.cons c951 (.cons c952 (.cons c953 (.cons c954 (.cons c955 (.cons c956 (.cons c957 (.cons c958 (.cons c959 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K944

end RACert.S3N1.C0
