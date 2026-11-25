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

namespace K1008

theorem c1008 : P.sumLeaves 20 1008 1 = 14663 := by decide +kernel

theorem c1009 : P.sumLeaves 20 1009 1 = 23684 := by decide +kernel

theorem c1010 : P.sumLeaves 20 1010 1 = 62828 := by decide +kernel

theorem c1011 : P.sumLeaves 20 1011 1 = 74355 := by decide +kernel

theorem c1012 : P.sumLeaves 20 1012 1 = 23684 := by decide +kernel

theorem c1013 : P.sumLeaves 20 1013 1 = 62370 := by decide +kernel

theorem c1014 : P.sumLeaves 20 1014 1 = 74355 := by decide +kernel

theorem c1015 : P.sumLeaves 20 1015 1 = 94623 := by decide +kernel

theorem c1016 : P.sumLeaves 20 1016 1 = 21007 := by decide +kernel

theorem c1017 : P.sumLeaves 20 1017 1 = 32721 := by decide +kernel

theorem c1018 : P.sumLeaves 20 1018 1 = 67217 := by decide +kernel

theorem c1019 : P.sumLeaves 20 1019 1 = 79207 := by decide +kernel

theorem c1020 : P.sumLeaves 20 1020 1 = 32721 := by decide +kernel

theorem c1021 : P.sumLeaves 20 1021 1 = 66398 := by decide +kernel

theorem c1022 : P.sumLeaves 20 1022 1 = 79207 := by decide +kernel

theorem c1023 : P.sumLeaves 20 1023 1 = 100805 := by decide +kernel

theorem total : P.sumLeaves 20 1008 16 = 909845 :=
  sumLeaves_of_chunks (cs := [(1, 14663), (1, 23684), (1, 62828), (1, 74355), (1, 23684), (1, 62370), (1, 74355), (1, 94623), (1, 21007), (1, 32721), (1, 67217), (1, 79207), (1, 32721), (1, 66398), (1, 79207), (1, 100805)])
    (.cons c1008 (.cons c1009 (.cons c1010 (.cons c1011 (.cons c1012 (.cons c1013 (.cons c1014 (.cons c1015 (.cons c1016 (.cons c1017 (.cons c1018 (.cons c1019 (.cons c1020 (.cons c1021 (.cons c1022 (.cons c1023 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K1008

end RACert.S3N1.C0
