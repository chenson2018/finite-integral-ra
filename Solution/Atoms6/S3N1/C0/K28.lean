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

namespace K448

theorem c448 : P.sumLeaves 20 448 1 = 1116 := by decide +kernel

theorem c449 : P.sumLeaves 20 449 1 = 2736 := by decide +kernel

theorem c450 : P.sumLeaves 20 450 1 = 8506 := by decide +kernel

theorem c451 : P.sumLeaves 20 451 1 = 11317 := by decide +kernel

theorem c452 : P.sumLeaves 20 452 1 = 1572 := by decide +kernel

theorem c453 : P.sumLeaves 20 453 1 = 5015 := by decide +kernel

theorem c454 : P.sumLeaves 20 454 1 = 9034 := by decide +kernel

theorem c455 : P.sumLeaves 20 455 1 = 13138 := by decide +kernel

theorem c456 : P.sumLeaves 20 456 1 = 2294 := by decide +kernel

theorem c457 : P.sumLeaves 20 457 1 = 6228 := by decide +kernel

theorem c458 : P.sumLeaves 20 458 1 = 16765 := by decide +kernel

theorem c459 : P.sumLeaves 20 459 1 = 22912 := by decide +kernel

theorem c460 : P.sumLeaves 20 460 1 = 3397 := by decide +kernel

theorem c461 : P.sumLeaves 20 461 1 = 11548 := by decide +kernel

theorem c462 : P.sumLeaves 20 462 1 = 18307 := by decide +kernel

theorem c463 : P.sumLeaves 20 463 1 = 27959 := by decide +kernel

theorem total : P.sumLeaves 20 448 16 = 161844 :=
  sumLeaves_of_chunks (cs := [(1, 1116), (1, 2736), (1, 8506), (1, 11317), (1, 1572), (1, 5015), (1, 9034), (1, 13138), (1, 2294), (1, 6228), (1, 16765), (1, 22912), (1, 3397), (1, 11548), (1, 18307), (1, 27959)])
    (.cons c448 (.cons c449 (.cons c450 (.cons c451 (.cons c452 (.cons c453 (.cons c454 (.cons c455 (.cons c456 (.cons c457 (.cons c458 (.cons c459 (.cons c460 (.cons c461 (.cons c462 (.cons c463 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K448

end RACert.S3N1.C0
