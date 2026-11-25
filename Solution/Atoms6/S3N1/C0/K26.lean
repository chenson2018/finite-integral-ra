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

namespace K416

theorem c416 : P.sumLeaves 20 416 1 = 1320 := by decide +kernel

theorem c417 : P.sumLeaves 20 417 1 = 1624 := by decide +kernel

theorem c418 : P.sumLeaves 20 418 1 = 7723 := by decide +kernel

theorem c419 : P.sumLeaves 20 419 1 = 8492 := by decide +kernel

theorem c420 : P.sumLeaves 20 420 1 = 1624 := by decide +kernel

theorem c421 : P.sumLeaves 20 421 1 = 3197 := by decide +kernel

theorem c422 : P.sumLeaves 20 422 1 = 8492 := by decide +kernel

theorem c423 : P.sumLeaves 20 423 1 = 10713 := by decide +kernel

theorem c424 : P.sumLeaves 20 424 1 = 1741 := by decide +kernel

theorem c425 : P.sumLeaves 20 425 1 = 2200 := by decide +kernel

theorem c426 : P.sumLeaves 20 426 1 = 13278 := by decide +kernel

theorem c427 : P.sumLeaves 20 427 1 = 15075 := by decide +kernel

theorem c428 : P.sumLeaves 20 428 1 = 2200 := by decide +kernel

theorem c429 : P.sumLeaves 20 429 1 = 4537 := by decide +kernel

theorem c430 : P.sumLeaves 20 430 1 = 15075 := by decide +kernel

theorem c431 : P.sumLeaves 20 431 1 = 20026 := by decide +kernel

theorem total : P.sumLeaves 20 416 16 = 117317 :=
  sumLeaves_of_chunks (cs := [(1, 1320), (1, 1624), (1, 7723), (1, 8492), (1, 1624), (1, 3197), (1, 8492), (1, 10713), (1, 1741), (1, 2200), (1, 13278), (1, 15075), (1, 2200), (1, 4537), (1, 15075), (1, 20026)])
    (.cons c416 (.cons c417 (.cons c418 (.cons c419 (.cons c420 (.cons c421 (.cons c422 (.cons c423 (.cons c424 (.cons c425 (.cons c426 (.cons c427 (.cons c428 (.cons c429 (.cons c430 (.cons c431 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K416

end RACert.S3N1.C0
