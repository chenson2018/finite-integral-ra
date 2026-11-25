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

namespace K352

theorem c352 : P.sumLeaves 20 352 1 = 1116 := by decide +kernel

theorem c353 : P.sumLeaves 20 353 1 = 1572 := by decide +kernel

theorem c354 : P.sumLeaves 20 354 1 = 8506 := by decide +kernel

theorem c355 : P.sumLeaves 20 355 1 = 9034 := by decide +kernel

theorem c356 : P.sumLeaves 20 356 1 = 2736 := by decide +kernel

theorem c357 : P.sumLeaves 20 357 1 = 5015 := by decide +kernel

theorem c358 : P.sumLeaves 20 358 1 = 11317 := by decide +kernel

theorem c359 : P.sumLeaves 20 359 1 = 13138 := by decide +kernel

theorem c360 : P.sumLeaves 20 360 1 = 2294 := by decide +kernel

theorem c361 : P.sumLeaves 20 361 1 = 3397 := by decide +kernel

theorem c362 : P.sumLeaves 20 362 1 = 16765 := by decide +kernel

theorem c363 : P.sumLeaves 20 363 1 = 18307 := by decide +kernel

theorem c364 : P.sumLeaves 20 364 1 = 6228 := by decide +kernel

theorem c365 : P.sumLeaves 20 365 1 = 11548 := by decide +kernel

theorem c366 : P.sumLeaves 20 366 1 = 22912 := by decide +kernel

theorem c367 : P.sumLeaves 20 367 1 = 27959 := by decide +kernel

theorem total : P.sumLeaves 20 352 16 = 161844 :=
  sumLeaves_of_chunks (cs := [(1, 1116), (1, 1572), (1, 8506), (1, 9034), (1, 2736), (1, 5015), (1, 11317), (1, 13138), (1, 2294), (1, 3397), (1, 16765), (1, 18307), (1, 6228), (1, 11548), (1, 22912), (1, 27959)])
    (.cons c352 (.cons c353 (.cons c354 (.cons c355 (.cons c356 (.cons c357 (.cons c358 (.cons c359 (.cons c360 (.cons c361 (.cons c362 (.cons c363 (.cons c364 (.cons c365 (.cons c366 (.cons c367 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K352

end RACert.S3N1.C0
