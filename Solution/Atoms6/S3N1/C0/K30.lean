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

namespace K480

theorem c480 : P.sumLeaves 20 480 1 = 3520 := by decide +kernel

theorem c481 : P.sumLeaves 20 481 1 = 4562 := by decide +kernel

theorem c482 : P.sumLeaves 20 482 1 = 14541 := by decide +kernel

theorem c483 : P.sumLeaves 20 483 1 = 16616 := by decide +kernel

theorem c484 : P.sumLeaves 20 484 1 = 4562 := by decide +kernel

theorem c485 : P.sumLeaves 20 485 1 = 8243 := by decide +kernel

theorem c486 : P.sumLeaves 20 486 1 = 16616 := by decide +kernel

theorem c487 : P.sumLeaves 20 487 1 = 19969 := by decide +kernel

theorem c488 : P.sumLeaves 20 488 1 = 12322 := by decide +kernel

theorem c489 : P.sumLeaves 20 489 1 = 14361 := by decide +kernel

theorem c490 : P.sumLeaves 20 490 1 = 31462 := by decide +kernel

theorem c491 : P.sumLeaves 20 491 1 = 35149 := by decide +kernel

theorem c492 : P.sumLeaves 20 492 1 = 14361 := by decide +kernel

theorem c493 : P.sumLeaves 20 493 1 = 25511 := by decide +kernel

theorem c494 : P.sumLeaves 20 494 1 = 35149 := by decide +kernel

theorem c495 : P.sumLeaves 20 495 1 = 42047 := by decide +kernel

theorem total : P.sumLeaves 20 480 16 = 298991 :=
  sumLeaves_of_chunks (cs := [(1, 3520), (1, 4562), (1, 14541), (1, 16616), (1, 4562), (1, 8243), (1, 16616), (1, 19969), (1, 12322), (1, 14361), (1, 31462), (1, 35149), (1, 14361), (1, 25511), (1, 35149), (1, 42047)])
    (.cons c480 (.cons c481 (.cons c482 (.cons c483 (.cons c484 (.cons c485 (.cons c486 (.cons c487 (.cons c488 (.cons c489 (.cons c490 (.cons c491 (.cons c492 (.cons c493 (.cons c494 (.cons c495 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K480

end RACert.S3N1.C0
