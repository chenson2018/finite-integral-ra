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

namespace K368

theorem c368 : P.sumLeaves 20 368 1 = 5160 := by decide +kernel

theorem c369 : P.sumLeaves 20 369 1 = 8162 := by decide +kernel

theorem c370 : P.sumLeaves 20 370 1 = 43857 := by decide +kernel

theorem c371 : P.sumLeaves 20 371 1 = 52943 := by decide +kernel

theorem c372 : P.sumLeaves 20 372 1 = 15676 := by decide +kernel

theorem c373 : P.sumLeaves 20 373 1 = 39170 := by decide +kernel

theorem c374 : P.sumLeaves 20 374 1 = 60115 := by decide +kernel

theorem c375 : P.sumLeaves 20 375 1 = 76414 := by decide +kernel

theorem c376 : P.sumLeaves 20 376 1 = 6220 := by decide +kernel

theorem c377 : P.sumLeaves 20 377 1 = 10108 := by decide +kernel

theorem c378 : P.sumLeaves 20 378 1 = 44854 := by decide +kernel

theorem c379 : P.sumLeaves 20 379 1 = 54088 := by decide +kernel

theorem c380 : P.sumLeaves 20 380 1 = 20025 := by decide +kernel

theorem c381 : P.sumLeaves 20 381 1 = 40619 := by decide +kernel

theorem c382 : P.sumLeaves 20 382 1 = 62972 := by decide +kernel

theorem c383 : P.sumLeaves 20 383 1 = 80013 := by decide +kernel

theorem total : P.sumLeaves 20 368 16 = 620396 :=
  sumLeaves_of_chunks (cs := [(1, 5160), (1, 8162), (1, 43857), (1, 52943), (1, 15676), (1, 39170), (1, 60115), (1, 76414), (1, 6220), (1, 10108), (1, 44854), (1, 54088), (1, 20025), (1, 40619), (1, 62972), (1, 80013)])
    (.cons c368 (.cons c369 (.cons c370 (.cons c371 (.cons c372 (.cons c373 (.cons c374 (.cons c375 (.cons c376 (.cons c377 (.cons c378 (.cons c379 (.cons c380 (.cons c381 (.cons c382 (.cons c383 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K368

end RACert.S3N1.C0
