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

namespace K384

theorem c384 : P.sumLeaves 20 384 1 = 260 := by decide +kernel

theorem c385 : P.sumLeaves 20 385 1 = 418 := by decide +kernel

theorem c386 : P.sumLeaves 20 386 1 = 915 := by decide +kernel

theorem c387 : P.sumLeaves 20 387 1 = 1770 := by decide +kernel

theorem c388 : P.sumLeaves 20 388 1 = 482 := by decide +kernel

theorem c389 : P.sumLeaves 20 389 1 = 1029 := by decide +kernel

theorem c390 : P.sumLeaves 20 390 1 = 1744 := by decide +kernel

theorem c391 : P.sumLeaves 20 391 1 = 4187 := by decide +kernel

theorem c392 : P.sumLeaves 20 392 1 = 338 := by decide +kernel

theorem c393 : P.sumLeaves 20 393 1 = 532 := by decide +kernel

theorem c394 : P.sumLeaves 20 394 1 = 1395 := by decide +kernel

theorem c395 : P.sumLeaves 20 395 1 = 2727 := by decide +kernel

theorem c396 : P.sumLeaves 20 396 1 = 616 := by decide +kernel

theorem c397 : P.sumLeaves 20 397 1 = 1314 := by decide +kernel

theorem c398 : P.sumLeaves 20 398 1 = 2704 := by decide +kernel

theorem c399 : P.sumLeaves 20 399 1 = 6449 := by decide +kernel

theorem total : P.sumLeaves 20 384 16 = 26880 :=
  sumLeaves_of_chunks (cs := [(1, 260), (1, 418), (1, 915), (1, 1770), (1, 482), (1, 1029), (1, 1744), (1, 4187), (1, 338), (1, 532), (1, 1395), (1, 2727), (1, 616), (1, 1314), (1, 2704), (1, 6449)])
    (.cons c384 (.cons c385 (.cons c386 (.cons c387 (.cons c388 (.cons c389 (.cons c390 (.cons c391 (.cons c392 (.cons c393 (.cons c394 (.cons c395 (.cons c396 (.cons c397 (.cons c398 (.cons c399 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K384

end RACert.S3N1.C0
