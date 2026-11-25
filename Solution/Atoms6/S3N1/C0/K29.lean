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

namespace K464

theorem c464 : P.sumLeaves 20 464 1 = 5160 := by decide +kernel

theorem c465 : P.sumLeaves 20 465 1 = 15676 := by decide +kernel

theorem c466 : P.sumLeaves 20 466 1 = 43857 := by decide +kernel

theorem c467 : P.sumLeaves 20 467 1 = 60115 := by decide +kernel

theorem c468 : P.sumLeaves 20 468 1 = 8162 := by decide +kernel

theorem c469 : P.sumLeaves 20 469 1 = 39170 := by decide +kernel

theorem c470 : P.sumLeaves 20 470 1 = 52943 := by decide +kernel

theorem c471 : P.sumLeaves 20 471 1 = 76414 := by decide +kernel

theorem c472 : P.sumLeaves 20 472 1 = 6220 := by decide +kernel

theorem c473 : P.sumLeaves 20 473 1 = 20025 := by decide +kernel

theorem c474 : P.sumLeaves 20 474 1 = 44854 := by decide +kernel

theorem c475 : P.sumLeaves 20 475 1 = 62972 := by decide +kernel

theorem c476 : P.sumLeaves 20 476 1 = 10108 := by decide +kernel

theorem c477 : P.sumLeaves 20 477 1 = 40619 := by decide +kernel

theorem c478 : P.sumLeaves 20 478 1 = 54088 := by decide +kernel

theorem c479 : P.sumLeaves 20 479 1 = 80013 := by decide +kernel

theorem total : P.sumLeaves 20 464 16 = 620396 :=
  sumLeaves_of_chunks (cs := [(1, 5160), (1, 15676), (1, 43857), (1, 60115), (1, 8162), (1, 39170), (1, 52943), (1, 76414), (1, 6220), (1, 20025), (1, 44854), (1, 62972), (1, 10108), (1, 40619), (1, 54088), (1, 80013)])
    (.cons c464 (.cons c465 (.cons c466 (.cons c467 (.cons c468 (.cons c469 (.cons c470 (.cons c471 (.cons c472 (.cons c473 (.cons c474 (.cons c475 (.cons c476 (.cons c477 (.cons c478 (.cons c479 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K464

end RACert.S3N1.C0
