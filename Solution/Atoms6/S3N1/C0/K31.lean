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

namespace K496

theorem c496 : P.sumLeaves 20 496 1 = 12607 := by decide +kernel

theorem c497 : P.sumLeaves 20 497 1 = 17820 := by decide +kernel

theorem c498 : P.sumLeaves 20 498 1 = 59933 := by decide +kernel

theorem c499 : P.sumLeaves 20 499 1 = 70761 := by decide +kernel

theorem c500 : P.sumLeaves 20 500 1 = 17820 := by decide +kernel

theorem c501 : P.sumLeaves 20 501 1 = 44443 := by decide +kernel

theorem c502 : P.sumLeaves 20 502 1 = 70761 := by decide +kernel

theorem c503 : P.sumLeaves 20 503 1 = 89473 := by decide +kernel

theorem c504 : P.sumLeaves 20 504 1 = 17963 := by decide +kernel

theorem c505 : P.sumLeaves 20 505 1 = 24292 := by decide +kernel

theorem c506 : P.sumLeaves 20 506 1 = 63850 := by decide +kernel

theorem c507 : P.sumLeaves 20 507 1 = 74998 := by decide +kernel

theorem c508 : P.sumLeaves 20 508 1 = 24292 := by decide +kernel

theorem c509 : P.sumLeaves 20 509 1 = 46795 := by decide +kernel

theorem c510 : P.sumLeaves 20 510 1 = 74998 := by decide +kernel

theorem c511 : P.sumLeaves 20 511 1 = 94877 := by decide +kernel

theorem total : P.sumLeaves 20 496 16 = 805683 :=
  sumLeaves_of_chunks (cs := [(1, 12607), (1, 17820), (1, 59933), (1, 70761), (1, 17820), (1, 44443), (1, 70761), (1, 89473), (1, 17963), (1, 24292), (1, 63850), (1, 74998), (1, 24292), (1, 46795), (1, 74998), (1, 94877)])
    (.cons c496 (.cons c497 (.cons c498 (.cons c499 (.cons c500 (.cons c501 (.cons c502 (.cons c503 (.cons c504 (.cons c505 (.cons c506 (.cons c507 (.cons c508 (.cons c509 (.cons c510 (.cons c511 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K496

end RACert.S3N1.C0
