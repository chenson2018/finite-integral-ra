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

namespace K576

theorem c576 : P.sumLeaves 20 576 1 = 164 := by decide +kernel

theorem c577 : P.sumLeaves 20 577 1 = 153 := by decide +kernel

theorem c578 : P.sumLeaves 20 578 1 = 274 := by decide +kernel

theorem c579 : P.sumLeaves 20 579 1 = 222 := by decide +kernel

theorem c580 : P.sumLeaves 20 580 1 = 153 := by decide +kernel

theorem c581 : P.sumLeaves 20 581 1 = 1035 := by decide +kernel

theorem c582 : P.sumLeaves 20 582 1 = 222 := by decide +kernel

theorem c583 : P.sumLeaves 20 583 1 = 3942 := by decide +kernel

theorem c584 : P.sumLeaves 20 584 1 = 332 := by decide +kernel

theorem c585 : P.sumLeaves 20 585 1 = 309 := by decide +kernel

theorem c586 : P.sumLeaves 20 586 1 = 420 := by decide +kernel

theorem c587 : P.sumLeaves 20 587 1 = 282 := by decide +kernel

theorem c588 : P.sumLeaves 20 588 1 = 309 := by decide +kernel

theorem c589 : P.sumLeaves 20 589 1 = 3504 := by decide +kernel

theorem c590 : P.sumLeaves 20 590 1 = 282 := by decide +kernel

theorem c591 : P.sumLeaves 20 591 1 = 6738 := by decide +kernel

theorem total : P.sumLeaves 20 576 16 = 18341 :=
  sumLeaves_of_chunks (cs := [(1, 164), (1, 153), (1, 274), (1, 222), (1, 153), (1, 1035), (1, 222), (1, 3942), (1, 332), (1, 309), (1, 420), (1, 282), (1, 309), (1, 3504), (1, 282), (1, 6738)])
    (.cons c576 (.cons c577 (.cons c578 (.cons c579 (.cons c580 (.cons c581 (.cons c582 (.cons c583 (.cons c584 (.cons c585 (.cons c586 (.cons c587 (.cons c588 (.cons c589 (.cons c590 (.cons c591 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K576

end RACert.S3N1.C0
