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

namespace K592

theorem c592 : P.sumLeaves 20 592 1 = 308 := by decide +kernel

theorem c593 : P.sumLeaves 20 593 1 = 283 := by decide +kernel

theorem c594 : P.sumLeaves 20 594 1 = 688 := by decide +kernel

theorem c595 : P.sumLeaves 20 595 1 = 436 := by decide +kernel

theorem c596 : P.sumLeaves 20 596 1 = 283 := by decide +kernel

theorem c597 : P.sumLeaves 20 597 1 = 7149 := by decide +kernel

theorem c598 : P.sumLeaves 20 598 1 = 436 := by decide +kernel

theorem c599 : P.sumLeaves 20 599 1 = 15063 := by decide +kernel

theorem c600 : P.sumLeaves 20 600 1 = 372 := by decide +kernel

theorem c601 : P.sumLeaves 20 601 1 = 377 := by decide +kernel

theorem c602 : P.sumLeaves 20 602 1 = 688 := by decide +kernel

theorem c603 : P.sumLeaves 20 603 1 = 436 := by decide +kernel

theorem c604 : P.sumLeaves 20 604 1 = 377 := by decide +kernel

theorem c605 : P.sumLeaves 20 605 1 = 7389 := by decide +kernel

theorem c606 : P.sumLeaves 20 606 1 = 436 := by decide +kernel

theorem c607 : P.sumLeaves 20 607 1 = 15555 := by decide +kernel

theorem total : P.sumLeaves 20 592 16 = 50276 :=
  sumLeaves_of_chunks (cs := [(1, 308), (1, 283), (1, 688), (1, 436), (1, 283), (1, 7149), (1, 436), (1, 15063), (1, 372), (1, 377), (1, 688), (1, 436), (1, 377), (1, 7389), (1, 436), (1, 15555)])
    (.cons c592 (.cons c593 (.cons c594 (.cons c595 (.cons c596 (.cons c597 (.cons c598 (.cons c599 (.cons c600 (.cons c601 (.cons c602 (.cons c603 (.cons c604 (.cons c605 (.cons c606 (.cons c607 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K592

end RACert.S3N1.C0
