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

namespace K624

theorem c624 : P.sumLeaves 20 624 1 = 280 := by decide +kernel

theorem c625 : P.sumLeaves 20 625 1 = 365 := by decide +kernel

theorem c626 : P.sumLeaves 20 626 1 = 450 := by decide +kernel

theorem c627 : P.sumLeaves 20 627 1 = 652 := by decide +kernel

theorem c628 : P.sumLeaves 20 628 1 = 2635 := by decide +kernel

theorem c629 : P.sumLeaves 20 629 1 = 9122 := by decide +kernel

theorem c630 : P.sumLeaves 20 630 1 = 9165 := by decide +kernel

theorem c631 : P.sumLeaves 20 631 1 = 22154 := by decide +kernel

theorem c632 : P.sumLeaves 20 632 1 = 316 := by decide +kernel

theorem c633 : P.sumLeaves 20 633 1 = 461 := by decide +kernel

theorem c634 : P.sumLeaves 20 634 1 = 450 := by decide +kernel

theorem c635 : P.sumLeaves 20 635 1 = 652 := by decide +kernel

theorem c636 : P.sumLeaves 20 636 1 = 3238 := by decide +kernel

theorem c637 : P.sumLeaves 20 637 1 = 9270 := by decide +kernel

theorem c638 : P.sumLeaves 20 638 1 = 9333 := by decide +kernel

theorem c639 : P.sumLeaves 20 639 1 = 23293 := by decide +kernel

theorem total : P.sumLeaves 20 624 16 = 91836 :=
  sumLeaves_of_chunks (cs := [(1, 280), (1, 365), (1, 450), (1, 652), (1, 2635), (1, 9122), (1, 9165), (1, 22154), (1, 316), (1, 461), (1, 450), (1, 652), (1, 3238), (1, 9270), (1, 9333), (1, 23293)])
    (.cons c624 (.cons c625 (.cons c626 (.cons c627 (.cons c628 (.cons c629 (.cons c630 (.cons c631 (.cons c632 (.cons c633 (.cons c634 (.cons c635 (.cons c636 (.cons c637 (.cons c638 (.cons c639 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K624

end RACert.S3N1.C0
