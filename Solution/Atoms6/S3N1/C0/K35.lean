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

namespace K560

theorem c560 : P.sumLeaves 20 560 1 = 164 := by decide +kernel

theorem c561 : P.sumLeaves 20 561 1 = 168 := by decide +kernel

theorem c562 : P.sumLeaves 20 562 1 = 312 := by decide +kernel

theorem c563 : P.sumLeaves 20 563 1 = 378 := by decide +kernel

theorem c564 : P.sumLeaves 20 564 1 = 678 := by decide +kernel

theorem c565 : P.sumLeaves 20 565 1 = 1064 := by decide +kernel

theorem c566 : P.sumLeaves 20 566 1 = 2644 := by decide +kernel

theorem c567 : P.sumLeaves 20 567 1 = 8383 := by decide +kernel

theorem c568 : P.sumLeaves 20 568 1 = 220 := by decide +kernel

theorem c569 : P.sumLeaves 20 569 1 = 248 := by decide +kernel

theorem c570 : P.sumLeaves 20 570 1 = 462 := by decide +kernel

theorem c571 : P.sumLeaves 20 571 1 = 572 := by decide +kernel

theorem c572 : P.sumLeaves 20 572 1 = 892 := by decide +kernel

theorem c573 : P.sumLeaves 20 573 1 = 1496 := by decide +kernel

theorem c574 : P.sumLeaves 20 574 1 = 3580 := by decide +kernel

theorem c575 : P.sumLeaves 20 575 1 = 11678 := by decide +kernel

theorem total : P.sumLeaves 20 560 16 = 32939 :=
  sumLeaves_of_chunks (cs := [(1, 164), (1, 168), (1, 312), (1, 378), (1, 678), (1, 1064), (1, 2644), (1, 8383), (1, 220), (1, 248), (1, 462), (1, 572), (1, 892), (1, 1496), (1, 3580), (1, 11678)])
    (.cons c560 (.cons c561 (.cons c562 (.cons c563 (.cons c564 (.cons c565 (.cons c566 (.cons c567 (.cons c568 (.cons c569 (.cons c570 (.cons c571 (.cons c572 (.cons c573 (.cons c574 (.cons c575 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K560

end RACert.S3N1.C0
