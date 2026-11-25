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

namespace K656

theorem c656 : P.sumLeaves 20 656 1 = 164 := by decide +kernel

theorem c657 : P.sumLeaves 20 657 1 = 678 := by decide +kernel

theorem c658 : P.sumLeaves 20 658 1 = 312 := by decide +kernel

theorem c659 : P.sumLeaves 20 659 1 = 2644 := by decide +kernel

theorem c660 : P.sumLeaves 20 660 1 = 168 := by decide +kernel

theorem c661 : P.sumLeaves 20 661 1 = 1064 := by decide +kernel

theorem c662 : P.sumLeaves 20 662 1 = 378 := by decide +kernel

theorem c663 : P.sumLeaves 20 663 1 = 8383 := by decide +kernel

theorem c664 : P.sumLeaves 20 664 1 = 220 := by decide +kernel

theorem c665 : P.sumLeaves 20 665 1 = 892 := by decide +kernel

theorem c666 : P.sumLeaves 20 666 1 = 462 := by decide +kernel

theorem c667 : P.sumLeaves 20 667 1 = 3580 := by decide +kernel

theorem c668 : P.sumLeaves 20 668 1 = 248 := by decide +kernel

theorem c669 : P.sumLeaves 20 669 1 = 1496 := by decide +kernel

theorem c670 : P.sumLeaves 20 670 1 = 572 := by decide +kernel

theorem c671 : P.sumLeaves 20 671 1 = 11678 := by decide +kernel

theorem total : P.sumLeaves 20 656 16 = 32939 :=
  sumLeaves_of_chunks (cs := [(1, 164), (1, 678), (1, 312), (1, 2644), (1, 168), (1, 1064), (1, 378), (1, 8383), (1, 220), (1, 892), (1, 462), (1, 3580), (1, 248), (1, 1496), (1, 572), (1, 11678)])
    (.cons c656 (.cons c657 (.cons c658 (.cons c659 (.cons c660 (.cons c661 (.cons c662 (.cons c663 (.cons c664 (.cons c665 (.cons c666 (.cons c667 (.cons c668 (.cons c669 (.cons c670 (.cons c671 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K656

end RACert.S3N1.C0
