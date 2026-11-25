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

namespace K608

theorem c608 : P.sumLeaves 20 608 1 = 164 := by decide +kernel

theorem c609 : P.sumLeaves 20 609 1 = 205 := by decide +kernel

theorem c610 : P.sumLeaves 20 610 1 = 210 := by decide +kernel

theorem c611 : P.sumLeaves 20 611 1 = 276 := by decide +kernel

theorem c612 : P.sumLeaves 20 612 1 = 597 := by decide +kernel

theorem c613 : P.sumLeaves 20 613 1 = 1729 := by decide +kernel

theorem c614 : P.sumLeaves 20 614 1 = 1637 := by decide +kernel

theorem c615 : P.sumLeaves 20 615 1 = 5771 := by decide +kernel

theorem c616 : P.sumLeaves 20 616 1 = 236 := by decide +kernel

theorem c617 : P.sumLeaves 20 617 1 = 303 := by decide +kernel

theorem c618 : P.sumLeaves 20 618 1 = 266 := by decide +kernel

theorem c619 : P.sumLeaves 20 619 1 = 366 := by decide +kernel

theorem c620 : P.sumLeaves 20 620 1 = 1128 := by decide +kernel

theorem c621 : P.sumLeaves 20 621 1 = 3468 := by decide +kernel

theorem c622 : P.sumLeaves 20 622 1 = 3045 := by decide +kernel

theorem c623 : P.sumLeaves 20 623 1 = 9770 := by decide +kernel

theorem total : P.sumLeaves 20 608 16 = 29171 :=
  sumLeaves_of_chunks (cs := [(1, 164), (1, 205), (1, 210), (1, 276), (1, 597), (1, 1729), (1, 1637), (1, 5771), (1, 236), (1, 303), (1, 266), (1, 366), (1, 1128), (1, 3468), (1, 3045), (1, 9770)])
    (.cons c608 (.cons c609 (.cons c610 (.cons c611 (.cons c612 (.cons c613 (.cons c614 (.cons c615 (.cons c616 (.cons c617 (.cons c618 (.cons c619 (.cons c620 (.cons c621 (.cons c622 (.cons c623 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K608

end RACert.S3N1.C0
