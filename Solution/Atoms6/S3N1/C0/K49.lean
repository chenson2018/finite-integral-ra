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

namespace K784

theorem c784 : P.sumLeaves 20 784 1 = 2056 := by decide +kernel

theorem c785 : P.sumLeaves 20 785 1 = 1831 := by decide +kernel

theorem c786 : P.sumLeaves 20 786 1 = 4902 := by decide +kernel

theorem c787 : P.sumLeaves 20 787 1 = 7862 := by decide +kernel

theorem c788 : P.sumLeaves 20 788 1 = 1831 := by decide +kernel

theorem c789 : P.sumLeaves 20 789 1 = 7509 := by decide +kernel

theorem c790 : P.sumLeaves 20 790 1 = 7862 := by decide +kernel

theorem c791 : P.sumLeaves 20 791 1 = 21169 := by decide +kernel

theorem c792 : P.sumLeaves 20 792 1 = 2887 := by decide +kernel

theorem c793 : P.sumLeaves 20 793 1 = 2423 := by decide +kernel

theorem c794 : P.sumLeaves 20 794 1 = 5278 := by decide +kernel

theorem c795 : P.sumLeaves 20 795 1 = 8560 := by decide +kernel

theorem c796 : P.sumLeaves 20 796 1 = 2423 := by decide +kernel

theorem c797 : P.sumLeaves 20 797 1 = 7914 := by decide +kernel

theorem c798 : P.sumLeaves 20 798 1 = 8560 := by decide +kernel

theorem c799 : P.sumLeaves 20 799 1 = 24605 := by decide +kernel

theorem total : P.sumLeaves 20 784 16 = 117672 :=
  sumLeaves_of_chunks (cs := [(1, 2056), (1, 1831), (1, 4902), (1, 7862), (1, 1831), (1, 7509), (1, 7862), (1, 21169), (1, 2887), (1, 2423), (1, 5278), (1, 8560), (1, 2423), (1, 7914), (1, 8560), (1, 24605)])
    (.cons c784 (.cons c785 (.cons c786 (.cons c787 (.cons c788 (.cons c789 (.cons c790 (.cons c791 (.cons c792 (.cons c793 (.cons c794 (.cons c795 (.cons c796 (.cons c797 (.cons c798 (.cons c799 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K784

end RACert.S3N1.C0
