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

namespace K752

theorem c752 : P.sumLeaves 20 752 1 = 5494 := by decide +kernel

theorem c753 : P.sumLeaves 20 753 1 = 8687 := by decide +kernel

theorem c754 : P.sumLeaves 20 754 1 = 16630 := by decide +kernel

theorem c755 : P.sumLeaves 20 755 1 = 24165 := by decide +kernel

theorem c756 : P.sumLeaves 20 756 1 = 8687 := by decide +kernel

theorem c757 : P.sumLeaves 20 757 1 = 32312 := by decide +kernel

theorem c758 : P.sumLeaves 20 758 1 = 24165 := by decide +kernel

theorem c759 : P.sumLeaves 20 759 1 = 64172 := by decide +kernel

theorem c760 : P.sumLeaves 20 760 1 = 7470 := by decide +kernel

theorem c761 : P.sumLeaves 20 761 1 = 11582 := by decide +kernel

theorem c762 : P.sumLeaves 20 762 1 = 17356 := by decide +kernel

theorem c763 : P.sumLeaves 20 763 1 = 25558 := by decide +kernel

theorem c764 : P.sumLeaves 20 764 1 = 11582 := by decide +kernel

theorem c765 : P.sumLeaves 20 765 1 = 34289 := by decide +kernel

theorem c766 : P.sumLeaves 20 766 1 = 25558 := by decide +kernel

theorem c767 : P.sumLeaves 20 767 1 = 68171 := by decide +kernel

theorem total : P.sumLeaves 20 752 16 = 385878 :=
  sumLeaves_of_chunks (cs := [(1, 5494), (1, 8687), (1, 16630), (1, 24165), (1, 8687), (1, 32312), (1, 24165), (1, 64172), (1, 7470), (1, 11582), (1, 17356), (1, 25558), (1, 11582), (1, 34289), (1, 25558), (1, 68171)])
    (.cons c752 (.cons c753 (.cons c754 (.cons c755 (.cons c756 (.cons c757 (.cons c758 (.cons c759 (.cons c760 (.cons c761 (.cons c762 (.cons c763 (.cons c764 (.cons c765 (.cons c766 (.cons c767 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K752

end RACert.S3N1.C0
