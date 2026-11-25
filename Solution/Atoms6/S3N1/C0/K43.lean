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

namespace K688

theorem c688 : P.sumLeaves 20 688 1 = 969 := by decide +kernel

theorem c689 : P.sumLeaves 20 689 1 = 964 := by decide +kernel

theorem c690 : P.sumLeaves 20 690 1 = 7694 := by decide +kernel

theorem c691 : P.sumLeaves 20 691 1 = 9441 := by decide +kernel

theorem c692 : P.sumLeaves 20 692 1 = 964 := by decide +kernel

theorem c693 : P.sumLeaves 20 693 1 = 3494 := by decide +kernel

theorem c694 : P.sumLeaves 20 694 1 = 9441 := by decide +kernel

theorem c695 : P.sumLeaves 20 695 1 = 33004 := by decide +kernel

theorem c696 : P.sumLeaves 20 696 1 = 1072 := by decide +kernel

theorem c697 : P.sumLeaves 20 697 1 = 1147 := by decide +kernel

theorem c698 : P.sumLeaves 20 698 1 = 7856 := by decide +kernel

theorem c699 : P.sumLeaves 20 699 1 = 9593 := by decide +kernel

theorem c700 : P.sumLeaves 20 700 1 = 1147 := by decide +kernel

theorem c701 : P.sumLeaves 20 701 1 = 3494 := by decide +kernel

theorem c702 : P.sumLeaves 20 702 1 = 9593 := by decide +kernel

theorem c703 : P.sumLeaves 20 703 1 = 34219 := by decide +kernel

theorem total : P.sumLeaves 20 688 16 = 134092 :=
  sumLeaves_of_chunks (cs := [(1, 969), (1, 964), (1, 7694), (1, 9441), (1, 964), (1, 3494), (1, 9441), (1, 33004), (1, 1072), (1, 1147), (1, 7856), (1, 9593), (1, 1147), (1, 3494), (1, 9593), (1, 34219)])
    (.cons c688 (.cons c689 (.cons c690 (.cons c691 (.cons c692 (.cons c693 (.cons c694 (.cons c695 (.cons c696 (.cons c697 (.cons c698 (.cons c699 (.cons c700 (.cons c701 (.cons c702 (.cons c703 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K688

end RACert.S3N1.C0
