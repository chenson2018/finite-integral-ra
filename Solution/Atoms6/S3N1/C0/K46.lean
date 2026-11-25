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

namespace K736

theorem c736 : P.sumLeaves 20 736 1 = 679 := by decide +kernel

theorem c737 : P.sumLeaves 20 737 1 = 1073 := by decide +kernel

theorem c738 : P.sumLeaves 20 738 1 = 1986 := by decide +kernel

theorem c739 : P.sumLeaves 20 739 1 = 2976 := by decide +kernel

theorem c740 : P.sumLeaves 20 740 1 = 1073 := by decide +kernel

theorem c741 : P.sumLeaves 20 741 1 = 4885 := by decide +kernel

theorem c742 : P.sumLeaves 20 742 1 = 2976 := by decide +kernel

theorem c743 : P.sumLeaves 20 743 1 = 11539 := by decide +kernel

theorem c744 : P.sumLeaves 20 744 1 = 2513 := by decide +kernel

theorem c745 : P.sumLeaves 20 745 1 = 4563 := by decide +kernel

theorem c746 : P.sumLeaves 20 746 1 = 5326 := by decide +kernel

theorem c747 : P.sumLeaves 20 747 1 = 8289 := by decide +kernel

theorem c748 : P.sumLeaves 20 748 1 = 4563 := by decide +kernel

theorem c749 : P.sumLeaves 20 749 1 = 17783 := by decide +kernel

theorem c750 : P.sumLeaves 20 750 1 = 8289 := by decide +kernel

theorem c751 : P.sumLeaves 20 751 1 = 26748 := by decide +kernel

theorem total : P.sumLeaves 20 736 16 = 105261 :=
  sumLeaves_of_chunks (cs := [(1, 679), (1, 1073), (1, 1986), (1, 2976), (1, 1073), (1, 4885), (1, 2976), (1, 11539), (1, 2513), (1, 4563), (1, 5326), (1, 8289), (1, 4563), (1, 17783), (1, 8289), (1, 26748)])
    (.cons c736 (.cons c737 (.cons c738 (.cons c739 (.cons c740 (.cons c741 (.cons c742 (.cons c743 (.cons c744 (.cons c745 (.cons c746 (.cons c747 (.cons c748 (.cons c749 (.cons c750 (.cons c751 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K736

end RACert.S3N1.C0
