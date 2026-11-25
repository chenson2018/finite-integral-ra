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

namespace K880

theorem c880 : P.sumLeaves 20 880 1 = 6216 := by decide +kernel

theorem c881 : P.sumLeaves 20 881 1 = 10833 := by decide +kernel

theorem c882 : P.sumLeaves 20 882 1 = 45363 := by decide +kernel

theorem c883 : P.sumLeaves 20 883 1 = 55015 := by decide +kernel

theorem c884 : P.sumLeaves 20 884 1 = 21045 := by decide +kernel

theorem c885 : P.sumLeaves 20 885 1 = 52636 := by decide +kernel

theorem c886 : P.sumLeaves 20 886 1 = 62723 := by decide +kernel

theorem c887 : P.sumLeaves 20 887 1 = 79127 := by decide +kernel

theorem c888 : P.sumLeaves 20 888 1 = 7713 := by decide +kernel

theorem c889 : P.sumLeaves 20 889 1 = 13582 := by decide +kernel

theorem c890 : P.sumLeaves 20 890 1 = 46545 := by decide +kernel

theorem c891 : P.sumLeaves 20 891 1 = 56448 := by decide +kernel

theorem c892 : P.sumLeaves 20 892 1 = 27609 := by decide +kernel

theorem c893 : P.sumLeaves 20 893 1 = 55308 := by decide +kernel

theorem c894 : P.sumLeaves 20 894 1 = 66069 := by decide +kernel

theorem c895 : P.sumLeaves 20 895 1 = 83303 := by decide +kernel

theorem total : P.sumLeaves 20 880 16 = 689535 :=
  sumLeaves_of_chunks (cs := [(1, 6216), (1, 10833), (1, 45363), (1, 55015), (1, 21045), (1, 52636), (1, 62723), (1, 79127), (1, 7713), (1, 13582), (1, 46545), (1, 56448), (1, 27609), (1, 55308), (1, 66069), (1, 83303)])
    (.cons c880 (.cons c881 (.cons c882 (.cons c883 (.cons c884 (.cons c885 (.cons c886 (.cons c887 (.cons c888 (.cons c889 (.cons c890 (.cons c891 (.cons c892 (.cons c893 (.cons c894 (.cons c895 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K880

end RACert.S3N1.C0
