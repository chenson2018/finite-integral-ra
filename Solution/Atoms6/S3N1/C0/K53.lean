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

namespace K848

theorem c848 : P.sumLeaves 20 848 1 = 3921 := by decide +kernel

theorem c849 : P.sumLeaves 20 849 1 = 9752 := by decide +kernel

theorem c850 : P.sumLeaves 20 850 1 = 36032 := by decide +kernel

theorem c851 : P.sumLeaves 20 851 1 = 46974 := by decide +kernel

theorem c852 : P.sumLeaves 20 852 1 = 9752 := by decide +kernel

theorem c853 : P.sumLeaves 20 853 1 = 45617 := by decide +kernel

theorem c854 : P.sumLeaves 20 854 1 = 46974 := by decide +kernel

theorem c855 : P.sumLeaves 20 855 1 = 68666 := by decide +kernel

theorem c856 : P.sumLeaves 20 856 1 = 4728 := by decide +kernel

theorem c857 : P.sumLeaves 20 857 1 = 11913 := by decide +kernel

theorem c858 : P.sumLeaves 20 858 1 = 36285 := by decide +kernel

theorem c859 : P.sumLeaves 20 859 1 = 47903 := by decide +kernel

theorem c860 : P.sumLeaves 20 860 1 = 11913 := by decide +kernel

theorem c861 : P.sumLeaves 20 861 1 = 47702 := by decide +kernel

theorem c862 : P.sumLeaves 20 862 1 = 47903 := by decide +kernel

theorem c863 : P.sumLeaves 20 863 1 = 71965 := by decide +kernel

theorem total : P.sumLeaves 20 848 16 = 548000 :=
  sumLeaves_of_chunks (cs := [(1, 3921), (1, 9752), (1, 36032), (1, 46974), (1, 9752), (1, 45617), (1, 46974), (1, 68666), (1, 4728), (1, 11913), (1, 36285), (1, 47903), (1, 11913), (1, 47702), (1, 47903), (1, 71965)])
    (.cons c848 (.cons c849 (.cons c850 (.cons c851 (.cons c852 (.cons c853 (.cons c854 (.cons c855 (.cons c856 (.cons c857 (.cons c858 (.cons c859 (.cons c860 (.cons c861 (.cons c862 (.cons c863 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K848

end RACert.S3N1.C0
