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

namespace K976

theorem c976 : P.sumLeaves 20 976 1 = 6216 := by decide +kernel

theorem c977 : P.sumLeaves 20 977 1 = 21045 := by decide +kernel

theorem c978 : P.sumLeaves 20 978 1 = 45363 := by decide +kernel

theorem c979 : P.sumLeaves 20 979 1 = 62723 := by decide +kernel

theorem c980 : P.sumLeaves 20 980 1 = 10833 := by decide +kernel

theorem c981 : P.sumLeaves 20 981 1 = 52636 := by decide +kernel

theorem c982 : P.sumLeaves 20 982 1 = 55015 := by decide +kernel

theorem c983 : P.sumLeaves 20 983 1 = 79127 := by decide +kernel

theorem c984 : P.sumLeaves 20 984 1 = 7713 := by decide +kernel

theorem c985 : P.sumLeaves 20 985 1 = 27609 := by decide +kernel

theorem c986 : P.sumLeaves 20 986 1 = 46545 := by decide +kernel

theorem c987 : P.sumLeaves 20 987 1 = 66069 := by decide +kernel

theorem c988 : P.sumLeaves 20 988 1 = 13582 := by decide +kernel

theorem c989 : P.sumLeaves 20 989 1 = 55308 := by decide +kernel

theorem c990 : P.sumLeaves 20 990 1 = 56448 := by decide +kernel

theorem c991 : P.sumLeaves 20 991 1 = 83303 := by decide +kernel

theorem total : P.sumLeaves 20 976 16 = 689535 :=
  sumLeaves_of_chunks (cs := [(1, 6216), (1, 21045), (1, 45363), (1, 62723), (1, 10833), (1, 52636), (1, 55015), (1, 79127), (1, 7713), (1, 27609), (1, 46545), (1, 66069), (1, 13582), (1, 55308), (1, 56448), (1, 83303)])
    (.cons c976 (.cons c977 (.cons c978 (.cons c979 (.cons c980 (.cons c981 (.cons c982 (.cons c983 (.cons c984 (.cons c985 (.cons c986 (.cons c987 (.cons c988 (.cons c989 (.cons c990 (.cons c991 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K976

end RACert.S3N1.C0
