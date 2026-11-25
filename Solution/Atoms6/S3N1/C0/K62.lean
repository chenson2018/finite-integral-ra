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

namespace K992

theorem c992 : P.sumLeaves 20 992 1 = 3712 := by decide +kernel

theorem c993 : P.sumLeaves 20 993 1 = 5032 := by decide +kernel

theorem c994 : P.sumLeaves 20 994 1 = 15096 := by decide +kernel

theorem c995 : P.sumLeaves 20 995 1 = 17182 := by decide +kernel

theorem c996 : P.sumLeaves 20 996 1 = 5032 := by decide +kernel

theorem c997 : P.sumLeaves 20 997 1 = 9281 := by decide +kernel

theorem c998 : P.sumLeaves 20 998 1 = 17182 := by decide +kernel

theorem c999 : P.sumLeaves 20 999 1 = 20566 := by decide +kernel

theorem c1000 : P.sumLeaves 20 1000 1 = 13738 := by decide +kernel

theorem c1001 : P.sumLeaves 20 1001 1 = 16891 := by decide +kernel

theorem c1002 : P.sumLeaves 20 1002 1 = 32492 := by decide +kernel

theorem c1003 : P.sumLeaves 20 1003 1 = 36330 := by decide +kernel

theorem c1004 : P.sumLeaves 20 1004 1 = 16891 := by decide +kernel

theorem c1005 : P.sumLeaves 20 1005 1 = 31269 := by decide +kernel

theorem c1006 : P.sumLeaves 20 1006 1 = 36330 := by decide +kernel

theorem c1007 : P.sumLeaves 20 1007 1 = 43291 := by decide +kernel

theorem total : P.sumLeaves 20 992 16 = 320315 :=
  sumLeaves_of_chunks (cs := [(1, 3712), (1, 5032), (1, 15096), (1, 17182), (1, 5032), (1, 9281), (1, 17182), (1, 20566), (1, 13738), (1, 16891), (1, 32492), (1, 36330), (1, 16891), (1, 31269), (1, 36330), (1, 43291)])
    (.cons c992 (.cons c993 (.cons c994 (.cons c995 (.cons c996 (.cons c997 (.cons c998 (.cons c999 (.cons c1000 (.cons c1001 (.cons c1002 (.cons c1003 (.cons c1004 (.cons c1005 (.cons c1006 (.cons c1007 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K992

end RACert.S3N1.C0
