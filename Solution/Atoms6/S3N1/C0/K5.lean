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

namespace K80

theorem c80 : P.sumLeaves 20 80 1 = 142 := by decide +kernel

theorem c81 : P.sumLeaves 20 81 1 = 146 := by decide +kernel

theorem c82 : P.sumLeaves 20 82 1 = 403 := by decide +kernel

theorem c83 : P.sumLeaves 20 83 1 = 309 := by decide +kernel

theorem c84 : P.sumLeaves 20 84 1 = 146 := by decide +kernel

theorem c85 : P.sumLeaves 20 85 1 = 2224 := by decide +kernel

theorem c86 : P.sumLeaves 20 86 1 = 309 := by decide +kernel

theorem c87 : P.sumLeaves 20 87 1 = 9002 := by decide +kernel

theorem c88 : P.sumLeaves 20 88 1 = 242 := by decide +kernel

theorem c89 : P.sumLeaves 20 89 1 = 270 := by decide +kernel

theorem c90 : P.sumLeaves 20 90 1 = 572 := by decide +kernel

theorem c91 : P.sumLeaves 20 91 1 = 406 := by decide +kernel

theorem c92 : P.sumLeaves 20 92 1 = 270 := by decide +kernel

theorem c93 : P.sumLeaves 20 93 1 = 3803 := by decide +kernel

theorem c94 : P.sumLeaves 20 94 1 = 406 := by decide +kernel

theorem c95 : P.sumLeaves 20 95 1 = 12359 := by decide +kernel

theorem total : P.sumLeaves 20 80 16 = 31009 :=
  sumLeaves_of_chunks (cs := [(1, 142), (1, 146), (1, 403), (1, 309), (1, 146), (1, 2224), (1, 309), (1, 9002), (1, 242), (1, 270), (1, 572), (1, 406), (1, 270), (1, 3803), (1, 406), (1, 12359)])
    (.cons c80 (.cons c81 (.cons c82 (.cons c83 (.cons c84 (.cons c85 (.cons c86 (.cons c87 (.cons c88 (.cons c89 (.cons c90 (.cons c91 (.cons c92 (.cons c93 (.cons c94 (.cons c95 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K80

end RACert.S3N1.C0
