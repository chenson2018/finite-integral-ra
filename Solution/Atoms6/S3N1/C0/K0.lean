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

namespace K0

theorem c0 : P.sumLeaves 20 0 1 = 94 := by decide +kernel

theorem c1 : P.sumLeaves 20 1 1 = 66 := by decide +kernel

theorem c2 : P.sumLeaves 20 2 1 = 141 := by decide +kernel

theorem c3 : P.sumLeaves 20 3 1 = 155 := by decide +kernel

theorem c4 : P.sumLeaves 20 4 1 = 66 := by decide +kernel

theorem c5 : P.sumLeaves 20 5 1 = 80 := by decide +kernel

theorem c6 : P.sumLeaves 20 6 1 = 155 := by decide +kernel

theorem c7 : P.sumLeaves 20 7 1 = 1220 := by decide +kernel

theorem c8 : P.sumLeaves 20 8 1 = 102 := by decide +kernel

theorem c9 : P.sumLeaves 20 9 1 = 64 := by decide +kernel

theorem c10 : P.sumLeaves 20 10 1 = 132 := by decide +kernel

theorem c11 : P.sumLeaves 20 11 1 = 136 := by decide +kernel

theorem c12 : P.sumLeaves 20 12 1 = 64 := by decide +kernel

theorem c13 : P.sumLeaves 20 13 1 = 70 := by decide +kernel

theorem c14 : P.sumLeaves 20 14 1 = 136 := by decide +kernel

theorem c15 : P.sumLeaves 20 15 1 = 1513 := by decide +kernel

theorem total : P.sumLeaves 20 0 16 = 4194 :=
  sumLeaves_of_chunks (cs := [(1, 94), (1, 66), (1, 141), (1, 155), (1, 66), (1, 80), (1, 155), (1, 1220), (1, 102), (1, 64), (1, 132), (1, 136), (1, 64), (1, 70), (1, 136), (1, 1513)])
    (.cons c0 (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.cons c5 (.cons c6 (.cons c7 (.cons c8 (.cons c9 (.cons c10 (.cons c11 (.cons c12 (.cons c13 (.cons c14 (.cons c15 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K0

end RACert.S3N1.C0
