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

namespace K32

theorem c32 : P.sumLeaves 20 32 1 = 70 := by decide +kernel

theorem c33 : P.sumLeaves 20 33 1 = 64 := by decide +kernel

theorem c34 : P.sumLeaves 20 34 1 = 136 := by decide +kernel

theorem c35 : P.sumLeaves 20 35 1 = 176 := by decide +kernel

theorem c36 : P.sumLeaves 20 36 1 = 64 := by decide +kernel

theorem c37 : P.sumLeaves 20 37 1 = 70 := by decide +kernel

theorem c38 : P.sumLeaves 20 38 1 = 527 := by decide +kernel

theorem c39 : P.sumLeaves 20 39 1 = 1846 := by decide +kernel

theorem c40 : P.sumLeaves 20 40 1 = 70 := by decide +kernel

theorem c41 : P.sumLeaves 20 41 1 = 64 := by decide +kernel

theorem c42 : P.sumLeaves 20 42 1 = 152 := by decide +kernel

theorem c43 : P.sumLeaves 20 43 1 = 208 := by decide +kernel

theorem c44 : P.sumLeaves 20 44 1 = 64 := by decide +kernel

theorem c45 : P.sumLeaves 20 45 1 = 70 := by decide +kernel

theorem c46 : P.sumLeaves 20 46 1 = 847 := by decide +kernel

theorem c47 : P.sumLeaves 20 47 1 = 2692 := by decide +kernel

theorem total : P.sumLeaves 20 32 16 = 7120 :=
  sumLeaves_of_chunks (cs := [(1, 70), (1, 64), (1, 136), (1, 176), (1, 64), (1, 70), (1, 527), (1, 1846), (1, 70), (1, 64), (1, 152), (1, 208), (1, 64), (1, 70), (1, 847), (1, 2692)])
    (.cons c32 (.cons c33 (.cons c34 (.cons c35 (.cons c36 (.cons c37 (.cons c38 (.cons c39 (.cons c40 (.cons c41 (.cons c42 (.cons c43 (.cons c44 (.cons c45 (.cons c46 (.cons c47 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K32

end RACert.S3N1.C0
