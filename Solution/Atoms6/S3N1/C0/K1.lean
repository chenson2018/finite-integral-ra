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

namespace K16

theorem c16 : P.sumLeaves 20 16 1 = 165 := by decide +kernel

theorem c17 : P.sumLeaves 20 17 1 = 68 := by decide +kernel

theorem c18 : P.sumLeaves 20 18 1 = 286 := by decide +kernel

theorem c19 : P.sumLeaves 20 19 1 = 288 := by decide +kernel

theorem c20 : P.sumLeaves 20 20 1 = 68 := by decide +kernel

theorem c21 : P.sumLeaves 20 21 1 = 100 := by decide +kernel

theorem c22 : P.sumLeaves 20 22 1 = 288 := by decide +kernel

theorem c23 : P.sumLeaves 20 23 1 = 3437 := by decide +kernel

theorem c24 : P.sumLeaves 20 24 1 = 179 := by decide +kernel

theorem c25 : P.sumLeaves 20 25 1 = 74 := by decide +kernel

theorem c26 : P.sumLeaves 20 26 1 = 326 := by decide +kernel

theorem c27 : P.sumLeaves 20 27 1 = 336 := by decide +kernel

theorem c28 : P.sumLeaves 20 28 1 = 74 := by decide +kernel

theorem c29 : P.sumLeaves 20 29 1 = 100 := by decide +kernel

theorem c30 : P.sumLeaves 20 30 1 = 336 := by decide +kernel

theorem c31 : P.sumLeaves 20 31 1 = 4025 := by decide +kernel

theorem total : P.sumLeaves 20 16 16 = 10150 :=
  sumLeaves_of_chunks (cs := [(1, 165), (1, 68), (1, 286), (1, 288), (1, 68), (1, 100), (1, 288), (1, 3437), (1, 179), (1, 74), (1, 326), (1, 336), (1, 74), (1, 100), (1, 336), (1, 4025)])
    (.cons c16 (.cons c17 (.cons c18 (.cons c19 (.cons c20 (.cons c21 (.cons c22 (.cons c23 (.cons c24 (.cons c25 (.cons c26 (.cons c27 (.cons c28 (.cons c29 (.cons c30 (.cons c31 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K16

end RACert.S3N1.C0
