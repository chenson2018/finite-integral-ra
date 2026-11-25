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

namespace K48

theorem c48 : P.sumLeaves 20 48 1 = 66 := by decide +kernel

theorem c49 : P.sumLeaves 20 49 1 = 64 := by decide +kernel

theorem c50 : P.sumLeaves 20 50 1 = 210 := by decide +kernel

theorem c51 : P.sumLeaves 20 51 1 = 326 := by decide +kernel

theorem c52 : P.sumLeaves 20 52 1 = 66 := by decide +kernel

theorem c53 : P.sumLeaves 20 53 1 = 70 := by decide +kernel

theorem c54 : P.sumLeaves 20 54 1 = 2134 := by decide +kernel

theorem c55 : P.sumLeaves 20 55 1 = 5551 := by decide +kernel

theorem c56 : P.sumLeaves 20 56 1 = 66 := by decide +kernel

theorem c57 : P.sumLeaves 20 57 1 = 64 := by decide +kernel

theorem c58 : P.sumLeaves 20 58 1 = 248 := by decide +kernel

theorem c59 : P.sumLeaves 20 59 1 = 384 := by decide +kernel

theorem c60 : P.sumLeaves 20 60 1 = 66 := by decide +kernel

theorem c61 : P.sumLeaves 20 61 1 = 70 := by decide +kernel

theorem c62 : P.sumLeaves 20 62 1 = 2417 := by decide +kernel

theorem c63 : P.sumLeaves 20 63 1 = 6242 := by decide +kernel

theorem total : P.sumLeaves 20 48 16 = 18044 :=
  sumLeaves_of_chunks (cs := [(1, 66), (1, 64), (1, 210), (1, 326), (1, 66), (1, 70), (1, 2134), (1, 5551), (1, 66), (1, 64), (1, 248), (1, 384), (1, 66), (1, 70), (1, 2417), (1, 6242)])
    (.cons c48 (.cons c49 (.cons c50 (.cons c51 (.cons c52 (.cons c53 (.cons c54 (.cons c55 (.cons c56 (.cons c57 (.cons c58 (.cons c59 (.cons c60 (.cons c61 (.cons c62 (.cons c63 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K48

end RACert.S3N1.C0
