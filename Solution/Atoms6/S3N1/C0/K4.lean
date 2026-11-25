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

namespace K64

theorem c64 : P.sumLeaves 20 64 1 = 225 := by decide +kernel

theorem c65 : P.sumLeaves 20 65 1 = 138 := by decide +kernel

theorem c66 : P.sumLeaves 20 66 1 = 229 := by decide +kernel

theorem c67 : P.sumLeaves 20 67 1 = 207 := by decide +kernel

theorem c68 : P.sumLeaves 20 68 1 = 138 := by decide +kernel

theorem c69 : P.sumLeaves 20 69 1 = 656 := by decide +kernel

theorem c70 : P.sumLeaves 20 70 1 = 207 := by decide +kernel

theorem c71 : P.sumLeaves 20 71 1 = 3446 := by decide +kernel

theorem c72 : P.sumLeaves 20 72 1 = 276 := by decide +kernel

theorem c73 : P.sumLeaves 20 73 1 = 192 := by decide +kernel

theorem c74 : P.sumLeaves 20 74 1 = 317 := by decide +kernel

theorem c75 : P.sumLeaves 20 75 1 = 261 := by decide +kernel

theorem c76 : P.sumLeaves 20 76 1 = 192 := by decide +kernel

theorem c77 : P.sumLeaves 20 77 1 = 1278 := by decide +kernel

theorem c78 : P.sumLeaves 20 78 1 = 261 := by decide +kernel

theorem c79 : P.sumLeaves 20 79 1 = 5475 := by decide +kernel

theorem total : P.sumLeaves 20 64 16 = 13498 :=
  sumLeaves_of_chunks (cs := [(1, 225), (1, 138), (1, 229), (1, 207), (1, 138), (1, 656), (1, 207), (1, 3446), (1, 276), (1, 192), (1, 317), (1, 261), (1, 192), (1, 1278), (1, 261), (1, 5475)])
    (.cons c64 (.cons c65 (.cons c66 (.cons c67 (.cons c68 (.cons c69 (.cons c70 (.cons c71 (.cons c72 (.cons c73 (.cons c74 (.cons c75 (.cons c76 (.cons c77 (.cons c78 (.cons c79 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K64

end RACert.S3N1.C0
