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

namespace K512

theorem c512 : P.sumLeaves 20 512 1 = 112 := by decide +kernel

theorem c513 : P.sumLeaves 20 513 1 = 88 := by decide +kernel

theorem c514 : P.sumLeaves 20 514 1 = 136 := by decide +kernel

theorem c515 : P.sumLeaves 20 515 1 = 120 := by decide +kernel

theorem c516 : P.sumLeaves 20 516 1 = 88 := by decide +kernel

theorem c517 : P.sumLeaves 20 517 1 = 234 := by decide +kernel

theorem c518 : P.sumLeaves 20 518 1 = 120 := by decide +kernel

theorem c519 : P.sumLeaves 20 519 1 = 1297 := by decide +kernel

theorem c520 : P.sumLeaves 20 520 1 = 120 := by decide +kernel

theorem c521 : P.sumLeaves 20 521 1 = 88 := by decide +kernel

theorem c522 : P.sumLeaves 20 522 1 = 164 := by decide +kernel

theorem c523 : P.sumLeaves 20 523 1 = 136 := by decide +kernel

theorem c524 : P.sumLeaves 20 524 1 = 88 := by decide +kernel

theorem c525 : P.sumLeaves 20 525 1 = 298 := by decide +kernel

theorem c526 : P.sumLeaves 20 526 1 = 136 := by decide +kernel

theorem c527 : P.sumLeaves 20 527 1 = 1765 := by decide +kernel

theorem total : P.sumLeaves 20 512 16 = 4990 :=
  sumLeaves_of_chunks (cs := [(1, 112), (1, 88), (1, 136), (1, 120), (1, 88), (1, 234), (1, 120), (1, 1297), (1, 120), (1, 88), (1, 164), (1, 136), (1, 88), (1, 298), (1, 136), (1, 1765)])
    (.cons c512 (.cons c513 (.cons c514 (.cons c515 (.cons c516 (.cons c517 (.cons c518 (.cons c519 (.cons c520 (.cons c521 (.cons c522 (.cons c523 (.cons c524 (.cons c525 (.cons c526 (.cons c527 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K512

end RACert.S3N1.C0
