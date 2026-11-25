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

namespace K528

theorem c528 : P.sumLeaves 20 528 1 = 424 := by decide +kernel

theorem c529 : P.sumLeaves 20 529 1 = 170 := by decide +kernel

theorem c530 : P.sumLeaves 20 530 1 = 418 := by decide +kernel

theorem c531 : P.sumLeaves 20 531 1 = 346 := by decide +kernel

theorem c532 : P.sumLeaves 20 532 1 = 170 := by decide +kernel

theorem c533 : P.sumLeaves 20 533 1 = 1367 := by decide +kernel

theorem c534 : P.sumLeaves 20 534 1 = 346 := by decide +kernel

theorem c535 : P.sumLeaves 20 535 1 = 6005 := by decide +kernel

theorem c536 : P.sumLeaves 20 536 1 = 559 := by decide +kernel

theorem c537 : P.sumLeaves 20 537 1 = 250 := by decide +kernel

theorem c538 : P.sumLeaves 20 538 1 = 458 := by decide +kernel

theorem c539 : P.sumLeaves 20 539 1 = 394 := by decide +kernel

theorem c540 : P.sumLeaves 20 540 1 = 250 := by decide +kernel

theorem c541 : P.sumLeaves 20 541 1 = 1486 := by decide +kernel

theorem c542 : P.sumLeaves 20 542 1 = 394 := by decide +kernel

theorem c543 : P.sumLeaves 20 543 1 = 7089 := by decide +kernel

theorem total : P.sumLeaves 20 528 16 = 20126 :=
  sumLeaves_of_chunks (cs := [(1, 424), (1, 170), (1, 418), (1, 346), (1, 170), (1, 1367), (1, 346), (1, 6005), (1, 559), (1, 250), (1, 458), (1, 394), (1, 250), (1, 1486), (1, 394), (1, 7089)])
    (.cons c528 (.cons c529 (.cons c530 (.cons c531 (.cons c532 (.cons c533 (.cons c534 (.cons c535 (.cons c536 (.cons c537 (.cons c538 (.cons c539 (.cons c540 (.cons c541 (.cons c542 (.cons c543 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K528

end RACert.S3N1.C0
