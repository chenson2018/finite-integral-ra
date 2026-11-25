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

namespace K544

theorem c544 : P.sumLeaves 20 544 1 = 106 := by decide +kernel

theorem c545 : P.sumLeaves 20 545 1 = 104 := by decide +kernel

theorem c546 : P.sumLeaves 20 546 1 = 160 := by decide +kernel

theorem c547 : P.sumLeaves 20 547 1 = 176 := by decide +kernel

theorem c548 : P.sumLeaves 20 548 1 = 297 := by decide +kernel

theorem c549 : P.sumLeaves 20 549 1 = 341 := by decide +kernel

theorem c550 : P.sumLeaves 20 550 1 = 527 := by decide +kernel

theorem c551 : P.sumLeaves 20 551 1 = 2402 := by decide +kernel

theorem c552 : P.sumLeaves 20 552 1 = 106 := by decide +kernel

theorem c553 : P.sumLeaves 20 553 1 = 104 := by decide +kernel

theorem c554 : P.sumLeaves 20 554 1 = 188 := by decide +kernel

theorem c555 : P.sumLeaves 20 555 1 = 208 := by decide +kernel

theorem c556 : P.sumLeaves 20 556 1 = 392 := by decide +kernel

theorem c557 : P.sumLeaves 20 557 1 = 452 := by decide +kernel

theorem c558 : P.sumLeaves 20 558 1 = 847 := by decide +kernel

theorem c559 : P.sumLeaves 20 559 1 = 3442 := by decide +kernel

theorem total : P.sumLeaves 20 544 16 = 9852 :=
  sumLeaves_of_chunks (cs := [(1, 106), (1, 104), (1, 160), (1, 176), (1, 297), (1, 341), (1, 527), (1, 2402), (1, 106), (1, 104), (1, 188), (1, 208), (1, 392), (1, 452), (1, 847), (1, 3442)])
    (.cons c544 (.cons c545 (.cons c546 (.cons c547 (.cons c548 (.cons c549 (.cons c550 (.cons c551 (.cons c552 (.cons c553 (.cons c554 (.cons c555 (.cons c556 (.cons c557 (.cons c558 (.cons c559 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K544

end RACert.S3N1.C0
