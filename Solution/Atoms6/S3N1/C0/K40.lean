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

namespace K640

theorem c640 : P.sumLeaves 20 640 1 = 106 := by decide +kernel

theorem c641 : P.sumLeaves 20 641 1 = 297 := by decide +kernel

theorem c642 : P.sumLeaves 20 642 1 = 160 := by decide +kernel

theorem c643 : P.sumLeaves 20 643 1 = 527 := by decide +kernel

theorem c644 : P.sumLeaves 20 644 1 = 104 := by decide +kernel

theorem c645 : P.sumLeaves 20 645 1 = 341 := by decide +kernel

theorem c646 : P.sumLeaves 20 646 1 = 176 := by decide +kernel

theorem c647 : P.sumLeaves 20 647 1 = 2402 := by decide +kernel

theorem c648 : P.sumLeaves 20 648 1 = 106 := by decide +kernel

theorem c649 : P.sumLeaves 20 649 1 = 392 := by decide +kernel

theorem c650 : P.sumLeaves 20 650 1 = 188 := by decide +kernel

theorem c651 : P.sumLeaves 20 651 1 = 847 := by decide +kernel

theorem c652 : P.sumLeaves 20 652 1 = 104 := by decide +kernel

theorem c653 : P.sumLeaves 20 653 1 = 452 := by decide +kernel

theorem c654 : P.sumLeaves 20 654 1 = 208 := by decide +kernel

theorem c655 : P.sumLeaves 20 655 1 = 3442 := by decide +kernel

theorem total : P.sumLeaves 20 640 16 = 9852 :=
  sumLeaves_of_chunks (cs := [(1, 106), (1, 297), (1, 160), (1, 527), (1, 104), (1, 341), (1, 176), (1, 2402), (1, 106), (1, 392), (1, 188), (1, 847), (1, 104), (1, 452), (1, 208), (1, 3442)])
    (.cons c640 (.cons c641 (.cons c642 (.cons c643 (.cons c644 (.cons c645 (.cons c646 (.cons c647 (.cons c648 (.cons c649 (.cons c650 (.cons c651 (.cons c652 (.cons c653 (.cons c654 (.cons c655 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K640

end RACert.S3N1.C0
