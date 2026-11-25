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

namespace K720

theorem c720 : P.sumLeaves 20 720 1 = 280 := by decide +kernel

theorem c721 : P.sumLeaves 20 721 1 = 2635 := by decide +kernel

theorem c722 : P.sumLeaves 20 722 1 = 450 := by decide +kernel

theorem c723 : P.sumLeaves 20 723 1 = 9165 := by decide +kernel

theorem c724 : P.sumLeaves 20 724 1 = 365 := by decide +kernel

theorem c725 : P.sumLeaves 20 725 1 = 9122 := by decide +kernel

theorem c726 : P.sumLeaves 20 726 1 = 652 := by decide +kernel

theorem c727 : P.sumLeaves 20 727 1 = 22154 := by decide +kernel

theorem c728 : P.sumLeaves 20 728 1 = 316 := by decide +kernel

theorem c729 : P.sumLeaves 20 729 1 = 3238 := by decide +kernel

theorem c730 : P.sumLeaves 20 730 1 = 450 := by decide +kernel

theorem c731 : P.sumLeaves 20 731 1 = 9333 := by decide +kernel

theorem c732 : P.sumLeaves 20 732 1 = 461 := by decide +kernel

theorem c733 : P.sumLeaves 20 733 1 = 9270 := by decide +kernel

theorem c734 : P.sumLeaves 20 734 1 = 652 := by decide +kernel

theorem c735 : P.sumLeaves 20 735 1 = 23293 := by decide +kernel

theorem total : P.sumLeaves 20 720 16 = 91836 :=
  sumLeaves_of_chunks (cs := [(1, 280), (1, 2635), (1, 450), (1, 9165), (1, 365), (1, 9122), (1, 652), (1, 22154), (1, 316), (1, 3238), (1, 450), (1, 9333), (1, 461), (1, 9270), (1, 652), (1, 23293)])
    (.cons c720 (.cons c721 (.cons c722 (.cons c723 (.cons c724 (.cons c725 (.cons c726 (.cons c727 (.cons c728 (.cons c729 (.cons c730 (.cons c731 (.cons c732 (.cons c733 (.cons c734 (.cons c735 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K720

end RACert.S3N1.C0
