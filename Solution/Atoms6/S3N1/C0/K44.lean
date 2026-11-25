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

namespace K704

theorem c704 : P.sumLeaves 20 704 1 = 164 := by decide +kernel

theorem c705 : P.sumLeaves 20 705 1 = 597 := by decide +kernel

theorem c706 : P.sumLeaves 20 706 1 = 210 := by decide +kernel

theorem c707 : P.sumLeaves 20 707 1 = 1637 := by decide +kernel

theorem c708 : P.sumLeaves 20 708 1 = 205 := by decide +kernel

theorem c709 : P.sumLeaves 20 709 1 = 1729 := by decide +kernel

theorem c710 : P.sumLeaves 20 710 1 = 276 := by decide +kernel

theorem c711 : P.sumLeaves 20 711 1 = 5771 := by decide +kernel

theorem c712 : P.sumLeaves 20 712 1 = 236 := by decide +kernel

theorem c713 : P.sumLeaves 20 713 1 = 1128 := by decide +kernel

theorem c714 : P.sumLeaves 20 714 1 = 266 := by decide +kernel

theorem c715 : P.sumLeaves 20 715 1 = 3045 := by decide +kernel

theorem c716 : P.sumLeaves 20 716 1 = 303 := by decide +kernel

theorem c717 : P.sumLeaves 20 717 1 = 3468 := by decide +kernel

theorem c718 : P.sumLeaves 20 718 1 = 366 := by decide +kernel

theorem c719 : P.sumLeaves 20 719 1 = 9770 := by decide +kernel

theorem total : P.sumLeaves 20 704 16 = 29171 :=
  sumLeaves_of_chunks (cs := [(1, 164), (1, 597), (1, 210), (1, 1637), (1, 205), (1, 1729), (1, 276), (1, 5771), (1, 236), (1, 1128), (1, 266), (1, 3045), (1, 303), (1, 3468), (1, 366), (1, 9770)])
    (.cons c704 (.cons c705 (.cons c706 (.cons c707 (.cons c708 (.cons c709 (.cons c710 (.cons c711 (.cons c712 (.cons c713 (.cons c714 (.cons c715 (.cons c716 (.cons c717 (.cons c718 (.cons c719 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K704

end RACert.S3N1.C0
