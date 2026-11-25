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

namespace K672

theorem c672 : P.sumLeaves 20 672 1 = 566 := by decide +kernel

theorem c673 : P.sumLeaves 20 673 1 = 510 := by decide +kernel

theorem c674 : P.sumLeaves 20 674 1 = 1228 := by decide +kernel

theorem c675 : P.sumLeaves 20 675 1 = 1467 := by decide +kernel

theorem c676 : P.sumLeaves 20 676 1 = 510 := by decide +kernel

theorem c677 : P.sumLeaves 20 677 1 = 1156 := by decide +kernel

theorem c678 : P.sumLeaves 20 678 1 = 1467 := by decide +kernel

theorem c679 : P.sumLeaves 20 679 1 = 7579 := by decide +kernel

theorem c680 : P.sumLeaves 20 680 1 = 778 := by decide +kernel

theorem c681 : P.sumLeaves 20 681 1 = 732 := by decide +kernel

theorem c682 : P.sumLeaves 20 682 1 = 2299 := by decide +kernel

theorem c683 : P.sumLeaves 20 683 1 = 3088 := by decide +kernel

theorem c684 : P.sumLeaves 20 684 1 = 732 := by decide +kernel

theorem c685 : P.sumLeaves 20 685 1 = 1669 := by decide +kernel

theorem c686 : P.sumLeaves 20 686 1 = 3088 := by decide +kernel

theorem c687 : P.sumLeaves 20 687 1 = 14467 := by decide +kernel

theorem total : P.sumLeaves 20 672 16 = 41336 :=
  sumLeaves_of_chunks (cs := [(1, 566), (1, 510), (1, 1228), (1, 1467), (1, 510), (1, 1156), (1, 1467), (1, 7579), (1, 778), (1, 732), (1, 2299), (1, 3088), (1, 732), (1, 1669), (1, 3088), (1, 14467)])
    (.cons c672 (.cons c673 (.cons c674 (.cons c675 (.cons c676 (.cons c677 (.cons c678 (.cons c679 (.cons c680 (.cons c681 (.cons c682 (.cons c683 (.cons c684 (.cons c685 (.cons c686 (.cons c687 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K672

end RACert.S3N1.C0
