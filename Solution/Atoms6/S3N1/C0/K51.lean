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

namespace K816

theorem c816 : P.sumLeaves 20 816 1 = 1941 := by decide +kernel

theorem c817 : P.sumLeaves 20 817 1 = 3720 := by decide +kernel

theorem c818 : P.sumLeaves 20 818 1 = 11242 := by decide +kernel

theorem c819 : P.sumLeaves 20 819 1 = 12069 := by decide +kernel

theorem c820 : P.sumLeaves 20 820 1 = 5810 := by decide +kernel

theorem c821 : P.sumLeaves 20 821 1 = 10876 := by decide +kernel

theorem c822 : P.sumLeaves 20 822 1 = 25811 := by decide +kernel

theorem c823 : P.sumLeaves 20 823 1 = 28845 := by decide +kernel

theorem c824 : P.sumLeaves 20 824 1 = 2508 := by decide +kernel

theorem c825 : P.sumLeaves 20 825 1 = 4884 := by decide +kernel

theorem c826 : P.sumLeaves 20 826 1 = 14446 := by decide +kernel

theorem c827 : P.sumLeaves 20 827 1 = 15557 := by decide +kernel

theorem c828 : P.sumLeaves 20 828 1 = 7505 := by decide +kernel

theorem c829 : P.sumLeaves 20 829 1 = 14058 := by decide +kernel

theorem c830 : P.sumLeaves 20 830 1 = 33683 := by decide +kernel

theorem c831 : P.sumLeaves 20 831 1 = 37903 := by decide +kernel

theorem total : P.sumLeaves 20 816 16 = 230858 :=
  sumLeaves_of_chunks (cs := [(1, 1941), (1, 3720), (1, 11242), (1, 12069), (1, 5810), (1, 10876), (1, 25811), (1, 28845), (1, 2508), (1, 4884), (1, 14446), (1, 15557), (1, 7505), (1, 14058), (1, 33683), (1, 37903)])
    (.cons c816 (.cons c817 (.cons c818 (.cons c819 (.cons c820 (.cons c821 (.cons c822 (.cons c823 (.cons c824 (.cons c825 (.cons c826 (.cons c827 (.cons c828 (.cons c829 (.cons c830 (.cons c831 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K816

end RACert.S3N1.C0
