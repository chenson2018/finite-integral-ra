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

namespace K912

theorem c912 : P.sumLeaves 20 912 1 = 1941 := by decide +kernel

theorem c913 : P.sumLeaves 20 913 1 = 5810 := by decide +kernel

theorem c914 : P.sumLeaves 20 914 1 = 11242 := by decide +kernel

theorem c915 : P.sumLeaves 20 915 1 = 25811 := by decide +kernel

theorem c916 : P.sumLeaves 20 916 1 = 3720 := by decide +kernel

theorem c917 : P.sumLeaves 20 917 1 = 10876 := by decide +kernel

theorem c918 : P.sumLeaves 20 918 1 = 12069 := by decide +kernel

theorem c919 : P.sumLeaves 20 919 1 = 28845 := by decide +kernel

theorem c920 : P.sumLeaves 20 920 1 = 2508 := by decide +kernel

theorem c921 : P.sumLeaves 20 921 1 = 7505 := by decide +kernel

theorem c922 : P.sumLeaves 20 922 1 = 14446 := by decide +kernel

theorem c923 : P.sumLeaves 20 923 1 = 33683 := by decide +kernel

theorem c924 : P.sumLeaves 20 924 1 = 4884 := by decide +kernel

theorem c925 : P.sumLeaves 20 925 1 = 14058 := by decide +kernel

theorem c926 : P.sumLeaves 20 926 1 = 15557 := by decide +kernel

theorem c927 : P.sumLeaves 20 927 1 = 37903 := by decide +kernel

theorem total : P.sumLeaves 20 912 16 = 230858 :=
  sumLeaves_of_chunks (cs := [(1, 1941), (1, 5810), (1, 11242), (1, 25811), (1, 3720), (1, 10876), (1, 12069), (1, 28845), (1, 2508), (1, 7505), (1, 14446), (1, 33683), (1, 4884), (1, 14058), (1, 15557), (1, 37903)])
    (.cons c912 (.cons c913 (.cons c914 (.cons c915 (.cons c916 (.cons c917 (.cons c918 (.cons c919 (.cons c920 (.cons c921 (.cons c922 (.cons c923 (.cons c924 (.cons c925 (.cons c926 (.cons c927 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K912

end RACert.S3N1.C0
