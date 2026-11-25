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

namespace K112

theorem c112 : P.sumLeaves 20 112 1 = 178 := by decide +kernel

theorem c113 : P.sumLeaves 20 113 1 = 238 := by decide +kernel

theorem c114 : P.sumLeaves 20 114 1 = 327 := by decide +kernel

theorem c115 : P.sumLeaves 20 115 1 = 475 := by decide +kernel

theorem c116 : P.sumLeaves 20 116 1 = 1713 := by decide +kernel

theorem c117 : P.sumLeaves 20 117 1 = 3472 := by decide +kernel

theorem c118 : P.sumLeaves 20 118 1 = 5844 := by decide +kernel

theorem c119 : P.sumLeaves 20 119 1 = 14033 := by decide +kernel

theorem c120 : P.sumLeaves 20 120 1 = 258 := by decide +kernel

theorem c121 : P.sumLeaves 20 121 1 = 418 := by decide +kernel

theorem c122 : P.sumLeaves 20 122 1 = 416 := by decide +kernel

theorem c123 : P.sumLeaves 20 123 1 = 606 := by decide +kernel

theorem c124 : P.sumLeaves 20 124 1 = 2739 := by decide +kernel

theorem c125 : P.sumLeaves 20 125 1 = 5677 := by decide +kernel

theorem c126 : P.sumLeaves 20 126 1 = 7499 := by decide +kernel

theorem c127 : P.sumLeaves 20 127 1 = 19174 := by decide +kernel

theorem total : P.sumLeaves 20 112 16 = 63067 :=
  sumLeaves_of_chunks (cs := [(1, 178), (1, 238), (1, 327), (1, 475), (1, 1713), (1, 3472), (1, 5844), (1, 14033), (1, 258), (1, 418), (1, 416), (1, 606), (1, 2739), (1, 5677), (1, 7499), (1, 19174)])
    (.cons c112 (.cons c113 (.cons c114 (.cons c115 (.cons c116 (.cons c117 (.cons c118 (.cons c119 (.cons c120 (.cons c121 (.cons c122 (.cons c123 (.cons c124 (.cons c125 (.cons c126 (.cons c127 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K112

end RACert.S3N1.C0
