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

namespace K128

theorem c128 : P.sumLeaves 20 128 1 = 70 := by decide +kernel

theorem c129 : P.sumLeaves 20 129 1 = 64 := by decide +kernel

theorem c130 : P.sumLeaves 20 130 1 = 136 := by decide +kernel

theorem c131 : P.sumLeaves 20 131 1 = 527 := by decide +kernel

theorem c132 : P.sumLeaves 20 132 1 = 64 := by decide +kernel

theorem c133 : P.sumLeaves 20 133 1 = 70 := by decide +kernel

theorem c134 : P.sumLeaves 20 134 1 = 176 := by decide +kernel

theorem c135 : P.sumLeaves 20 135 1 = 1846 := by decide +kernel

theorem c136 : P.sumLeaves 20 136 1 = 70 := by decide +kernel

theorem c137 : P.sumLeaves 20 137 1 = 64 := by decide +kernel

theorem c138 : P.sumLeaves 20 138 1 = 152 := by decide +kernel

theorem c139 : P.sumLeaves 20 139 1 = 847 := by decide +kernel

theorem c140 : P.sumLeaves 20 140 1 = 64 := by decide +kernel

theorem c141 : P.sumLeaves 20 141 1 = 70 := by decide +kernel

theorem c142 : P.sumLeaves 20 142 1 = 208 := by decide +kernel

theorem c143 : P.sumLeaves 20 143 1 = 2692 := by decide +kernel

theorem total : P.sumLeaves 20 128 16 = 7120 :=
  sumLeaves_of_chunks (cs := [(1, 70), (1, 64), (1, 136), (1, 527), (1, 64), (1, 70), (1, 176), (1, 1846), (1, 70), (1, 64), (1, 152), (1, 847), (1, 64), (1, 70), (1, 208), (1, 2692)])
    (.cons c128 (.cons c129 (.cons c130 (.cons c131 (.cons c132 (.cons c133 (.cons c134 (.cons c135 (.cons c136 (.cons c137 (.cons c138 (.cons c139 (.cons c140 (.cons c141 (.cons c142 (.cons c143 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K128

end RACert.S3N1.C0
