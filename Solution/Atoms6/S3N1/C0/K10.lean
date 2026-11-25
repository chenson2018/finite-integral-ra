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

namespace K160

theorem c160 : P.sumLeaves 20 160 1 = 99 := by decide +kernel

theorem c161 : P.sumLeaves 20 161 1 = 68 := by decide +kernel

theorem c162 : P.sumLeaves 20 162 1 = 742 := by decide +kernel

theorem c163 : P.sumLeaves 20 163 1 = 1022 := by decide +kernel

theorem c164 : P.sumLeaves 20 164 1 = 68 := by decide +kernel

theorem c165 : P.sumLeaves 20 165 1 = 102 := by decide +kernel

theorem c166 : P.sumLeaves 20 166 1 = 1022 := by decide +kernel

theorem c167 : P.sumLeaves 20 167 1 = 4052 := by decide +kernel

theorem c168 : P.sumLeaves 20 168 1 = 99 := by decide +kernel

theorem c169 : P.sumLeaves 20 169 1 = 68 := by decide +kernel

theorem c170 : P.sumLeaves 20 170 1 = 1126 := by decide +kernel

theorem c171 : P.sumLeaves 20 171 1 = 1602 := by decide +kernel

theorem c172 : P.sumLeaves 20 172 1 = 68 := by decide +kernel

theorem c173 : P.sumLeaves 20 173 1 = 102 := by decide +kernel

theorem c174 : P.sumLeaves 20 174 1 = 1602 := by decide +kernel

theorem c175 : P.sumLeaves 20 175 1 = 6110 := by decide +kernel

theorem total : P.sumLeaves 20 160 16 = 17952 :=
  sumLeaves_of_chunks (cs := [(1, 99), (1, 68), (1, 742), (1, 1022), (1, 68), (1, 102), (1, 1022), (1, 4052), (1, 99), (1, 68), (1, 1126), (1, 1602), (1, 68), (1, 102), (1, 1602), (1, 6110)])
    (.cons c160 (.cons c161 (.cons c162 (.cons c163 (.cons c164 (.cons c165 (.cons c166 (.cons c167 (.cons c168 (.cons c169 (.cons c170 (.cons c171 (.cons c172 (.cons c173 (.cons c174 (.cons c175 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K160

end RACert.S3N1.C0
