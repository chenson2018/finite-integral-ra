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

namespace K224

theorem c224 : P.sumLeaves 20 224 1 = 664 := by decide +kernel

theorem c225 : P.sumLeaves 20 225 1 = 836 := by decide +kernel

theorem c226 : P.sumLeaves 20 226 1 = 1362 := by decide +kernel

theorem c227 : P.sumLeaves 20 227 1 = 2129 := by decide +kernel

theorem c228 : P.sumLeaves 20 228 1 = 836 := by decide +kernel

theorem c229 : P.sumLeaves 20 229 1 = 1605 := by decide +kernel

theorem c230 : P.sumLeaves 20 230 1 = 2129 := by decide +kernel

theorem c231 : P.sumLeaves 20 231 1 = 9067 := by decide +kernel

theorem c232 : P.sumLeaves 20 232 1 = 1698 := by decide +kernel

theorem c233 : P.sumLeaves 20 233 1 = 2400 := by decide +kernel

theorem c234 : P.sumLeaves 20 234 1 = 3770 := by decide +kernel

theorem c235 : P.sumLeaves 20 235 1 = 6258 := by decide +kernel

theorem c236 : P.sumLeaves 20 236 1 = 2400 := by decide +kernel

theorem c237 : P.sumLeaves 20 237 1 = 5676 := by decide +kernel

theorem c238 : P.sumLeaves 20 238 1 = 6258 := by decide +kernel

theorem c239 : P.sumLeaves 20 239 1 = 21320 := by decide +kernel

theorem total : P.sumLeaves 20 224 16 = 68408 :=
  sumLeaves_of_chunks (cs := [(1, 664), (1, 836), (1, 1362), (1, 2129), (1, 836), (1, 1605), (1, 2129), (1, 9067), (1, 1698), (1, 2400), (1, 3770), (1, 6258), (1, 2400), (1, 5676), (1, 6258), (1, 21320)])
    (.cons c224 (.cons c225 (.cons c226 (.cons c227 (.cons c228 (.cons c229 (.cons c230 (.cons c231 (.cons c232 (.cons c233 (.cons c234 (.cons c235 (.cons c236 (.cons c237 (.cons c238 (.cons c239 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K224

end RACert.S3N1.C0
