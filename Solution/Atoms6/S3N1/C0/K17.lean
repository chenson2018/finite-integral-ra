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

namespace K272

theorem c272 : P.sumLeaves 20 272 1 = 1675 := by decide +kernel

theorem c273 : P.sumLeaves 20 273 1 = 1187 := by decide +kernel

theorem c274 : P.sumLeaves 20 274 1 = 3507 := by decide +kernel

theorem c275 : P.sumLeaves 20 275 1 = 5749 := by decide +kernel

theorem c276 : P.sumLeaves 20 276 1 = 1187 := by decide +kernel

theorem c277 : P.sumLeaves 20 277 1 = 3465 := by decide +kernel

theorem c278 : P.sumLeaves 20 278 1 = 5749 := by decide +kernel

theorem c279 : P.sumLeaves 20 279 1 = 18199 := by decide +kernel

theorem c280 : P.sumLeaves 20 280 1 = 2155 := by decide +kernel

theorem c281 : P.sumLeaves 20 281 1 = 1611 := by decide +kernel

theorem c282 : P.sumLeaves 20 282 1 = 3846 := by decide +kernel

theorem c283 : P.sumLeaves 20 283 1 = 6277 := by decide +kernel

theorem c284 : P.sumLeaves 20 284 1 = 1611 := by decide +kernel

theorem c285 : P.sumLeaves 20 285 1 = 3740 := by decide +kernel

theorem c286 : P.sumLeaves 20 286 1 = 6277 := by decide +kernel

theorem c287 : P.sumLeaves 20 287 1 = 21191 := by decide +kernel

theorem total : P.sumLeaves 20 272 16 = 87426 :=
  sumLeaves_of_chunks (cs := [(1, 1675), (1, 1187), (1, 3507), (1, 5749), (1, 1187), (1, 3465), (1, 5749), (1, 18199), (1, 2155), (1, 1611), (1, 3846), (1, 6277), (1, 1611), (1, 3740), (1, 6277), (1, 21191)])
    (.cons c272 (.cons c273 (.cons c274 (.cons c275 (.cons c276 (.cons c277 (.cons c278 (.cons c279 (.cons c280 (.cons c281 (.cons c282 (.cons c283 (.cons c284 (.cons c285 (.cons c286 (.cons c287 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K272

end RACert.S3N1.C0
