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

namespace K256

theorem c256 : P.sumLeaves 20 256 1 = 251 := by decide +kernel

theorem c257 : P.sumLeaves 20 257 1 = 305 := by decide +kernel

theorem c258 : P.sumLeaves 20 258 1 = 572 := by decide +kernel

theorem c259 : P.sumLeaves 20 259 1 = 1034 := by decide +kernel

theorem c260 : P.sumLeaves 20 260 1 = 305 := by decide +kernel

theorem c261 : P.sumLeaves 20 261 1 = 644 := by decide +kernel

theorem c262 : P.sumLeaves 20 262 1 = 1034 := by decide +kernel

theorem c263 : P.sumLeaves 20 263 1 = 2716 := by decide +kernel

theorem c264 : P.sumLeaves 20 264 1 = 316 := by decide +kernel

theorem c265 : P.sumLeaves 20 265 1 = 387 := by decide +kernel

theorem c266 : P.sumLeaves 20 266 1 = 933 := by decide +kernel

theorem c267 : P.sumLeaves 20 267 1 = 1730 := by decide +kernel

theorem c268 : P.sumLeaves 20 268 1 = 387 := by decide +kernel

theorem c269 : P.sumLeaves 20 269 1 = 824 := by decide +kernel

theorem c270 : P.sumLeaves 20 270 1 = 1730 := by decide +kernel

theorem c271 : P.sumLeaves 20 271 1 = 4306 := by decide +kernel

theorem total : P.sumLeaves 20 256 16 = 17474 :=
  sumLeaves_of_chunks (cs := [(1, 251), (1, 305), (1, 572), (1, 1034), (1, 305), (1, 644), (1, 1034), (1, 2716), (1, 316), (1, 387), (1, 933), (1, 1730), (1, 387), (1, 824), (1, 1730), (1, 4306)])
    (.cons c256 (.cons c257 (.cons c258 (.cons c259 (.cons c260 (.cons c261 (.cons c262 (.cons c263 (.cons c264 (.cons c265 (.cons c266 (.cons c267 (.cons c268 (.cons c269 (.cons c270 (.cons c271 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K256

end RACert.S3N1.C0
