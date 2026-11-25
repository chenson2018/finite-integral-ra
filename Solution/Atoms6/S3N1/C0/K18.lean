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

namespace K288

theorem c288 : P.sumLeaves 20 288 1 = 260 := by decide +kernel

theorem c289 : P.sumLeaves 20 289 1 = 482 := by decide +kernel

theorem c290 : P.sumLeaves 20 290 1 = 915 := by decide +kernel

theorem c291 : P.sumLeaves 20 291 1 = 1744 := by decide +kernel

theorem c292 : P.sumLeaves 20 292 1 = 418 := by decide +kernel

theorem c293 : P.sumLeaves 20 293 1 = 1029 := by decide +kernel

theorem c294 : P.sumLeaves 20 294 1 = 1770 := by decide +kernel

theorem c295 : P.sumLeaves 20 295 1 = 4187 := by decide +kernel

theorem c296 : P.sumLeaves 20 296 1 = 338 := by decide +kernel

theorem c297 : P.sumLeaves 20 297 1 = 616 := by decide +kernel

theorem c298 : P.sumLeaves 20 298 1 = 1395 := by decide +kernel

theorem c299 : P.sumLeaves 20 299 1 = 2704 := by decide +kernel

theorem c300 : P.sumLeaves 20 300 1 = 532 := by decide +kernel

theorem c301 : P.sumLeaves 20 301 1 = 1314 := by decide +kernel

theorem c302 : P.sumLeaves 20 302 1 = 2727 := by decide +kernel

theorem c303 : P.sumLeaves 20 303 1 = 6449 := by decide +kernel

theorem total : P.sumLeaves 20 288 16 = 26880 :=
  sumLeaves_of_chunks (cs := [(1, 260), (1, 482), (1, 915), (1, 1744), (1, 418), (1, 1029), (1, 1770), (1, 4187), (1, 338), (1, 616), (1, 1395), (1, 2704), (1, 532), (1, 1314), (1, 2727), (1, 6449)])
    (.cons c288 (.cons c289 (.cons c290 (.cons c291 (.cons c292 (.cons c293 (.cons c294 (.cons c295 (.cons c296 (.cons c297 (.cons c298 (.cons c299 (.cons c300 (.cons c301 (.cons c302 (.cons c303 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K288

end RACert.S3N1.C0
