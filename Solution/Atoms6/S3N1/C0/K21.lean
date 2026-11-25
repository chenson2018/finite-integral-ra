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

namespace K336

theorem c336 : P.sumLeaves 20 336 1 = 3269 := by decide +kernel

theorem c337 : P.sumLeaves 20 337 1 = 7377 := by decide +kernel

theorem c338 : P.sumLeaves 20 338 1 = 35459 := by decide +kernel

theorem c339 : P.sumLeaves 20 339 1 = 45683 := by decide +kernel

theorem c340 : P.sumLeaves 20 340 1 = 7377 := by decide +kernel

theorem c341 : P.sumLeaves 20 341 1 = 35716 := by decide +kernel

theorem c342 : P.sumLeaves 20 342 1 = 45683 := by decide +kernel

theorem c343 : P.sumLeaves 20 343 1 = 66872 := by decide +kernel

theorem c344 : P.sumLeaves 20 344 1 = 3828 := by decide +kernel

theorem c345 : P.sumLeaves 20 345 1 = 8875 := by decide +kernel

theorem c346 : P.sumLeaves 20 346 1 = 35712 := by decide +kernel

theorem c347 : P.sumLeaves 20 347 1 = 46437 := by decide +kernel

theorem c348 : P.sumLeaves 20 348 1 = 8875 := by decide +kernel

theorem c349 : P.sumLeaves 20 349 1 = 36935 := by decide +kernel

theorem c350 : P.sumLeaves 20 350 1 = 46437 := by decide +kernel

theorem c351 : P.sumLeaves 20 351 1 = 69785 := by decide +kernel

theorem total : P.sumLeaves 20 336 16 = 504320 :=
  sumLeaves_of_chunks (cs := [(1, 3269), (1, 7377), (1, 35459), (1, 45683), (1, 7377), (1, 35716), (1, 45683), (1, 66872), (1, 3828), (1, 8875), (1, 35712), (1, 46437), (1, 8875), (1, 36935), (1, 46437), (1, 69785)])
    (.cons c336 (.cons c337 (.cons c338 (.cons c339 (.cons c340 (.cons c341 (.cons c342 (.cons c343 (.cons c344 (.cons c345 (.cons c346 (.cons c347 (.cons c348 (.cons c349 (.cons c350 (.cons c351 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K336

end RACert.S3N1.C0
