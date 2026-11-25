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

namespace K400

theorem c400 : P.sumLeaves 20 400 1 = 1216 := by decide +kernel

theorem c401 : P.sumLeaves 20 401 1 = 2134 := by decide +kernel

theorem c402 : P.sumLeaves 20 402 1 = 7443 := by decide +kernel

theorem c403 : P.sumLeaves 20 403 1 = 17105 := by decide +kernel

theorem c404 : P.sumLeaves 20 404 1 = 2186 := by decide +kernel

theorem c405 : P.sumLeaves 20 405 1 = 3731 := by decide +kernel

theorem c406 : P.sumLeaves 20 406 1 = 8102 := by decide +kernel

theorem c407 : P.sumLeaves 20 407 1 = 21414 := by decide +kernel

theorem c408 : P.sumLeaves 20 408 1 = 1676 := by decide +kernel

theorem c409 : P.sumLeaves 20 409 1 = 2906 := by decide +kernel

theorem c410 : P.sumLeaves 20 410 1 = 9802 := by decide +kernel

theorem c411 : P.sumLeaves 20 411 1 = 23063 := by decide +kernel

theorem c412 : P.sumLeaves 20 412 1 = 3299 := by decide +kernel

theorem c413 : P.sumLeaves 20 413 1 = 5195 := by decide +kernel

theorem c414 : P.sumLeaves 20 414 1 = 10689 := by decide +kernel

theorem c415 : P.sumLeaves 20 415 1 = 28985 := by decide +kernel

theorem total : P.sumLeaves 20 400 16 = 148946 :=
  sumLeaves_of_chunks (cs := [(1, 1216), (1, 2134), (1, 7443), (1, 17105), (1, 2186), (1, 3731), (1, 8102), (1, 21414), (1, 1676), (1, 2906), (1, 9802), (1, 23063), (1, 3299), (1, 5195), (1, 10689), (1, 28985)])
    (.cons c400 (.cons c401 (.cons c402 (.cons c403 (.cons c404 (.cons c405 (.cons c406 (.cons c407 (.cons c408 (.cons c409 (.cons c410 (.cons c411 (.cons c412 (.cons c413 (.cons c414 (.cons c415 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K400

end RACert.S3N1.C0
