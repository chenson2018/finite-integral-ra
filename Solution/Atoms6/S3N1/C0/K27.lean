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

namespace K432

theorem c432 : P.sumLeaves 20 432 1 = 2537 := by decide +kernel

theorem c433 : P.sumLeaves 20 433 1 = 3266 := by decide +kernel

theorem c434 : P.sumLeaves 20 434 1 = 31440 := by decide +kernel

theorem c435 : P.sumLeaves 20 435 1 = 35863 := by decide +kernel

theorem c436 : P.sumLeaves 20 436 1 = 3266 := by decide +kernel

theorem c437 : P.sumLeaves 20 437 1 = 10202 := by decide +kernel

theorem c438 : P.sumLeaves 20 438 1 = 35863 := by decide +kernel

theorem c439 : P.sumLeaves 20 439 1 = 46142 := by decide +kernel

theorem c440 : P.sumLeaves 20 440 1 = 3075 := by decide +kernel

theorem c441 : P.sumLeaves 20 441 1 = 4179 := by decide +kernel

theorem c442 : P.sumLeaves 20 442 1 = 32379 := by decide +kernel

theorem c443 : P.sumLeaves 20 443 1 = 36922 := by decide +kernel

theorem c444 : P.sumLeaves 20 444 1 = 4179 := by decide +kernel

theorem c445 : P.sumLeaves 20 445 1 = 10450 := by decide +kernel

theorem c446 : P.sumLeaves 20 446 1 = 36922 := by decide +kernel

theorem c447 : P.sumLeaves 20 447 1 = 48111 := by decide +kernel

theorem total : P.sumLeaves 20 432 16 = 344796 :=
  sumLeaves_of_chunks (cs := [(1, 2537), (1, 3266), (1, 31440), (1, 35863), (1, 3266), (1, 10202), (1, 35863), (1, 46142), (1, 3075), (1, 4179), (1, 32379), (1, 36922), (1, 4179), (1, 10450), (1, 36922), (1, 48111)])
    (.cons c432 (.cons c433 (.cons c434 (.cons c435 (.cons c436 (.cons c437 (.cons c438 (.cons c439 (.cons c440 (.cons c441 (.cons c442 (.cons c443 (.cons c444 (.cons c445 (.cons c446 (.cons c447 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K432

end RACert.S3N1.C0
