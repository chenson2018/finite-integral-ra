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

namespace K320

theorem c320 : P.sumLeaves 20 320 1 = 585 := by decide +kernel

theorem c321 : P.sumLeaves 20 321 1 = 986 := by decide +kernel

theorem c322 : P.sumLeaves 20 322 1 = 5901 := by decide +kernel

theorem c323 : P.sumLeaves 20 323 1 = 6820 := by decide +kernel

theorem c324 : P.sumLeaves 20 324 1 = 986 := by decide +kernel

theorem c325 : P.sumLeaves 20 325 1 = 3431 := by decide +kernel

theorem c326 : P.sumLeaves 20 326 1 = 6820 := by decide +kernel

theorem c327 : P.sumLeaves 20 327 1 = 10091 := by decide +kernel

theorem c328 : P.sumLeaves 20 328 1 = 1176 := by decide +kernel

theorem c329 : P.sumLeaves 20 329 1 = 2317 := by decide +kernel

theorem c330 : P.sumLeaves 20 330 1 = 12522 := by decide +kernel

theorem c331 : P.sumLeaves 20 331 1 = 15042 := by decide +kernel

theorem c332 : P.sumLeaves 20 332 1 = 2317 := by decide +kernel

theorem c333 : P.sumLeaves 20 333 1 = 8738 := by decide +kernel

theorem c334 : P.sumLeaves 20 334 1 = 15042 := by decide +kernel

theorem c335 : P.sumLeaves 20 335 1 = 23038 := by decide +kernel

theorem total : P.sumLeaves 20 320 16 = 115812 :=
  sumLeaves_of_chunks (cs := [(1, 585), (1, 986), (1, 5901), (1, 6820), (1, 986), (1, 3431), (1, 6820), (1, 10091), (1, 1176), (1, 2317), (1, 12522), (1, 15042), (1, 2317), (1, 8738), (1, 15042), (1, 23038)])
    (.cons c320 (.cons c321 (.cons c322 (.cons c323 (.cons c324 (.cons c325 (.cons c326 (.cons c327 (.cons c328 (.cons c329 (.cons c330 (.cons c331 (.cons c332 (.cons c333 (.cons c334 (.cons c335 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K320

end RACert.S3N1.C0
