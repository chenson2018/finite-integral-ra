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

namespace K240

theorem c240 : P.sumLeaves 20 240 1 = 2542 := by decide +kernel

theorem c241 : P.sumLeaves 20 241 1 = 4601 := by decide +kernel

theorem c242 : P.sumLeaves 20 242 1 = 11204 := by decide +kernel

theorem c243 : P.sumLeaves 20 243 1 = 16606 := by decide +kernel

theorem c244 : P.sumLeaves 20 244 1 = 4601 := by decide +kernel

theorem c245 : P.sumLeaves 20 245 1 = 11100 := by decide +kernel

theorem c246 : P.sumLeaves 20 246 1 = 16606 := by decide +kernel

theorem c247 : P.sumLeaves 20 247 1 = 43528 := by decide +kernel

theorem c248 : P.sumLeaves 20 248 1 = 5291 := by decide +kernel

theorem c249 : P.sumLeaves 20 249 1 = 8494 := by decide +kernel

theorem c250 : P.sumLeaves 20 250 1 = 13946 := by decide +kernel

theorem c251 : P.sumLeaves 20 251 1 = 20995 := by decide +kernel

theorem c252 : P.sumLeaves 20 252 1 = 8494 := by decide +kernel

theorem c253 : P.sumLeaves 20 253 1 = 18466 := by decide +kernel

theorem c254 : P.sumLeaves 20 254 1 = 20995 := by decide +kernel

theorem c255 : P.sumLeaves 20 255 1 = 56551 := by decide +kernel

theorem total : P.sumLeaves 20 240 16 = 264020 :=
  sumLeaves_of_chunks (cs := [(1, 2542), (1, 4601), (1, 11204), (1, 16606), (1, 4601), (1, 11100), (1, 16606), (1, 43528), (1, 5291), (1, 8494), (1, 13946), (1, 20995), (1, 8494), (1, 18466), (1, 20995), (1, 56551)])
    (.cons c240 (.cons c241 (.cons c242 (.cons c243 (.cons c244 (.cons c245 (.cons c246 (.cons c247 (.cons c248 (.cons c249 (.cons c250 (.cons c251 (.cons c252 (.cons c253 (.cons c254 (.cons c255 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K240

end RACert.S3N1.C0
