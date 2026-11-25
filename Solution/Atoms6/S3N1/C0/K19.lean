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

namespace K304

theorem c304 : P.sumLeaves 20 304 1 = 1216 := by decide +kernel

theorem c305 : P.sumLeaves 20 305 1 = 2186 := by decide +kernel

theorem c306 : P.sumLeaves 20 306 1 = 7443 := by decide +kernel

theorem c307 : P.sumLeaves 20 307 1 = 8102 := by decide +kernel

theorem c308 : P.sumLeaves 20 308 1 = 2134 := by decide +kernel

theorem c309 : P.sumLeaves 20 309 1 = 3731 := by decide +kernel

theorem c310 : P.sumLeaves 20 310 1 = 17105 := by decide +kernel

theorem c311 : P.sumLeaves 20 311 1 = 21414 := by decide +kernel

theorem c312 : P.sumLeaves 20 312 1 = 1676 := by decide +kernel

theorem c313 : P.sumLeaves 20 313 1 = 3299 := by decide +kernel

theorem c314 : P.sumLeaves 20 314 1 = 9802 := by decide +kernel

theorem c315 : P.sumLeaves 20 315 1 = 10689 := by decide +kernel

theorem c316 : P.sumLeaves 20 316 1 = 2906 := by decide +kernel

theorem c317 : P.sumLeaves 20 317 1 = 5195 := by decide +kernel

theorem c318 : P.sumLeaves 20 318 1 = 23063 := by decide +kernel

theorem c319 : P.sumLeaves 20 319 1 = 28985 := by decide +kernel

theorem total : P.sumLeaves 20 304 16 = 148946 :=
  sumLeaves_of_chunks (cs := [(1, 1216), (1, 2186), (1, 7443), (1, 8102), (1, 2134), (1, 3731), (1, 17105), (1, 21414), (1, 1676), (1, 3299), (1, 9802), (1, 10689), (1, 2906), (1, 5195), (1, 23063), (1, 28985)])
    (.cons c304 (.cons c305 (.cons c306 (.cons c307 (.cons c308 (.cons c309 (.cons c310 (.cons c311 (.cons c312 (.cons c313 (.cons c314 (.cons c315 (.cons c316 (.cons c317 (.cons c318 (.cons c319 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K304

end RACert.S3N1.C0
