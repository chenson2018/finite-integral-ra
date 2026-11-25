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

namespace K192

theorem c192 : P.sumLeaves 20 192 1 = 196 := by decide +kernel

theorem c193 : P.sumLeaves 20 193 1 = 492 := by decide +kernel

theorem c194 : P.sumLeaves 20 194 1 = 195 := by decide +kernel

theorem c195 : P.sumLeaves 20 195 1 = 1259 := by decide +kernel

theorem c196 : P.sumLeaves 20 196 1 = 174 := by decide +kernel

theorem c197 : P.sumLeaves 20 197 1 = 882 := by decide +kernel

theorem c198 : P.sumLeaves 20 198 1 = 257 := by decide +kernel

theorem c199 : P.sumLeaves 20 199 1 = 4784 := by decide +kernel

theorem c200 : P.sumLeaves 20 200 1 = 283 := by decide +kernel

theorem c201 : P.sumLeaves 20 201 1 = 981 := by decide +kernel

theorem c202 : P.sumLeaves 20 202 1 = 245 := by decide +kernel

theorem c203 : P.sumLeaves 20 203 1 = 2269 := by decide +kernel

theorem c204 : P.sumLeaves 20 204 1 = 264 := by decide +kernel

theorem c205 : P.sumLeaves 20 205 1 = 1792 := by decide +kernel

theorem c206 : P.sumLeaves 20 206 1 = 339 := by decide +kernel

theorem c207 : P.sumLeaves 20 207 1 = 7997 := by decide +kernel

theorem total : P.sumLeaves 20 192 16 = 22409 :=
  sumLeaves_of_chunks (cs := [(1, 196), (1, 492), (1, 195), (1, 1259), (1, 174), (1, 882), (1, 257), (1, 4784), (1, 283), (1, 981), (1, 245), (1, 2269), (1, 264), (1, 1792), (1, 339), (1, 7997)])
    (.cons c192 (.cons c193 (.cons c194 (.cons c195 (.cons c196 (.cons c197 (.cons c198 (.cons c199 (.cons c200 (.cons c201 (.cons c202 (.cons c203 (.cons c204 (.cons c205 (.cons c206 (.cons c207 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K192

end RACert.S3N1.C0
