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

namespace K144

theorem c144 : P.sumLeaves 20 144 1 = 66 := by decide +kernel

theorem c145 : P.sumLeaves 20 145 1 = 66 := by decide +kernel

theorem c146 : P.sumLeaves 20 146 1 = 210 := by decide +kernel

theorem c147 : P.sumLeaves 20 147 1 = 2134 := by decide +kernel

theorem c148 : P.sumLeaves 20 148 1 = 64 := by decide +kernel

theorem c149 : P.sumLeaves 20 149 1 = 70 := by decide +kernel

theorem c150 : P.sumLeaves 20 150 1 = 326 := by decide +kernel

theorem c151 : P.sumLeaves 20 151 1 = 5551 := by decide +kernel

theorem c152 : P.sumLeaves 20 152 1 = 66 := by decide +kernel

theorem c153 : P.sumLeaves 20 153 1 = 66 := by decide +kernel

theorem c154 : P.sumLeaves 20 154 1 = 248 := by decide +kernel

theorem c155 : P.sumLeaves 20 155 1 = 2417 := by decide +kernel

theorem c156 : P.sumLeaves 20 156 1 = 64 := by decide +kernel

theorem c157 : P.sumLeaves 20 157 1 = 70 := by decide +kernel

theorem c158 : P.sumLeaves 20 158 1 = 384 := by decide +kernel

theorem c159 : P.sumLeaves 20 159 1 = 6242 := by decide +kernel

theorem total : P.sumLeaves 20 144 16 = 18044 :=
  sumLeaves_of_chunks (cs := [(1, 66), (1, 66), (1, 210), (1, 2134), (1, 64), (1, 70), (1, 326), (1, 5551), (1, 66), (1, 66), (1, 248), (1, 2417), (1, 64), (1, 70), (1, 384), (1, 6242)])
    (.cons c144 (.cons c145 (.cons c146 (.cons c147 (.cons c148 (.cons c149 (.cons c150 (.cons c151 (.cons c152 (.cons c153 (.cons c154 (.cons c155 (.cons c156 (.cons c157 (.cons c158 (.cons c159 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K144

end RACert.S3N1.C0
