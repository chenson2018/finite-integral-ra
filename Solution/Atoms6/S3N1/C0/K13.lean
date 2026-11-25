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

namespace K208

theorem c208 : P.sumLeaves 20 208 1 = 178 := by decide +kernel

theorem c209 : P.sumLeaves 20 209 1 = 1713 := by decide +kernel

theorem c210 : P.sumLeaves 20 210 1 = 327 := by decide +kernel

theorem c211 : P.sumLeaves 20 211 1 = 5844 := by decide +kernel

theorem c212 : P.sumLeaves 20 212 1 = 238 := by decide +kernel

theorem c213 : P.sumLeaves 20 213 1 = 3472 := by decide +kernel

theorem c214 : P.sumLeaves 20 214 1 = 475 := by decide +kernel

theorem c215 : P.sumLeaves 20 215 1 = 14033 := by decide +kernel

theorem c216 : P.sumLeaves 20 216 1 = 258 := by decide +kernel

theorem c217 : P.sumLeaves 20 217 1 = 2739 := by decide +kernel

theorem c218 : P.sumLeaves 20 218 1 = 416 := by decide +kernel

theorem c219 : P.sumLeaves 20 219 1 = 7499 := by decide +kernel

theorem c220 : P.sumLeaves 20 220 1 = 418 := by decide +kernel

theorem c221 : P.sumLeaves 20 221 1 = 5677 := by decide +kernel

theorem c222 : P.sumLeaves 20 222 1 = 606 := by decide +kernel

theorem c223 : P.sumLeaves 20 223 1 = 19174 := by decide +kernel

theorem total : P.sumLeaves 20 208 16 = 63067 :=
  sumLeaves_of_chunks (cs := [(1, 178), (1, 1713), (1, 327), (1, 5844), (1, 238), (1, 3472), (1, 475), (1, 14033), (1, 258), (1, 2739), (1, 416), (1, 7499), (1, 418), (1, 5677), (1, 606), (1, 19174)])
    (.cons c208 (.cons c209 (.cons c210 (.cons c211 (.cons c212 (.cons c213 (.cons c214 (.cons c215 (.cons c216 (.cons c217 (.cons c218 (.cons c219 (.cons c220 (.cons c221 (.cons c222 (.cons c223 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K208

end RACert.S3N1.C0
