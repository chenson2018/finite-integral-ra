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

namespace K96

theorem c96 : P.sumLeaves 20 96 1 = 196 := by decide +kernel

theorem c97 : P.sumLeaves 20 97 1 = 174 := by decide +kernel

theorem c98 : P.sumLeaves 20 98 1 = 195 := by decide +kernel

theorem c99 : P.sumLeaves 20 99 1 = 257 := by decide +kernel

theorem c100 : P.sumLeaves 20 100 1 = 492 := by decide +kernel

theorem c101 : P.sumLeaves 20 101 1 = 882 := by decide +kernel

theorem c102 : P.sumLeaves 20 102 1 = 1259 := by decide +kernel

theorem c103 : P.sumLeaves 20 103 1 = 4784 := by decide +kernel

theorem c104 : P.sumLeaves 20 104 1 = 283 := by decide +kernel

theorem c105 : P.sumLeaves 20 105 1 = 264 := by decide +kernel

theorem c106 : P.sumLeaves 20 106 1 = 245 := by decide +kernel

theorem c107 : P.sumLeaves 20 107 1 = 339 := by decide +kernel

theorem c108 : P.sumLeaves 20 108 1 = 981 := by decide +kernel

theorem c109 : P.sumLeaves 20 109 1 = 1792 := by decide +kernel

theorem c110 : P.sumLeaves 20 110 1 = 2269 := by decide +kernel

theorem c111 : P.sumLeaves 20 111 1 = 7997 := by decide +kernel

theorem total : P.sumLeaves 20 96 16 = 22409 :=
  sumLeaves_of_chunks (cs := [(1, 196), (1, 174), (1, 195), (1, 257), (1, 492), (1, 882), (1, 1259), (1, 4784), (1, 283), (1, 264), (1, 245), (1, 339), (1, 981), (1, 1792), (1, 2269), (1, 7997)])
    (.cons c96 (.cons c97 (.cons c98 (.cons c99 (.cons c100 (.cons c101 (.cons c102 (.cons c103 (.cons c104 (.cons c105 (.cons c106 (.cons c107 (.cons c108 (.cons c109 (.cons c110 (.cons c111 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K96

end RACert.S3N1.C0
