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

namespace K176

theorem c176 : P.sumLeaves 20 176 1 = 76 := by decide +kernel

theorem c177 : P.sumLeaves 20 177 1 = 72 := by decide +kernel

theorem c178 : P.sumLeaves 20 178 1 = 3036 := by decide +kernel

theorem c179 : P.sumLeaves 20 179 1 = 4585 := by decide +kernel

theorem c180 : P.sumLeaves 20 180 1 = 72 := by decide +kernel

theorem c181 : P.sumLeaves 20 181 1 = 98 := by decide +kernel

theorem c182 : P.sumLeaves 20 182 1 = 4585 := by decide +kernel

theorem c183 : P.sumLeaves 20 183 1 = 13294 := by decide +kernel

theorem c184 : P.sumLeaves 20 184 1 = 76 := by decide +kernel

theorem c185 : P.sumLeaves 20 185 1 = 72 := by decide +kernel

theorem c186 : P.sumLeaves 20 186 1 = 3057 := by decide +kernel

theorem c187 : P.sumLeaves 20 187 1 = 4614 := by decide +kernel

theorem c188 : P.sumLeaves 20 188 1 = 72 := by decide +kernel

theorem c189 : P.sumLeaves 20 189 1 = 98 := by decide +kernel

theorem c190 : P.sumLeaves 20 190 1 = 4614 := by decide +kernel

theorem c191 : P.sumLeaves 20 191 1 = 13391 := by decide +kernel

theorem total : P.sumLeaves 20 176 16 = 51812 :=
  sumLeaves_of_chunks (cs := [(1, 76), (1, 72), (1, 3036), (1, 4585), (1, 72), (1, 98), (1, 4585), (1, 13294), (1, 76), (1, 72), (1, 3057), (1, 4614), (1, 72), (1, 98), (1, 4614), (1, 13391)])
    (.cons c176 (.cons c177 (.cons c178 (.cons c179 (.cons c180 (.cons c181 (.cons c182 (.cons c183 (.cons c184 (.cons c185 (.cons c186 (.cons c187 (.cons c188 (.cons c189 (.cons c190 (.cons c191 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K176

end RACert.S3N1.C0
