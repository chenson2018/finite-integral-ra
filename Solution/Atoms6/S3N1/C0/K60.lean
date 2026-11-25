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

namespace K960

theorem c960 : P.sumLeaves 20 960 1 = 1388 := by decide +kernel

theorem c961 : P.sumLeaves 20 961 1 = 3814 := by decide +kernel

theorem c962 : P.sumLeaves 20 962 1 = 9011 := by decide +kernel

theorem c963 : P.sumLeaves 20 963 1 = 12288 := by decide +kernel

theorem c964 : P.sumLeaves 20 964 1 = 2055 := by decide +kernel

theorem c965 : P.sumLeaves 20 965 1 = 6519 := by decide +kernel

theorem c966 : P.sumLeaves 20 966 1 = 9703 := by decide +kernel

theorem c967 : P.sumLeaves 20 967 1 = 14334 := by decide +kernel

theorem c968 : P.sumLeaves 20 968 1 = 4357 := by decide +kernel

theorem c969 : P.sumLeaves 20 969 1 = 12287 := by decide +kernel

theorem c970 : P.sumLeaves 20 970 1 = 17676 := by decide +kernel

theorem c971 : P.sumLeaves 20 971 1 = 24796 := by decide +kernel

theorem c972 : P.sumLeaves 20 972 1 = 6517 := by decide +kernel

theorem c973 : P.sumLeaves 20 973 1 = 21078 := by decide +kernel

theorem c974 : P.sumLeaves 20 974 1 = 19554 := by decide +kernel

theorem c975 : P.sumLeaves 20 975 1 = 30310 := by decide +kernel

theorem total : P.sumLeaves 20 960 16 = 195687 :=
  sumLeaves_of_chunks (cs := [(1, 1388), (1, 3814), (1, 9011), (1, 12288), (1, 2055), (1, 6519), (1, 9703), (1, 14334), (1, 4357), (1, 12287), (1, 17676), (1, 24796), (1, 6517), (1, 21078), (1, 19554), (1, 30310)])
    (.cons c960 (.cons c961 (.cons c962 (.cons c963 (.cons c964 (.cons c965 (.cons c966 (.cons c967 (.cons c968 (.cons c969 (.cons c970 (.cons c971 (.cons c972 (.cons c973 (.cons c974 (.cons c975 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K960

end RACert.S3N1.C0
