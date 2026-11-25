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

namespace K864

theorem c864 : P.sumLeaves 20 864 1 = 1388 := by decide +kernel

theorem c865 : P.sumLeaves 20 865 1 = 2055 := by decide +kernel

theorem c866 : P.sumLeaves 20 866 1 = 9011 := by decide +kernel

theorem c867 : P.sumLeaves 20 867 1 = 9703 := by decide +kernel

theorem c868 : P.sumLeaves 20 868 1 = 3814 := by decide +kernel

theorem c869 : P.sumLeaves 20 869 1 = 6519 := by decide +kernel

theorem c870 : P.sumLeaves 20 870 1 = 12288 := by decide +kernel

theorem c871 : P.sumLeaves 20 871 1 = 14334 := by decide +kernel

theorem c872 : P.sumLeaves 20 872 1 = 4357 := by decide +kernel

theorem c873 : P.sumLeaves 20 873 1 = 6517 := by decide +kernel

theorem c874 : P.sumLeaves 20 874 1 = 17676 := by decide +kernel

theorem c875 : P.sumLeaves 20 875 1 = 19554 := by decide +kernel

theorem c876 : P.sumLeaves 20 876 1 = 12287 := by decide +kernel

theorem c877 : P.sumLeaves 20 877 1 = 21078 := by decide +kernel

theorem c878 : P.sumLeaves 20 878 1 = 24796 := by decide +kernel

theorem c879 : P.sumLeaves 20 879 1 = 30310 := by decide +kernel

theorem total : P.sumLeaves 20 864 16 = 195687 :=
  sumLeaves_of_chunks (cs := [(1, 1388), (1, 2055), (1, 9011), (1, 9703), (1, 3814), (1, 6519), (1, 12288), (1, 14334), (1, 4357), (1, 6517), (1, 17676), (1, 19554), (1, 12287), (1, 21078), (1, 24796), (1, 30310)])
    (.cons c864 (.cons c865 (.cons c866 (.cons c867 (.cons c868 (.cons c869 (.cons c870 (.cons c871 (.cons c872 (.cons c873 (.cons c874 (.cons c875 (.cons c876 (.cons c877 (.cons c878 (.cons c879 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K864

end RACert.S3N1.C0
