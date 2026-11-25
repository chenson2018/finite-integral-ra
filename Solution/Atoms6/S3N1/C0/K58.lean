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

namespace K928

theorem c928 : P.sumLeaves 20 928 1 = 1995 := by decide +kernel

theorem c929 : P.sumLeaves 20 929 1 = 2657 := by decide +kernel

theorem c930 : P.sumLeaves 20 930 1 = 8754 := by decide +kernel

theorem c931 : P.sumLeaves 20 931 1 = 9735 := by decide +kernel

theorem c932 : P.sumLeaves 20 932 1 = 2657 := by decide +kernel

theorem c933 : P.sumLeaves 20 933 1 = 4998 := by decide +kernel

theorem c934 : P.sumLeaves 20 934 1 = 9735 := by decide +kernel

theorem c935 : P.sumLeaves 20 935 1 = 11849 := by decide +kernel

theorem c936 : P.sumLeaves 20 936 1 = 2714 := by decide +kernel

theorem c937 : P.sumLeaves 20 937 1 = 3842 := by decide +kernel

theorem c938 : P.sumLeaves 20 938 1 = 14915 := by decide +kernel

theorem c939 : P.sumLeaves 20 939 1 = 17086 := by decide +kernel

theorem c940 : P.sumLeaves 20 940 1 = 3842 := by decide +kernel

theorem c941 : P.sumLeaves 20 941 1 = 7614 := by decide +kernel

theorem c942 : P.sumLeaves 20 942 1 = 17086 := by decide +kernel

theorem c943 : P.sumLeaves 20 943 1 = 21814 := by decide +kernel

theorem total : P.sumLeaves 20 928 16 = 141293 :=
  sumLeaves_of_chunks (cs := [(1, 1995), (1, 2657), (1, 8754), (1, 9735), (1, 2657), (1, 4998), (1, 9735), (1, 11849), (1, 2714), (1, 3842), (1, 14915), (1, 17086), (1, 3842), (1, 7614), (1, 17086), (1, 21814)])
    (.cons c928 (.cons c929 (.cons c930 (.cons c931 (.cons c932 (.cons c933 (.cons c934 (.cons c935 (.cons c936 (.cons c937 (.cons c938 (.cons c939 (.cons c940 (.cons c941 (.cons c942 (.cons c943 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K928

end RACert.S3N1.C0
