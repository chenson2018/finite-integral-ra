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

namespace K768

theorem c768 : P.sumLeaves 20 768 1 = 253 := by decide +kernel

theorem c769 : P.sumLeaves 20 769 1 = 367 := by decide +kernel

theorem c770 : P.sumLeaves 20 770 1 = 694 := by decide +kernel

theorem c771 : P.sumLeaves 20 771 1 = 1204 := by decide +kernel

theorem c772 : P.sumLeaves 20 772 1 = 367 := by decide +kernel

theorem c773 : P.sumLeaves 20 773 1 = 1078 := by decide +kernel

theorem c774 : P.sumLeaves 20 774 1 = 1204 := by decide +kernel

theorem c775 : P.sumLeaves 20 775 1 = 2822 := by decide +kernel

theorem c776 : P.sumLeaves 20 776 1 = 318 := by decide +kernel

theorem c777 : P.sumLeaves 20 777 1 = 514 := by decide +kernel

theorem c778 : P.sumLeaves 20 778 1 = 1159 := by decide +kernel

theorem c779 : P.sumLeaves 20 779 1 = 2048 := by decide +kernel

theorem c780 : P.sumLeaves 20 780 1 = 514 := by decide +kernel

theorem c781 : P.sumLeaves 20 781 1 = 1642 := by decide +kernel

theorem c782 : P.sumLeaves 20 782 1 = 2048 := by decide +kernel

theorem c783 : P.sumLeaves 20 783 1 = 4524 := by decide +kernel

theorem total : P.sumLeaves 20 768 16 = 20756 :=
  sumLeaves_of_chunks (cs := [(1, 253), (1, 367), (1, 694), (1, 1204), (1, 367), (1, 1078), (1, 1204), (1, 2822), (1, 318), (1, 514), (1, 1159), (1, 2048), (1, 514), (1, 1642), (1, 2048), (1, 4524)])
    (.cons c768 (.cons c769 (.cons c770 (.cons c771 (.cons c772 (.cons c773 (.cons c774 (.cons c775 (.cons c776 (.cons c777 (.cons c778 (.cons c779 (.cons c780 (.cons c781 (.cons c782 (.cons c783 (.nil)))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end K768

end RACert.S3N1.C0
