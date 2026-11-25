/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S2N2.C0.Defs
public import Solution.Atoms7.S2N2.C0.S192
public import Solution.Atoms7.S2N2.C0.S193
public import Solution.Atoms7.S2N2.C0.S194
public import Solution.Atoms7.S2N2.C0.S195
public import Solution.Atoms7.S2N2.C0.S196
public import Solution.Atoms7.S2N2.C0.S197
public import Solution.Atoms7.S2N2.C0.S198
public import Solution.Atoms7.S2N2.C0.S199
public import Solution.Atoms7.S2N2.C0.S200
public import Solution.Atoms7.S2N2.C0.S201
public import Solution.Atoms7.S2N2.C0.S202
public import Solution.Atoms7.S2N2.C0.S203
public import Solution.Atoms7.S2N2.C0.S204
public import Solution.Atoms7.S2N2.C0.S205
public import Solution.Atoms7.S2N2.C0.S206
public import Solution.Atoms7.S2N2.C0.S207
public import Solution.Atoms7.S2N2.C0.S208
public import Solution.Atoms7.S2N2.C0.S209

/-! Generated certificate; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S2N2.C0

open RACert RACert.Problem

namespace G0x3

theorem total : OrbitSeg 22 perms (P.leaf 22) 2028500 4194304 237856 12867689995 :=
  OrbitSeg.cast ((S192.total).append ((S193.total).append ((S194.total).append ((S195.total).append ((S196.total).append ((S197.total).append ((S198.total).append ((S199.total).append ((S200.total).append ((S201.total).append ((S202.total).append ((S203.total).append ((S204.total).append ((S205.total).append ((S206.total).append ((S207.total).append ((S208.total).append (S209.total))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end G0x3

end RACert.S2N2.C0
