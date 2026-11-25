/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs
public import Solution.Atoms7.S0N3.C0.S128
public import Solution.Atoms7.S0N3.C0.S129
public import Solution.Atoms7.S0N3.C0.S130
public import Solution.Atoms7.S0N3.C0.S131
public import Solution.Atoms7.S0N3.C0.S132
public import Solution.Atoms7.S0N3.C0.S133
public import Solution.Atoms7.S0N3.C0.S134
public import Solution.Atoms7.S0N3.C0.S135
public import Solution.Atoms7.S0N3.C0.S136
public import Solution.Atoms7.S0N3.C0.S137
public import Solution.Atoms7.S0N3.C0.S138
public import Solution.Atoms7.S0N3.C0.S139

/-! Generated certificate; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace G0x2

theorem total : OrbitSeg 20 perms (P.leaf 18) 520586 1048576 26232 72642798 :=
  OrbitSeg.cast ((S128.total).append ((S129.total).append ((S130.total).append ((S131.total).append ((S132.total).append ((S133.total).append ((S134.total).append ((S135.total).append ((S136.total).append ((S137.total).append ((S138.total).append (S139.total))))))))))))
    (by decide +kernel) (by decide +kernel)

end G0x2

end RACert.S0N3.C0
