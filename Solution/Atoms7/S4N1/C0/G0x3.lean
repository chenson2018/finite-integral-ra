/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Defs
public import Solution.Atoms7.S4N1.C0.S192

/-! Generated certificate; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0

open RACert RACert.Problem

namespace G0x3

theorem total : OrbitSeg 26 perms (P.leaf (20 + 4)) 67108535 67108864 90 442052730 :=
  OrbitSeg.cast (S192.total)
    (by decide +kernel) (by decide +kernel)

end G0x3

end RACert.S4N1.C0
