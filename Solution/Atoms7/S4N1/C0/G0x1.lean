/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Defs
public import Solution.Atoms7.S4N1.C0.S64
public import Solution.Atoms7.S4N1.C0.S65
public import Solution.Atoms7.S4N1.C0.S66
public import Solution.Atoms7.S4N1.C0.S67
public import Solution.Atoms7.S4N1.C0.S68
public import Solution.Atoms7.S4N1.C0.S69
public import Solution.Atoms7.S4N1.C0.S70
public import Solution.Atoms7.S4N1.C0.S71
public import Solution.Atoms7.S4N1.C0.S72
public import Solution.Atoms7.S4N1.C0.S73
public import Solution.Atoms7.S4N1.C0.S74
public import Solution.Atoms7.S4N1.C0.S75
public import Solution.Atoms7.S4N1.C0.S76
public import Solution.Atoms7.S4N1.C0.S77
public import Solution.Atoms7.S4N1.C0.S78
public import Solution.Atoms7.S4N1.C0.S79
public import Solution.Atoms7.S4N1.C0.S80
public import Solution.Atoms7.S4N1.C0.S81
public import Solution.Atoms7.S4N1.C0.S82
public import Solution.Atoms7.S4N1.C0.S83
public import Solution.Atoms7.S4N1.C0.S84
public import Solution.Atoms7.S4N1.C0.S85
public import Solution.Atoms7.S4N1.C0.S86
public import Solution.Atoms7.S4N1.C0.S87
public import Solution.Atoms7.S4N1.C0.S88
public import Solution.Atoms7.S4N1.C0.S89
public import Solution.Atoms7.S4N1.C0.S90
public import Solution.Atoms7.S4N1.C0.S91
public import Solution.Atoms7.S4N1.C0.S92

/-! Generated certificate; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0

open RACert RACert.Problem

namespace G0x1

theorem total : OrbitSeg 16 perms (P.leaf 34) 22254 65536 7100 1473214836683 :=
  OrbitSeg.cast ((S64.total).append ((S65.total).append ((S66.total).append ((S67.total).append ((S68.total).append ((S69.total).append ((S70.total).append ((S71.total).append ((S72.total).append ((S73.total).append ((S74.total).append ((S75.total).append ((S76.total).append ((S77.total).append ((S78.total).append ((S79.total).append ((S80.total).append ((S81.total).append ((S82.total).append ((S83.total).append ((S84.total).append ((S85.total).append ((S86.total).append ((S87.total).append ((S88.total).append ((S89.total).append ((S90.total).append ((S91.total).append (S92.total)))))))))))))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end G0x1

end RACert.S4N1.C0
