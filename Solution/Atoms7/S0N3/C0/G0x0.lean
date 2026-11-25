/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs
public import Solution.Atoms7.S0N3.C0.S0
public import Solution.Atoms7.S0N3.C0.S1
public import Solution.Atoms7.S0N3.C0.S2
public import Solution.Atoms7.S0N3.C0.S3
public import Solution.Atoms7.S0N3.C0.S4
public import Solution.Atoms7.S0N3.C0.S5
public import Solution.Atoms7.S0N3.C0.S6
public import Solution.Atoms7.S0N3.C0.S7
public import Solution.Atoms7.S0N3.C0.S8
public import Solution.Atoms7.S0N3.C0.S9
public import Solution.Atoms7.S0N3.C0.S10
public import Solution.Atoms7.S0N3.C0.S11
public import Solution.Atoms7.S0N3.C0.S12
public import Solution.Atoms7.S0N3.C0.S13
public import Solution.Atoms7.S0N3.C0.S14
public import Solution.Atoms7.S0N3.C0.S15
public import Solution.Atoms7.S0N3.C0.S16
public import Solution.Atoms7.S0N3.C0.S17
public import Solution.Atoms7.S0N3.C0.S18
public import Solution.Atoms7.S0N3.C0.S19
public import Solution.Atoms7.S0N3.C0.S20
public import Solution.Atoms7.S0N3.C0.S21
public import Solution.Atoms7.S0N3.C0.S22
public import Solution.Atoms7.S0N3.C0.S23
public import Solution.Atoms7.S0N3.C0.S24
public import Solution.Atoms7.S0N3.C0.S25
public import Solution.Atoms7.S0N3.C0.S26
public import Solution.Atoms7.S0N3.C0.S27
public import Solution.Atoms7.S0N3.C0.S28
public import Solution.Atoms7.S0N3.C0.S29
public import Solution.Atoms7.S0N3.C0.S30
public import Solution.Atoms7.S0N3.C0.S31
public import Solution.Atoms7.S0N3.C0.S32
public import Solution.Atoms7.S0N3.C0.S33
public import Solution.Atoms7.S0N3.C0.S34
public import Solution.Atoms7.S0N3.C0.S35
public import Solution.Atoms7.S0N3.C0.S36
public import Solution.Atoms7.S0N3.C0.S37
public import Solution.Atoms7.S0N3.C0.S38
public import Solution.Atoms7.S0N3.C0.S39
public import Solution.Atoms7.S0N3.C0.S40
public import Solution.Atoms7.S0N3.C0.S41
public import Solution.Atoms7.S0N3.C0.S42
public import Solution.Atoms7.S0N3.C0.S43
public import Solution.Atoms7.S0N3.C0.S44
public import Solution.Atoms7.S0N3.C0.S45
public import Solution.Atoms7.S0N3.C0.S46
public import Solution.Atoms7.S0N3.C0.S47
public import Solution.Atoms7.S0N3.C0.S48
public import Solution.Atoms7.S0N3.C0.S49
public import Solution.Atoms7.S0N3.C0.S50
public import Solution.Atoms7.S0N3.C0.S51
public import Solution.Atoms7.S0N3.C0.S52
public import Solution.Atoms7.S0N3.C0.S53
public import Solution.Atoms7.S0N3.C0.S54
public import Solution.Atoms7.S0N3.C0.S55
public import Solution.Atoms7.S0N3.C0.S56
public import Solution.Atoms7.S0N3.C0.S57
public import Solution.Atoms7.S0N3.C0.S58
public import Solution.Atoms7.S0N3.C0.S59
public import Solution.Atoms7.S0N3.C0.S60
public import Solution.Atoms7.S0N3.C0.S61
public import Solution.Atoms7.S0N3.C0.S62
public import Solution.Atoms7.S0N3.C0.S63

/-! Generated certificate; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace G0x0

theorem total : OrbitSeg 20 perms (P.leaf 18) 0 130903 730064 32556173 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append ((S2.total).append ((S3.total).append ((S4.total).append ((S5.total).append ((S6.total).append ((S7.total).append ((S8.total).append ((S9.total).append ((S10.total).append ((S11.total).append ((S12.total).append ((S13.total).append ((S14.total).append ((S15.total).append ((S16.total).append ((S17.total).append ((S18.total).append ((S19.total).append ((S20.total).append ((S21.total).append ((S22.total).append ((S23.total).append ((S24.total).append ((S25.total).append ((S26.total).append ((S27.total).append ((S28.total).append ((S29.total).append ((S30.total).append ((S31.total).append ((S32.total).append ((S33.total).append ((S34.total).append ((S35.total).append ((S36.total).append ((S37.total).append ((S38.total).append ((S39.total).append ((S40.total).append ((S41.total).append ((S42.total).append ((S43.total).append ((S44.total).append ((S45.total).append ((S46.total).append ((S47.total).append ((S48.total).append ((S49.total).append ((S50.total).append ((S51.total).append ((S52.total).append ((S53.total).append ((S54.total).append ((S55.total).append ((S56.total).append ((S57.total).append ((S58.total).append ((S59.total).append ((S60.total).append ((S61.total).append ((S62.total).append (S63.total))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end G0x0

end RACert.S0N3.C0
