/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs
public import Solution.Atoms7.S6N0.C0.S704
public import Solution.Atoms7.S6N0.C0.S705
public import Solution.Atoms7.S6N0.C0.S706
public import Solution.Atoms7.S6N0.C0.S707
public import Solution.Atoms7.S6N0.C0.S708
public import Solution.Atoms7.S6N0.C0.S709
public import Solution.Atoms7.S6N0.C0.S710
public import Solution.Atoms7.S6N0.C0.S711
public import Solution.Atoms7.S6N0.C0.S712
public import Solution.Atoms7.S6N0.C0.S713
public import Solution.Atoms7.S6N0.C0.S714
public import Solution.Atoms7.S6N0.C0.S715
public import Solution.Atoms7.S6N0.C0.S716
public import Solution.Atoms7.S6N0.C0.S717
public import Solution.Atoms7.S6N0.C0.S718
public import Solution.Atoms7.S6N0.C0.S719
public import Solution.Atoms7.S6N0.C0.S720
public import Solution.Atoms7.S6N0.C0.S721
public import Solution.Atoms7.S6N0.C0.S722
public import Solution.Atoms7.S6N0.C0.S723
public import Solution.Atoms7.S6N0.C0.S724
public import Solution.Atoms7.S6N0.C0.S725
public import Solution.Atoms7.S6N0.C0.S726
public import Solution.Atoms7.S6N0.C0.S727
public import Solution.Atoms7.S6N0.C0.S728
public import Solution.Atoms7.S6N0.C0.S729
public import Solution.Atoms7.S6N0.C0.S730
public import Solution.Atoms7.S6N0.C0.S731
public import Solution.Atoms7.S6N0.C0.S732
public import Solution.Atoms7.S6N0.C0.S733
public import Solution.Atoms7.S6N0.C0.S734
public import Solution.Atoms7.S6N0.C0.S735
public import Solution.Atoms7.S6N0.C0.S736
public import Solution.Atoms7.S6N0.C0.S737
public import Solution.Atoms7.S6N0.C0.S738
public import Solution.Atoms7.S6N0.C0.S739
public import Solution.Atoms7.S6N0.C0.S740
public import Solution.Atoms7.S6N0.C0.S741
public import Solution.Atoms7.S6N0.C0.S742
public import Solution.Atoms7.S6N0.C0.S743
public import Solution.Atoms7.S6N0.C0.S744
public import Solution.Atoms7.S6N0.C0.S745
public import Solution.Atoms7.S6N0.C0.S746
public import Solution.Atoms7.S6N0.C0.S747
public import Solution.Atoms7.S6N0.C0.S748
public import Solution.Atoms7.S6N0.C0.S749
public import Solution.Atoms7.S6N0.C0.S750
public import Solution.Atoms7.S6N0.C0.S751
public import Solution.Atoms7.S6N0.C0.S752
public import Solution.Atoms7.S6N0.C0.S753
public import Solution.Atoms7.S6N0.C0.S754
public import Solution.Atoms7.S6N0.C0.S755
public import Solution.Atoms7.S6N0.C0.S756
public import Solution.Atoms7.S6N0.C0.S757
public import Solution.Atoms7.S6N0.C0.S758
public import Solution.Atoms7.S6N0.C0.S759
public import Solution.Atoms7.S6N0.C0.S760
public import Solution.Atoms7.S6N0.C0.S761
public import Solution.Atoms7.S6N0.C0.S762
public import Solution.Atoms7.S6N0.C0.S763
public import Solution.Atoms7.S6N0.C0.S764
public import Solution.Atoms7.S6N0.C0.S765
public import Solution.Atoms7.S6N0.C0.S766
public import Solution.Atoms7.S6N0.C0.S767

/-! Generated certificate; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0

open RACert RACert.Problem

namespace G0x11

theorem total : OrbitSeg 30 perms (P.leaf (20 + 6)) 63663065 112155643 84218200 46624638862288 :=
  OrbitSeg.cast ((S704.total).append ((S705.total).append ((S706.total).append ((S707.total).append ((S708.total).append ((S709.total).append ((S710.total).append ((S711.total).append ((S712.total).append ((S713.total).append ((S714.total).append ((S715.total).append ((S716.total).append ((S717.total).append ((S718.total).append ((S719.total).append ((S720.total).append ((S721.total).append ((S722.total).append ((S723.total).append ((S724.total).append ((S725.total).append ((S726.total).append ((S727.total).append ((S728.total).append ((S729.total).append ((S730.total).append ((S731.total).append ((S732.total).append ((S733.total).append ((S734.total).append ((S735.total).append ((S736.total).append ((S737.total).append ((S738.total).append ((S739.total).append ((S740.total).append ((S741.total).append ((S742.total).append ((S743.total).append ((S744.total).append ((S745.total).append ((S746.total).append ((S747.total).append ((S748.total).append ((S749.total).append ((S750.total).append ((S751.total).append ((S752.total).append ((S753.total).append ((S754.total).append ((S755.total).append ((S756.total).append ((S757.total).append ((S758.total).append ((S759.total).append ((S760.total).append ((S761.total).append ((S762.total).append ((S763.total).append ((S764.total).append ((S765.total).append ((S766.total).append (S767.total))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

end G0x11

end RACert.S6N0.C0
