/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms7.S2N2.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_two_two : (ofSymmNsymm 2 2).encard = 2186435732 :=
  mod_cast RACert.S2N2.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
