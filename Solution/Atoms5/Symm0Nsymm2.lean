/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms5.S0N2.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_zero_two : (ofSymmNsymm 0 2).encard = 83 :=
  mod_cast RACert.S0N2.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
