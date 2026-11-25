/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms7.S0N3.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_zero_three : (ofSymmNsymm 0 3).encard = 4492953 :=
  mod_cast RACert.S0N3.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
