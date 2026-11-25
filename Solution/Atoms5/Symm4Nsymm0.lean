/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms5.S4N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_four_zero : (ofSymmNsymm 4 0).encard = 3013 :=
  mod_cast RACert.S4N0.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
