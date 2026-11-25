/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms6.S5N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_five_zero : (ofSymmNsymm 5 0).encard = 3849920 :=
  mod_cast RACert.S5N0.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
