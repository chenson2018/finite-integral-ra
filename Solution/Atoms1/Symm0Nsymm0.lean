/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms1.S0N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_zero_zero : (ofSymmNsymm 0 0).encard = 1 :=
  mod_cast RACert.S0N0.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
