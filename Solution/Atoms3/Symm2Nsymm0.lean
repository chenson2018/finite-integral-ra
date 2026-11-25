/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms3.S2N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_two_zero : (ofSymmNsymm 2 0).encard = 7 :=
  mod_cast RACert.S2N0.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
