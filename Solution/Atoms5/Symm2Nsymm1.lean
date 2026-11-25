/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms5.S2N1.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_two_one : (ofSymmNsymm 2 1).encard = 1316 :=
  mod_cast RACert.S2N1.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
