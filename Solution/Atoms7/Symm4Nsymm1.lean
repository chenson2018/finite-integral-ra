/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms7.S4N1.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_four_one : (ofSymmNsymm 4 1).encard = 50265788140 :=
  mod_cast RACert.S4N1.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
