/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms7.S6N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_six_zero : (ofSymmNsymm 6 0).encard = 292352449486 :=
  mod_cast RACert.S6N0.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
