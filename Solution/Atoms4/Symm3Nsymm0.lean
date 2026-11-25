/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms4.S3N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_three_zero : (ofSymmNsymm 3 0).encard = 65 :=
  mod_cast RACert.S3N0.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
