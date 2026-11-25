/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms6.S3N1.Group

public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

theorem encard_ofSymmNsymm_three_one : (ofSymmNsymm 3 1).encard = 988464 :=
  mod_cast RACert.S3N1.count

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
