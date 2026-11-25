/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms3.S0N1.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_zero_one : Nat.card (ofSymmNsymm 0 1) = 3 :=
  RACert.S0N1.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
