/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms5.S0N2.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_zero_two : Nat.card (ofSymmNsymm 0 2) = 83 :=
  RACert.S0N2.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
