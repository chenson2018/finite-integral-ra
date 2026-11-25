/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms6.S1N2.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_one_two : Nat.card (ofSymmNsymm 1 2) = 47965 :=
  RACert.S1N2.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
