/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms7.S2N2.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_two_two : Nat.card (ofSymmNsymm 2 2) = 2186435732 :=
  RACert.S2N2.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
