/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms3.S2N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_two_zero : Nat.card (ofSymmNsymm 2 0) = 7 :=
  RACert.S2N0.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
