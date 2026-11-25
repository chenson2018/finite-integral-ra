/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms5.S4N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_four_zero : Nat.card (ofSymmNsymm 4 0) = 3013 :=
  RACert.S4N0.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
