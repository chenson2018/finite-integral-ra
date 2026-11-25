/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms5.S2N1.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_two_one : Nat.card (ofSymmNsymm 2 1) = 1316 :=
  RACert.S2N1.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
