/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
import Solution.Atoms4.S3N0.Group

public section

namespace Cslib.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_three_zero : Nat.card (ofSymmNsymm 3 0) = 65 :=
  RACert.S3N0.count

end Cslib.RelationAlgebra.IntegralAtom.IsoClass
