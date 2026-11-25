/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Theory.AutEquiv
public import Solution.Theory.Orbits

/-!
# Burnside's lemma over the explicit parametrization of the symmetry group

This restates `encard_ofSymmNsymm_eq_of_sum` with the sum over `IntegralAtom.Aut s n` reindexed
along `IntegralAtom.autEquiv`.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

open IntegralAtom

/-- Burnside form of the count, with the group enumerated as triples `(π, ρ, ε)` acting through
`IntegralAtom.autFun`. -/
theorem encard_ofSymmNsymm_eq_of_sum_triples (s n N : ℕ)
    (h : ∑ p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool),
        Nat.card {T : Set (IntegralAtom.Cycle s n) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (autFun p.1 p.2.1 p.2.2 a, autFun p.1 p.2.1 p.2.2 b,
            autFun p.1 p.2.1 p.2.2 c) ∈ T ↔ (a, b, c) ∈ T} =
      N * (s.factorial * n.factorial * 2 ^ n)) :
    (ofSymmNsymm s n).encard = N := by
  classical
  let _ : Fintype (Aut s n) := Fintype.ofFinite _
  refine encard_ofSymmNsymm_eq_of_sum' s n N ?_
  rw [card_aut, ← h]
  exact (Fintype.sum_equiv autEquiv.symm _ _ fun _ => rfl).symm

end Cslib.RelationAlgebra.IntegralAlgebra.IsoClass
