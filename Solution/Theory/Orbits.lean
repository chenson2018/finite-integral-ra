/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Theory.Classification
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting isomorphism classes as orbits

Two lawful cycle sets on `IntegralAtom s n` have isomorphic complex algebras exactly when they lie
in the same orbit of `IntegralAtom.Aut s n`. Hence the number of isomorphism classes of finite
integral relation algebras with `s` symmetric diversity atoms and `n` pairs of nonsymmetric atoms
is the number of orbits, which Burnside's lemma expresses through counts of fixed points.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

namespace IntegralAtom

variable {s n : ℕ}

/-- Two lawful cycle sets have isomorphic complex algebras exactly when they are related by an
element of `Aut s n`. -/
theorem isoClassOf_eq_iff (T T' : {T : Set (Cycle s n) // IsLawfulCycles T}) :
    isoClassOf T = isoClassOf T' ↔ ∃ σ : Aut s n, σ • T = T' := by
  constructor
  · intro h
    obtain ⟨f⟩ : Nonempty (RelationAlgebraEquiv (ComplexAlgebra (structOf T.val))
      (ComplexAlgebra (structOf T'.val))) := Quotient.exact h
    obtain ⟨e, -, hconv, hid, hcyc⟩ := ComplexAlgebra.exists_equiv_of_relationAlgebraEquiv f
    exact ⟨⟨e, mem_aut_iff.mpr ⟨(hid one).mpr rfl, hconv⟩⟩, smul_eq_iff.mpr hcyc⟩
  · rintro ⟨σ, rfl⟩
    exact Quotient.sound
      ⟨ComplexAlgebra.congr σ.val (Aut.apply_conv σ) fun _ _ _ => apply_mem_smul_iff.symm⟩

/-- The lawful cycle sets fixed by `σ`, as a plain subtype of cycle sets. -/
def fixedByEquiv (σ : Aut s n) :
    MulAction.fixedBy {T : Set (Cycle s n) // IsLawfulCycles T} σ ≃
      {T : Set (Cycle s n) // IsLawfulCycles T ∧
        ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} where
  toFun T := ⟨T.val.val, T.val.property, smul_eq_self_iff.mp T.property⟩
  invFun T := ⟨⟨T.val, T.property.1⟩, smul_eq_self_iff.mpr T.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end IntegralAtom

namespace IntegralAlgebra.IsoClass

open IntegralAtom

variable {s n : ℕ}

theorem range_isoClassOf (s n : ℕ) :
    Set.range (isoClassOf (s := s) (n := n)) = ofSymmNsymm s n :=
  Set.ext fun _ => mem_ofSymmNsymm_iff_exists_lawful.symm

/-- The isomorphism class of an orbit of lawful cycle sets. -/
def orbitIsoClass (s n : ℕ) :
    MulAction.orbitRel.Quotient (Aut s n) {T : Set (Cycle s n) // IsLawfulCycles T} → IsoClass :=
  Quotient.lift isoClassOf fun T T' h => by
    obtain ⟨σ, hσ⟩ := MulAction.orbitRel_apply.mp h
    exact ((isoClassOf_eq_iff T' T).mpr ⟨σ, hσ⟩).symm

@[simp]
theorem orbitIsoClass_mk (T : {T : Set (Cycle s n) // IsLawfulCycles T}) :
    orbitIsoClass s n ⟦T⟧ = isoClassOf T := rfl

theorem orbitIsoClass_injective (s n : ℕ) : Function.Injective (orbitIsoClass s n) := by
  intro x y
  induction x using Quotient.inductionOn with | _ T
  induction y using Quotient.inductionOn with | _ T'
  intro h
  obtain ⟨σ, hσ⟩ := (isoClassOf_eq_iff T' T).mp h.symm
  exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨σ, hσ⟩)

theorem range_orbitIsoClass (s n : ℕ) : Set.range (orbitIsoClass s n) = ofSymmNsymm s n := by
  rw [← range_isoClassOf]
  exact Set.range_quotient_lift (s := MulAction.orbitRel _ _) _

/-- The number of isomorphism classes of finite integral relation algebras with `s` symmetric
diversity atoms and `n` pairs of nonsymmetric atoms is the number of orbits of `Aut s n` on lawful
cycle sets. -/
theorem encard_ofSymmNsymm_eq_card_orbits (s n : ℕ) :
    (ofSymmNsymm s n).encard =
      (Nat.card (MulAction.orbitRel.Quotient (IntegralAtom.Aut s n)
        {T : Set (IntegralAtom.Cycle s n) // IntegralAtom.IsLawfulCycles T}) : ℕ∞) := by
  rw [← range_orbitIsoClass, (orbitIsoClass_injective s n).encard_range,
    ENat.card_eq_coe_natCard]

/-- Burnside's lemma for the action of `Aut s n` on lawful cycle sets. -/
theorem sum_card_fixed_eq_card_orbits_mul_card_aut (s n : ℕ) [Fintype (Aut s n)] :
    ∑ σ : IntegralAtom.Aut s n,
        Nat.card {T : Set (IntegralAtom.Cycle s n) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} =
      Nat.card (MulAction.orbitRel.Quotient (IntegralAtom.Aut s n)
        {T : Set (IntegralAtom.Cycle s n) // IntegralAtom.IsLawfulCycles T}) *
        Nat.card (IntegralAtom.Aut s n) := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient (Aut s n)
    {T : Set (Cycle s n) // IsLawfulCycles T}) := Fintype.ofFinite _
  let _ : ∀ σ : Aut s n,
      Fintype (MulAction.fixedBy {T : Set (Cycle s n) // IsLawfulCycles T} σ) :=
    fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (fixedByEquiv σ)]

theorem card_aut_pos (s n : ℕ) : 0 < Nat.card (Aut s n) := Nat.card_pos

/-- Burnside form of the count, with the sum over any `Fintype` structure on `Aut s n`. -/
theorem encard_ofSymmNsymm_eq_of_sum' (s n N : ℕ) [Fintype (Aut s n)]
    (h : ∑ σ : IntegralAtom.Aut s n,
        Nat.card {T : Set (IntegralAtom.Cycle s n) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} =
      N * Nat.card (IntegralAtom.Aut s n)) :
    (ofSymmNsymm s n).encard = N := by
  rw [sum_card_fixed_eq_card_orbits_mul_card_aut] at h
  rw [encard_ofSymmNsymm_eq_card_orbits, Nat.eq_of_mul_eq_mul_right (card_aut_pos s n) h]

/-- Burnside form of the count: if the numbers of lawful cycle sets fixed by the elements of
`Aut s n` sum to `N * |Aut s n|`, then there are `N` isomorphism classes. -/
theorem encard_ofSymmNsymm_eq_of_sum (s n N : ℕ)
    (h : ∑ᶠ σ : IntegralAtom.Aut s n,
        Nat.card {T : Set (IntegralAtom.Cycle s n) // IntegralAtom.IsLawfulCycles T ∧
          ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T ↔ (a, b, c) ∈ T} =
      N * Nat.card (IntegralAtom.Aut s n)) :
    (ofSymmNsymm s n).encard = N := by
  classical
  let _ : Fintype (Aut s n) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at h
  exact encard_ofSymmNsymm_eq_of_sum' s n N h

end IntegralAlgebra.IsoClass

end Cslib.RelationAlgebra
