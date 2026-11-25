/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Theory.Aut
public import Solution.Theory.ComplexAlgebra
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Classification of finite integral relation algebras by lawful cycle sets

Every finite integral relation algebra with `s` symmetric diversity atoms and `n` pairs of
nonsymmetric atoms is isomorphic to the complex algebra of a lawful cycle set on
`IntegralAtom s n`. In particular this proves `exists_ofCycles_of_mem_ofSymmNsymm`.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

/-- A fixed-point-free involution on a finite type with `2 * n` elements can be straightened to
the swap of the Boolean coordinate of `Fin n × Bool`. -/
theorem exists_equiv_fin_prod_bool {X : Type*} [Finite X] (τ : X → X) (hτ : ∀ x, τ (τ x) = x)
    (hne : ∀ x, τ x ≠ x) {n : ℕ} (hcard : Nat.card X = 2 * n) :
    ∃ e : Fin n × Bool ≃ X, ∀ i b, e (i, !b) = τ (e (i, b)) := by
  classical
  -- order the elements of `X`, and take as representatives the smaller element of each pair
  let f : X → ℕ := fun x => (Finite.equivFin X x).val
  have hf : Function.Injective f := fun x y h => (Finite.equivFin X).injective (Fin.ext h)
  have hlt : ∀ x, ¬ f x < f (τ x) → f (τ x) < f (τ (τ x)) := fun x hx => by
    rw [hτ]
    exact lt_of_le_of_ne (not_lt.mp hx) fun h => hne x (hf h)
  let g : {x : X // f x < f (τ x)} × Bool ≃ X :=
    { toFun := fun p => bif p.2 then τ p.1.val else p.1.val
      invFun := fun x => if h : f x < f (τ x) then (⟨x, h⟩, false) else (⟨τ x, hlt x h⟩, true)
      left_inv := by
        rintro ⟨⟨r, hr⟩, b⟩
        cases b
        · simp [hr]
        · have : ¬ f (τ r) < f r := not_lt.mpr hr.le
          simp [this, hτ]
      right_inv := by
        intro x
        by_cases h : f x < f (τ x)
        · simp [h]
        · simp [h, hτ] }
  have hcardR : Nat.card {x : X // f x < f (τ x)} = n := by
    have h := Nat.card_congr g
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hcard,
      mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left two_pos h
  let k : Fin n ≃ {x : X // f x < f (τ x)} := ((Finite.equivFin _).trans (finCongr hcardR)).symm
  refine ⟨(Equiv.prodCongr k (Equiv.refl Bool)).trans g, fun i b => ?_⟩
  cases b
  · rfl
  · exact (hτ _).symm

namespace IntegralAtom

variable {s n : ℕ}

/-- The non-dependent eliminator of `IntegralAtom`. -/
def elim {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) : IntegralAtom s n → γ
  | one => x
  | symm i => f i
  | nsymm i b => g i b

@[simp]
theorem elim_one {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) :
    elim x f g one = x := rfl

@[simp]
theorem elim_symm {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) (i : Fin s) :
    elim x f g (symm i) = f i := rfl

@[simp]
theorem elim_nsymm {γ : Sort*} (x : γ) (f : Fin s → γ) (g : Fin n → Bool → γ) (i : Fin n)
    (b : Bool) : elim x f g (nsymm i b) = g i b := rfl

/-- The lawful atom structure of a lawful cycle set, as an instance. -/
instance instLawfulAtomStructureStructOf (T : {T : Set (Cycle s n) // IsLawfulCycles T}) :
    LawfulAtomStructure (structOf T.val) := T.property

/-- The complex algebra of a lawful cycle set is integral. -/
theorem isIntegral_structOf (T : {T : Set (Cycle s n) // IsLawfulCycles T}) :
    IsIntegral (ComplexAlgebra (structOf T.val)) :=
  (ComplexAlgebra.isIntegral_iff _).mpr ⟨one, rfl⟩

/-- The isomorphism class of the complex algebra of a lawful cycle set. -/
def isoClassOf (T : {T : Set (Cycle s n) // IsLawfulCycles T}) : IntegralAlgebra.IsoClass :=
  ⟦⟨ComplexAlgebra (structOf T.val), isIntegral_structOf T⟩⟧

section Finite

variable {α : Type*} [RelationAlgebra α] [Finite α]

/-- The atoms of a finite integral relation algebra with `s` symmetric diversity atoms and `2 * n`
nonsymmetric atoms can be labelled by `IntegralAtom s n`, compatibly with identity and converse. -/
theorem exists_equiv_isAtom (h1 : IsIntegral α) (hs : (symmetricDiversityAtoms α).ncard = s)
    (hn : (nonsymmetricDiversityAtoms α).ncard = 2 * n) :
    ∃ e : IntegralAtom s n ≃ {a : α // IsAtom a},
      (e one).val = 1 ∧ ∀ a, (e (conv a)).val = star (e a).val := by
  obtain ⟨es⟩ : Nonempty (Fin s ≃ symmetricDiversityAtoms α) :=
    ⟨((Finite.equivFin _).trans (finCongr (by rw [Nat.card_coe_set_eq, hs]))).symm⟩
  obtain ⟨en, hen⟩ := exists_equiv_fin_prod_bool (X := nonsymmetricDiversityAtoms α)
    (fun x => ⟨star x.val, isAtom_star_iff.mpr x.property.1,
      fun h => x.property.2 (star_injective h)⟩)
    (fun x => Subtype.ext (star_star x.val)) (fun x h => x.property.2 (congrArg Subtype.val h))
    (by rw [Nat.card_coe_set_eq, hn])
  let φ : IntegralAtom s n → {a : α // IsAtom a} :=
    elim ⟨1, h1⟩ (fun i => ⟨(es i).val, (es i).property.1⟩)
      (fun i b => ⟨(en (i, b)).val, (en (i, b)).property.1⟩)
  have hone_symm : (1 : α) ∉ symmetricDiversityAtoms α := fun h =>
    (IsAtom.le_compl_iff h.1).mp h.2.1 le_rfl
  have hone_nsymm : (1 : α) ∉ nonsymmetricDiversityAtoms α := fun h => h.2 (star_one α)
  have hdisj : ∀ x, x ∈ symmetricDiversityAtoms α → x ∉ nonsymmetricDiversityAtoms α :=
    fun x h h' => h'.2 h.2.2
  have hinj : Function.Injective φ := by
    rintro (_ | i | ⟨i, b⟩) (_ | j | ⟨j, c⟩) h
    · rfl
    · have h' := congrArg Subtype.val h
      change (1 : α) = (es j).val at h'
      exact (hone_symm (h' ▸ (es j).property)).elim
    · have h' := congrArg Subtype.val h
      change (1 : α) = (en (j, c)).val at h'
      exact (hone_nsymm (h' ▸ (en (j, c)).property)).elim
    · have h' := congrArg Subtype.val h
      change (es i).val = (1 : α) at h'
      exact (hone_symm (h' ▸ (es i).property)).elim
    · have h' := congrArg Subtype.val h
      change (es i).val = (es j).val at h'
      exact congrArg symm (es.injective (Subtype.ext h'))
    · have h' := congrArg Subtype.val h
      change (es i).val = (en (j, c)).val at h'
      exact (hdisj _ (es i).property (h' ▸ (en (j, c)).property)).elim
    · have h' := congrArg Subtype.val h
      change (en (i, b)).val = (1 : α) at h'
      exact (hone_nsymm (h' ▸ (en (i, b)).property)).elim
    · have h' := congrArg Subtype.val h
      change (en (i, b)).val = (es j).val at h'
      exact (hdisj _ (es j).property (h' ▸ (en (i, b)).property)).elim
    · have h' := congrArg Subtype.val h
      change (en (i, b)).val = (en (j, c)).val at h'
      have h'' := en.injective (Subtype.ext h')
      rw [Prod.mk.injEq] at h''
      rw [h''.1, h''.2]
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have hmem : a ∈ {a : α | IsAtom a} := ha
    rw [setOf_isAtom_eq, identityAtoms_eq_of_isIntegral h1] at hmem
    rcases hmem with (h | h) | h
    · exact ⟨one, Subtype.ext h.symm⟩
    · refine ⟨symm (es.symm ⟨a, h⟩), Subtype.ext ?_⟩
      change (es (es.symm ⟨a, h⟩)).val = a
      rw [Equiv.apply_symm_apply]
    · obtain ⟨⟨i, b⟩, hib⟩ := en.surjective ⟨a, h⟩
      exact ⟨nsymm i b, Subtype.ext (show (en (i, b)).val = a from congrArg Subtype.val hib)⟩
  have hconv : ∀ a, (φ (conv a)).val = star (φ a).val := by
    rintro (_ | i | ⟨i, b⟩)
    · exact (star_one α).symm
    · exact (es i).property.2.2.symm
    · exact congrArg Subtype.val (hen i b)
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, rfl, hconv⟩

/-- A finite integral relation algebra with `s` symmetric diversity atoms and `2 * n` nonsymmetric
atoms is isomorphic to the complex algebra of a lawful cycle set on `IntegralAtom s n`. -/
theorem exists_isLawfulCycles_relationAlgebraEquiv (h1 : IsIntegral α)
    (hs : (symmetricDiversityAtoms α).ncard = s)
    (hn : (nonsymmetricDiversityAtoms α).ncard = 2 * n) :
    ∃ T : {T : Set (Cycle s n) // IsLawfulCycles T},
      Nonempty (RelationAlgebraEquiv (ComplexAlgebra (structOf T.val)) α) := by
  obtain ⟨e, he1, heconv⟩ := exists_equiv_isAtom (s := s) (n := n) h1 hs hn
  let T : Set (Cycle s n) := {c | (e c.1, e c.2.1, e c.2.2) ∈ (atomStructure α).cycles}
  have hconv : ∀ a, e ((structOf T).conv a) = (atomStructure α).conv (e a) :=
    fun a => Subtype.ext (heconv a)
  have hcyc : ∀ a b c,
      (a, b, c) ∈ (structOf T).cycles ↔ (e a, e b, e c) ∈ (atomStructure α).cycles :=
    fun _ _ _ => Iff.rfl
  have hid : ∀ a, a ∈ (structOf T).id ↔ e a ∈ (atomStructure α).id := fun a => by
    change a = one ↔ (e a).val ≤ 1
    rw [IsAtom.le_iff_eq h1 (e a).property.ne_bot, ← he1, ← Subtype.ext_iff,
      e.apply_eq_iff_eq]
  have hT : IsLawfulCycles T := LawfulAtomStructure.of_equiv e hconv hid hcyc
  have := hT.lawfulAtomStructure
  exact ⟨⟨T, hT⟩,
    ⟨(ComplexAlgebra.congr e hconv hcyc).trans (complexAlgebraEquivOfFinite α).symm⟩⟩

end Finite

end IntegralAtom

namespace IntegralAlgebra.IsoClass

open IntegralAtom

variable {s n : ℕ}

/-- The class of a lawful `ofCycles` structure is the class of its full cycle set. -/
theorem isoClassOf_cycleClosure (g : Set (Cycle s n)) [LawfulAtomStructure (ofCycles g)] :
    isoClassOf ⟨{c | CycleClosure g c}, isLawfulCycles_cycleClosure g⟩ =
      ⟦⟨ComplexAlgebra (ofCycles g), isIntegral_ofCycles g⟩⟧ := rfl

/-- The class of a lawful cycle set is the class of the `ofCycles` structure generated by its
diversity cycles. -/
theorem exists_lawful_ofCycles_eq_isoClassOf (T : {T : Set (Cycle s n) // IsLawfulCycles T}) :
    ∃ _ : LawfulAtomStructure (ofCycles {c ∈ T.val | c.IsDiversity}),
      ⟦⟨ComplexAlgebra (ofCycles {c ∈ T.val | c.IsDiversity}), isIntegral_ofCycles _⟩⟧ =
        isoClassOf T := by
  have hlawful : LawfulAtomStructure (ofCycles {c ∈ T.val | c.IsDiversity}) :=
    T.property.ofCycles_diversity ▸ T.property.lawfulAtomStructure
  exact ⟨hlawful, Quotient.sound ⟨ComplexAlgebra.congr (Equiv.refl _) (fun _ => rfl)
    fun _ _ _ => T.property.cycleClosure_diversity_iff⟩⟩

theorem isoClassOf_mem_ofSymmNsymm (T : {T : Set (Cycle s n) // IsLawfulCycles T}) :
    isoClassOf T ∈ ofSymmNsymm s n := by
  obtain ⟨_, h⟩ := exists_lawful_ofCycles_eq_isoClassOf T
  exact h ▸ mk_complexAlgebra_ofCycles_mem_ofSymmNsymm _

/-- Every class in `ofSymmNsymm s n` is the class of a lawful cycle set. -/
theorem exists_isoClassOf_eq_of_mem_ofSymmNsymm {q : IsoClass} (hq : q ∈ ofSymmNsymm s n) :
    ∃ T : {T : Set (Cycle s n) // IsLawfulCycles T}, isoClassOf T = q := by
  obtain ⟨A, rfl, hs, hn⟩ := hq
  obtain ⟨T, ⟨e⟩⟩ := exists_isLawfulCycles_relationAlgebraEquiv (s := s) (n := n) A.isIntegral hs hn
  exact ⟨T, Quotient.sound ⟨e⟩⟩

/-- The classes in `ofSymmNsymm s n` are exactly the classes of lawful cycle sets. -/
theorem mem_ofSymmNsymm_iff_exists_lawful {q : IsoClass} :
    q ∈ ofSymmNsymm s n ↔
      ∃ T : {T : Set (Cycle s n) // IsLawfulCycles T}, isoClassOf T = q :=
  ⟨exists_isoClassOf_eq_of_mem_ofSymmNsymm, fun ⟨T, h⟩ => h ▸ isoClassOf_mem_ofSymmNsymm T⟩

/-- Every class in `ofSymmNsymm s n` is the class of an `ofCycles` structure. This is the
`theorem_wanted` of the same name in Cslib. -/
theorem exists_ofCycles_of_mem_ofSymmNsymm {q : IsoClass} (hq : q ∈ ofSymmNsymm s n) :
    ∃ (g : Set (IntegralAtom.Cycle s n)) (_ : LawfulAtomStructure (IntegralAtom.ofCycles g)),
      ⟦⟨ComplexAlgebra (IntegralAtom.ofCycles g), IntegralAtom.isIntegral_ofCycles g⟩⟧ = q := by
  obtain ⟨T, rfl⟩ := exists_isoClassOf_eq_of_mem_ofSymmNsymm hq
  exact ⟨_, exists_lawful_ofCycles_eq_isoClassOf T⟩

/-- The isomorphism classes with `s` symmetric diversity atoms and `n` pairs of nonsymmetric atoms
are exactly those of the complex algebras of `IntegralAtom.ofCycles`. -/
theorem mem_ofSymmNsymm_iff {q : IsoClass} :
    q ∈ ofSymmNsymm s n ↔
      ∃ (g : Set (IntegralAtom.Cycle s n)) (_ : LawfulAtomStructure (IntegralAtom.ofCycles g)),
        ⟦⟨ComplexAlgebra (IntegralAtom.ofCycles g), IntegralAtom.isIntegral_ofCycles g⟩⟧ = q :=
  ⟨exists_ofCycles_of_mem_ofSymmNsymm,
    fun ⟨g, _, h⟩ => h ▸ mk_complexAlgebra_ofCycles_mem_ofSymmNsymm g⟩

end IntegralAlgebra.IsoClass

end Cslib.RelationAlgebra
