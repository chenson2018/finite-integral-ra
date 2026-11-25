/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Eval

/-!
# Symmetries of a counting problem

A permutation of the atoms which respects the classes of a `Problem` induces a permutation of its
variables under which the set of models is invariant. If this permutation preserves the split into
low and high variables, then the leaf of an assignment of the high variables only depends on its
orbit. This file proves that invariance (`Problem.card_models_le_of_symF`), and the criterion
`Problem.leaf_dead` for a leaf to vanish because one associativity condition is already violated
by the high variables alone.
-/

@[expose] public section

namespace RACert

open Cslib.RelationAlgebra IntegralAtom

/-- The action of a permutation of the variables on class codes. -/
def vmapF (π : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => π j + 2

/-- Transport of `dotB` along a map of codes relating two tables. -/
theorem dotB_transport {k : ℕ} {X X' : ℕ → ℕ → ℕ → Bool} {f g : ℕ → ℕ} (hf : ∀ a < k, f a < k)
    (hg : ∀ a < k, g a < k) (hfg : ∀ a < k, f (g a) = a)
    (hX : ∀ a < k, ∀ b < k, ∀ c < k, X' (f a) (f b) (f c) = X a b c) {a b c d : ℕ} (ha : a < k)
    (hb : b < k) (hc : c < k) (hd : d < k) :
    dotB k X' (f a) (f b) (f c) (f d) = dotB k X a b c d := by
  rw [Bool.eq_iff_iff, dotB_iff, dotB_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    refine ⟨g q, hg q hq, ?_, ?_⟩
    · rw [← hX a ha b hb _ (hg q hq), hfg q hq]; exact h1
    · rw [← hX c hc d hd _ (hg q hq), hfg q hq]; exact h2
  · rintro ⟨q, hq, h1, h2⟩
    exact ⟨f q, hf q hq, by rw [hX a ha b hb q hq]; exact h1, by rw [hX c hc d hd q hq]; exact h2⟩

/-- Transport of the associativity condition along a map of codes relating two tables. -/
theorem quadB_transport {s n : ℕ} {X X' : ℕ → ℕ → ℕ → Bool} {f g : ℕ → ℕ}
    (hf : ∀ a < numAtoms s n, f a < numAtoms s n) (hg : ∀ a < numAtoms s n, g a < numAtoms s n)
    (hfg : ∀ a < numAtoms s n, f (g a) = a)
    (hX : ∀ a < numAtoms s n, ∀ b < numAtoms s n, ∀ c < numAtoms s n,
      X' (f a) (f b) (f c) = X a b c)
    (hcv : ∀ a < numAtoms s n, f (cvN s a) = cvN s (f a)) {r u t p : ℕ}
    (hr : r < numAtoms s n) (hu : u < numAtoms s n) (ht : t < numAtoms s n)
    (hp : p < numAtoms s n) :
    quadB s (numAtoms s n) X' (f r) (f u) (f t) (f p) = quadB s (numAtoms s n) X r u t p := by
  unfold quadB
  rw [← hcv r hr, ← hcv t ht, dotB_transport hf hg hfg hX (cvN_lt hr) hp hu ht,
    dotB_transport hf hg hfg hX hr hu hp (cvN_lt ht)]

namespace Problem

variable {P : Problem}

/-- Every class code is a constant or one of the `V` variables. -/
theorem clsAt_lt (h : P.check = true) {a b c : ℕ} (ha : a < P.k) (hb : b < P.k) (hc : c < P.k) :
    P.clsAt a b c < P.V + 2 := by
  by_cases h0 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0
  · exact (checkDiv_spec h ha hb hc h0).2.1
  · have h0' : a = 0 ∨ b = 0 ∨ c = 0 := by tauto
    have hle : ∀ x y : ℕ, (bif Nat.beq x y then 1 else 0) < P.V + 2 := by
      intro x y
      cases Nat.beq x y <;> simp
    rcases h0' with rfl | rfl | rfl
    · rw [(checkId_spec h hb hc).2.1]; exact hle _ _
    · rw [(checkId_spec h ha hc).1]; exact hle _ _
    · rw [(checkId_spec h ha hb).2.2]; exact hle _ _

/-- The table of an assignment only depends on the first `V` variables. -/
theorem tbl_congr (h : P.check = true) {v v' : ℕ → Bool} (hv : ∀ j < P.V, v j = v' j) {a b c : ℕ}
    (ha : a < P.k) (hb : b < P.k) (hc : c < P.k) : P.tbl v a b c = P.tbl v' a b c := by
  have hlt := clsAt_lt h ha hb hc
  rw [tbl, tbl]
  match hm : P.clsAt a b c with
  | 0 => rfl
  | 1 => rfl
  | j + 2 => exact hv j (by omega)

/-- The formula only depends on the first `V` variables. -/
theorem phi_congr (h : P.check = true) {v v' : ℕ → Bool} (hv : ∀ j < P.V, v j = v' j) :
    P.phi v = P.phi v' := by
  have hk := numAtoms_pos P.s P.n
  rw [phi, phi]
  congr 1
  funext x
  rw [quadAt, quadAt]
  exact quadB_congr (fun a ha b hb c hc => tbl_congr h hv ha hb hc) (Nat.mod_lt _ hk)
    (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) (Nat.mod_lt _ hk)

/-- A symmetry of the problem: a permutation `f` of the atom codes (with inverse `g`) commuting
with converse, and a permutation `π` of the variables (with inverse `ρ`) preserving the low
variables, such that `f` maps the class of a triple according to `π`. -/
structure SymF (P : Problem) (b : ℕ) (f g π ρ : ℕ → ℕ) : Prop where
  f_lt : ∀ c < P.k, f c < P.k
  g_lt : ∀ c < P.k, g c < P.k
  fg : ∀ c < P.k, f (g c) = c
  gf : ∀ c < P.k, g (f c) = c
  f_cv : ∀ c < P.k, f (cvN P.s c) = cvN P.s (f c)
  cls : ∀ a < P.k, ∀ b' < P.k, ∀ c < P.k,
    P.clsAt (f a) (f b') (f c) = vmapF π (P.clsAt a b' c)
  π_lt : ∀ j < P.V, π j < P.V
  ρ_lt : ∀ j < P.V, ρ j < P.V
  ρπ : ∀ j < P.V, ρ (π j) = j
  πρ : ∀ j < P.V, π (ρ j) = j
  low : ∀ j < P.V, (j < b ↔ π j < b)

theorem vmapF_inv {π ρ : ℕ → ℕ} {V m : ℕ} (hρπ : ∀ j < V, ρ (π j) = j) (hm : m < V + 2) :
    vmapF ρ (vmapF π m) = m := by
  match m with
  | 0 => rfl
  | 1 => rfl
  | j + 2 => simp only [vmapF]; rw [hρπ j (by omega)]

/-- The inverse symmetry. -/
theorem SymF.symm {b : ℕ} {f g π ρ : ℕ → ℕ} (h : P.check = true) (F : SymF P b f g π ρ) :
    SymF P b g f ρ π where
  f_lt := F.g_lt
  g_lt := F.f_lt
  fg := F.gf
  gf := F.fg
  f_cv c hc := by
    have h1 := F.f_cv (g c) (F.g_lt c hc)
    rw [F.fg c hc] at h1
    rw [← h1, F.gf _ (cvN_lt (F.g_lt c hc))]
  cls a ha b' hb c hc := by
    have h1 := F.cls (g a) (F.g_lt a ha) (g b') (F.g_lt b' hb) (g c) (F.g_lt c hc)
    rw [F.fg a ha, F.fg b' hb, F.fg c hc] at h1
    rw [h1, vmapF_inv F.ρπ (clsAt_lt h (F.g_lt a ha) (F.g_lt b' hb) (F.g_lt c hc))]
  π_lt := F.ρ_lt
  ρ_lt := F.π_lt
  ρπ := F.πρ
  πρ := F.ρπ
  low j hj := by
    have h1 := F.low (ρ j) (F.ρ_lt j hj)
    rw [F.πρ j hj] at h1
    exact h1.symm

/-- Models are transported along a symmetry. -/
theorem SymF.phi_comp {b : ℕ} {f g π ρ : ℕ → ℕ} (h : P.check = true) (F : SymF P b f g π ρ)
    {v : ℕ → Bool} (hv : P.phi v = true) : P.phi (fun j => v (ρ j)) = true := by
  have hk := numAtoms_pos P.s P.n
  have hX : ∀ a < P.k, ∀ b' < P.k, ∀ c < P.k,
      P.tbl (fun j => v (ρ j)) (f a) (f b') (f c) = P.tbl v a b' c := by
    intro a ha b' hb c hc
    have hlt := clsAt_lt h ha hb hc
    rw [tbl, tbl, F.cls a ha b' hb c hc]
    match hm : P.clsAt a b' c with
    | 0 => rfl
    | 1 => rfl
    | j + 2 =>
      simp only [vmapF, litB]
      rw [F.ρπ j (by omega)]
  rw [phi, List.all_eq_true]
  intro x _
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  have key := quadB_transport (X := P.tbl v) (X' := P.tbl fun j => v (ρ j)) F.f_lt F.g_lt F.fg hX
    F.f_cv (F.g_lt _ (hm (x / P.k / P.k / P.k))) (F.g_lt _ (hm (x / P.k / P.k)))
    (F.g_lt _ (hm (x / P.k))) (F.g_lt _ (hm x))
  rw [F.fg _ (hm _), F.fg _ (hm _), F.fg _ (hm _), F.fg _ (hm _)] at key
  rw [quadAt, key]
  exact quadB_of_phi h hv (F.g_lt _ (hm _)) (F.g_lt _ (hm _)) (F.g_lt _ (hm _)) (F.g_lt _ (hm _))

/-- Along a symmetry, the models above an assignment `α` of the high variables inject into the
models above the transported assignment `α'`. -/
theorem SymF.card_models_le {b : ℕ} {f g π ρ : ℕ → ℕ} (h : P.check = true) (hb : b ≤ P.V)
    (F : SymF P b f g π ρ) {α α' : ℕ}
    (hbits : ∀ j, b ≤ j → j < P.V → α'.testBit (j - b) = α.testBit (ρ j - b)) :
    (Finset.univ.filter fun w : Fin b → Bool => P.phi (join b α w) = true).card ≤
      (Finset.univ.filter fun w : Fin b → Bool => P.phi (join b α' w) = true).card := by
  have Fs := F.symm h
  have hρlow : ∀ j < P.V, (j < b ↔ ρ j < b) := Fs.low
  refine Finset.card_le_card_of_injOn
    (fun w => fun i : Fin b => w ⟨ρ i, (hρlow i (by omega)).mp i.isLt⟩) ?_ ?_
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← F.phi_comp h hw.2]
    apply phi_congr h
    intro j hj
    by_cases hjb : j < b
    · have hρ := (hρlow j hj).mp hjb
      simp [join, hjb, hρ]
    · have hρ : ¬ ρ j < b := fun hlt => hjb ((hρlow j hj).mpr hlt)
      simp only [join, hjb, hρ, dite_false]
      exact hbits j (by omega) hj
  · intro w _ w' _ heq
    funext ⟨i, hi⟩
    have hπ : π i < b := (F.low i (by omega)).mp hi
    have := congrFun heq ⟨π i, hπ⟩
    simp only [F.ρπ i (by omega)] at this
    exact this

/-- The two sides of the condition of the quadruple `(r, u, t, p)` are opposite constants. -/
noncomputable def deadLR (T L R : ℕ) : Bool :=
  (Nat.beq L T && Nat.beq R 0) || (Nat.beq L 0 && Nat.beq R T)

/-- The associativity condition of the quadruple `(r, u, t, p)` is violated for every assignment
of the low variables, the high variables being given by `α`. -/
noncomputable def deadAt4 (P : Problem) (b α r u t p : ℕ) : Bool :=
  deadLR (top b)
    (dot (top b) (rowAt (rowsOf (top b) (varTabs b (Nat.sub P.V b) α) P.cls) (cvN P.s r) p)
      (rowAt (rowsOf (top b) (varTabs b (Nat.sub P.V b) α) P.cls) u t) 0)
    (dot (top b) (rowAt (rowsOf (top b) (varTabs b (Nat.sub P.V b) α) P.cls) r u)
      (rowAt (rowsOf (top b) (varTabs b (Nat.sub P.V b) α) P.cls) p (cvN P.s t)) 0)

/-- The associativity condition of the quadruple with code `x` is violated for every assignment
of the low variables, the high variables being given by `α`. -/
noncomputable def deadAt (P : Problem) (b α x : ℕ) : Bool :=
  P.deadAt4 b α (Nat.mod (Nat.div (Nat.div (Nat.div x P.k) P.k) P.k) P.k)
    (Nat.mod (Nat.div (Nat.div x P.k) P.k) P.k) (Nat.mod (Nat.div x P.k) P.k) (Nat.mod x P.k)

theorem deadAt_eq (P : Problem) (b α x : ℕ) :
    P.deadAt b α x = P.deadAt4 b α (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k)
      (x / P.k % P.k) (x % P.k) := rfl

/-- A leaf vanishes when some associativity condition is violated by the high variables alone. -/
theorem leaf_dead (hcheck : P.check = true) (hrows : P.checkRows = true) {b α x : ℕ}
    (hα : α < 2 ^ (P.V - b)) (hdead : P.deadAt b α x = true) : P.leaf b α = 0 := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  rw [leaf_eq hrows hα, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hphi
  have hβ : Nat.ofBits w < 2 ^ b := Nat.ofBits_lt_two_pow w
  have hw : (fun i : Fin b => (Nat.ofBits w).testBit i) = w := by
    funext i
    exact Nat.testBit_ofBits_lt w i i.isLt
  have hgood := goodVt_varTabs hα hβ
  rw [← join_testBit, hw] at hgood
  obtain ⟨-, hL⟩ := dot_rows_spec hrows hgood (cvN_lt (hm (x / P.k / P.k / P.k))) (hm x)
    (hm (x / P.k / P.k)) (hm (x / P.k))
  obtain ⟨-, hR⟩ := dot_rows_spec hrows hgood (hm (x / P.k / P.k / P.k)) (hm (x / P.k / P.k))
    (hm x) (cvN_lt (hm (x / P.k)))
  have hq := quadB_of_phi hcheck hphi (hm (x / P.k / P.k / P.k)) (hm (x / P.k / P.k))
    (hm (x / P.k)) (hm x)
  rw [quadB, beq_iff_eq, ← hL, ← hR] at hq
  have hT := top_pos b
  rw [deadAt_eq, deadAt4, deadLR, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq,
    Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at hdead
  rcases hdead with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : dot (top b) (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _)
        (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _) 0 = top b := h1
    have h2' : dot (top b) (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _)
        (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _) 0 = 0 := h2
    rw [h1', h2', sem_top, sem_zero hT] at hq
    exact Bool.noConfusion hq
  · have h1' : dot (top b) (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _)
        (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _) 0 = 0 := h1
    have h2' : dot (top b) (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _)
        (rowAt (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) _ _) 0 = top b := h2
    rw [h1', h2', sem_top, sem_zero hT] at hq
    exact Bool.noConfusion hq

/-- Two assignments of the high variables related by a symmetry have the same leaf. -/
theorem SymF.leaf_eq {b : ℕ} {f g π ρ : ℕ → ℕ} (hcheck : P.check = true)
    (hrows : P.checkRows = true) (hb : b ≤ P.V) (F : SymF P b f g π ρ) {α α' : ℕ}
    (hα : α < 2 ^ (P.V - b)) (hα' : α' < 2 ^ (P.V - b))
    (h1 : ∀ j, b ≤ j → j < P.V → α'.testBit (j - b) = α.testBit (ρ j - b))
    (h2 : ∀ j, b ≤ j → j < P.V → α.testBit (j - b) = α'.testBit (π j - b)) :
    P.leaf b α' = P.leaf b α := by
  rw [Problem.leaf_eq hrows hα, Problem.leaf_eq hrows hα']
  exact Nat.le_antisymm ((F.symm hcheck).card_models_le hcheck hb h2)
    (F.card_models_le hcheck hb h1)

end Problem

/-- A symmetry of a problem, as lists: an atom permutation with its inverse, and the induced
permutation of the variables with its inverse. -/
structure Sym where
  /-- The permutation of atom codes. -/
  h : List ℕ
  /-- Its inverse. -/
  hi : List ℕ
  /-- The induced permutation of the variables. -/
  vp : List ℕ
  /-- Its inverse. -/
  vq : List ℕ

/-- `vmapF` for a permutation given as a list. -/
noncomputable def vmapL (vp : List ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun m' _ => Nat.rec (motive := fun _ => ℕ) 1 (fun j _ => Nat.add (nth 0 vp j) 2) m') m

theorem vmapL_eq (vp : List ℕ) (m : ℕ) : vmapL vp m = vmapF (nth 0 vp) m := by
  match m with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

namespace Problem

variable {P : Problem}

/-- The atom part of the symmetry check. -/
noncomputable def checkSymAtoms (P : Problem) (S : Sym) : Bool :=
  allRange P.k fun c =>
    Nat.blt (nth 0 S.h c) P.k && (Nat.blt (nth 0 S.hi c) P.k &&
      (Nat.beq (nth 0 S.h (nth 0 S.hi c)) c && (Nat.beq (nth 0 S.hi (nth 0 S.h c)) c &&
        Nat.beq (nth 0 S.h (cvN P.s c)) (cvN P.s (nth 0 S.h c)))))

/-- The class part of the symmetry check. -/
noncomputable def checkSymCls (P : Problem) (S : Sym) : Bool :=
  allRange P.k fun a => allRange P.k fun b' => allRange P.k fun c =>
    Nat.beq (P.clsAt (nth 0 S.h a) (nth 0 S.h b') (nth 0 S.h c)) (vmapL S.vp (P.clsAt a b' c))

/-- The variable part of the symmetry check. -/
noncomputable def checkSymVars (P : Problem) (b : ℕ) (S : Sym) : Bool :=
  allRange P.V fun j =>
    Nat.blt (nth 0 S.vp j) P.V && (Nat.blt (nth 0 S.vq j) P.V &&
      (Nat.beq (nth 0 S.vq (nth 0 S.vp j)) j && (Nat.beq (nth 0 S.vp (nth 0 S.vq j)) j &&
        (Nat.blt j b == Nat.blt (nth 0 S.vp j) b))))

/-- The lists `e = (p, q)` are the action of the symmetry on the high variables. -/
noncomputable def checkSymTop (P : Problem) (b : ℕ) (S : Sym) (e : List ℕ × List ℕ) : Bool :=
  allRange (P.V - b) fun i =>
    Nat.beq (Nat.add (nth 0 e.1 i) b) (nth 0 S.vp (Nat.add b i)) &&
      Nat.beq (Nat.add (nth 0 e.2 i) b) (nth 0 S.vq (Nat.add b i))

/-- `S` is a symmetry of the problem acting on the high variables through `e`. -/
noncomputable def checkSym (P : Problem) (b : ℕ) (S : Sym) (e : List ℕ × List ℕ) : Bool :=
  P.checkSymAtoms S && (P.checkSymCls S && (P.checkSymVars b S && P.checkSymTop b S e))

theorem checkSym_spec {b : ℕ} {S : Sym} {e : List ℕ × List ℕ} (h : P.checkSym b S e = true) :
    SymF P b (nth 0 S.h) (nth 0 S.hi) (nth 0 S.vp) (nth 0 S.vq) ∧
      ∀ i < P.V - b, nth 0 e.1 i + b = nth 0 S.vp (b + i) ∧ nth 0 e.2 i + b = nth 0 S.vq (b + i) := by
  simp only [checkSym, Bool.and_eq_true] at h
  obtain ⟨hA, hC, hV, hT⟩ := h
  have hA' : ∀ c < P.k, _ := fun c hc => by
    simpa only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using allRange_iff.mp hA c hc
  have hV' : ∀ j < P.V, _ := fun j hj => by
    simpa only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, beq_iff_eq] using
      allRange_iff.mp hV j hj
  refine ⟨⟨fun c hc => (hA' c hc).1, fun c hc => (hA' c hc).2.1, fun c hc => (hA' c hc).2.2.1,
    fun c hc => (hA' c hc).2.2.2.1, fun c hc => (hA' c hc).2.2.2.2, ?_, fun j hj => (hV' j hj).1,
    fun j hj => (hV' j hj).2.1, fun j hj => (hV' j hj).2.2.1, fun j hj => (hV' j hj).2.2.2.1,
    ?_⟩, ?_⟩
  · intro a ha b' hb c hc
    have := allRange_iff.mp (allRange_iff.mp (allRange_iff.mp hC a ha) b' hb) c hc
    rw [Nat.beq_eq, vmapL_eq] at this
    exact this
  · intro j hj
    have := (hV' j hj).2.2.2.2
    constructor
    · intro hlt
      have e1 : Nat.blt j b = true := by rw [Nat.blt_eq]; exact hlt
      rw [e1] at this
      exact Nat.blt_eq.mp this.symm
    · intro hlt
      have e1 : Nat.blt (nth 0 S.vp j) b = true := by rw [Nat.blt_eq]; exact hlt
      rw [e1] at this
      exact Nat.blt_eq.mp this
  · intro i hi
    have := allRange_iff.mp hT i hi
    simp only [Bool.and_eq_true, Nat.beq_eq] at this
    exact this

/-- Check a list of symmetries against the list of their actions on the high variables. -/
noncomputable def checkSyms (P : Problem) (b : ℕ) : List Sym → List (List ℕ × List ℕ) → Bool
  | [], [] => true
  | S :: Ss, e :: es => P.checkSym b S e && checkSyms P b Ss es
  | _, _ => false

theorem checkSyms_spec {b : ℕ} : ∀ {syms : List Sym} {perms : List (List ℕ × List ℕ)},
    P.checkSyms b syms perms = true → ∀ e ∈ perms, ∃ S, P.checkSym b S e = true
  | [], [], _, e, he => by simp at he
  | S :: Ss, e' :: es, h, e, he => by
    rw [checkSyms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨S, h.1⟩
    · exact checkSyms_spec h.2 e he'
  | [], _ :: _, h, _, _ => by simp [checkSyms] at h
  | _ :: _, [], h, _, _ => by simp [checkSyms] at h

/-- Proofs of the values of the listed leaves. -/
def LiveProofs (P : Problem) (b : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | e :: es => P.leaf b e.1 = e.2 ∧ LiveProofs P b es

theorem LiveProofs.nil {b : ℕ} : LiveProofs P b [] := trivial

theorem LiveProofs.cons {b α v : ℕ} {es : List (ℕ × ℕ)} (h : P.leaf b α = v)
    (hs : LiveProofs P b es) : LiveProofs P b ((α, v) :: es) := ⟨h, hs⟩

/-- Evaluate the weighted sum of the leaves of a segment of orbit minima `(α, m)`: an entry with
evidence `0` takes its value from the next element of `live`, an entry with evidence `x + 1` is
checked to vanish because of the quadruple with code `x`. The result must be `W`. -/
noncomputable def checkEv (P : Problem) (b : ℕ) :
    List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], [], [], acc, W => Nat.beq acc W
  | e :: seg, 0 :: ev, l :: live, acc, W =>
    Nat.beq e.1 l.1 && checkEv P b seg ev live (Nat.add acc (Nat.mul e.2 l.2)) W
  | e :: seg, (x + 1) :: ev, live, acc, W =>
    Nat.blt e.1 (2 ^ (P.V - b)) && (P.deadAt b e.1 x && checkEv P b seg ev live acc W)
  | _, _, _, _, _ => false

theorem checkEv_spec (hcheck : P.check = true) (hrows : P.checkRows = true) {b : ℕ} :
    ∀ {seg : List (ℕ × ℕ)} {ev : List ℕ} {live : List (ℕ × ℕ)} {acc W : ℕ},
      P.checkEv b seg ev live acc W = true → LiveProofs P b live →
      acc + (seg.map fun e => e.2 * P.leaf b e.1).sum = W
  | [], [], [], acc, W, h, _ => by
    rw [checkEv, Nat.beq_eq] at h
    simpa using h
  | e :: seg, 0 :: ev, l :: live, acc, W, h, hl => by
    rw [checkEv, Bool.and_eq_true, Nat.beq_eq] at h
    have ih := checkEv_spec hcheck hrows h.2 hl.2
    rw [List.map_cons, List.sum_cons, h.1, hl.1, ← Nat.add_assoc]
    exact ih
  | e :: seg, (x + 1) :: ev, live, acc, W, h, hl => by
    rw [checkEv, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := checkEv_spec hcheck hrows h.2.2 hl
    rw [List.map_cons, List.sum_cons, leaf_dead hcheck hrows h.1 h.2.1, Nat.mul_zero, Nat.zero_add]
    exact ih
  | [], [], _ :: _, _, _, h, _ => by simp [checkEv] at h
  | [], _ :: _, _, _, _, h, _ => by simp [checkEv] at h
  | _ :: _, [], _, _, _, h, _ => by simp [checkEv] at h
  | _ :: _, 0 :: _, [], _, _, h, _ => by simp [checkEv] at h

end Problem

end RACert
