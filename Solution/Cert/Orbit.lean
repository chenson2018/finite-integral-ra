/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Prim
public import Solution.Cert.Bits

/-!
# Sums over orbit representatives of a group of bit permutations

Fix `t`. A *bit permutation* is given by two lists `(p, q)` describing inverse permutations of
`[0, t)`; it acts on the numbers below `2 ^ t` by moving bit `i` to position `p[i]`
(`RACert.actBits`). For a finite group of bit permutations, given as a list `perms` with a
multiplication table and a list of inverses (`RACert.checkBitGroup`), and a function `F` that is
invariant under the group, the sum of `F` over `[0, 2 ^ t)` is the sum of `F` over the minima of
the orbits, weighted by the orbit sizes.

The list of orbit minima is certified in segments: `RACert.checkSeg` checks by computation that
the listed numbers in `[lo, hi)` are minima of their orbits and computes the orbit sizes by
orbit–stabilizer, `RACert.OrbitSeg` is the resulting proposition, `RACert.OrbitSeg.append` glues
adjacent segments, and `RACert.OrbitSeg.sum_eq` is the final identity: no completeness check of
the list of minima is needed beyond the total of the orbit sizes being `2 ^ t`.

The definitions on the hot path (`actBits`, `checkSeg`) are written with recursors and the raw
functions `Nat.lor`, `Nat.shiftLeft`, ... for fast kernel reduction.
-/

@[expose] public section

namespace RACert

/-! ### List access -/

theorem nth_eq_getElem {α : Type} (d : α) {l : List α} {i : ℕ} (h : i < l.length) :
    nth d l i = l[i] := by
  rw [nth_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem nth_mem {α : Type} (d : α) {l : List α} {i : ℕ} (h : i < l.length) : nth d l i ∈ l := by
  rw [nth_eq_getElem d h]
  exact List.getElem_mem h

theorem nth_tail (l : List ℕ) (i : ℕ) : nth 0 l.tail i = nth 0 l (i + 1) := by
  cases l <;> rfl

theorem countP_eq_card_filter_range {α : Type} (d : α) (p : α → Bool) (l : List α) :
    l.countP p = ((Finset.range l.length).filter fun i => p (nth d l i) = true).card := by
  rw [Finset.card_filter]
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.countP_cons, List.length_cons, Finset.sum_range_succ', ih]
    rfl

/-! ### Orbit sums for a finite group acting on `[0, B)` -/

/-- The maps `g 0, …, g (N - 1)` form a group of permutations of `[0, B)`, listed without
repetition. -/
structure IsActGroup (N B : ℕ) (g : ℕ → ℕ → ℕ) : Prop where
  /-- The group is nonempty. -/
  pos : 0 < N
  /-- The maps preserve `[0, B)`. -/
  act_lt : ∀ i < N, ∀ α < B, g i α < B
  /-- The first map is the identity. -/
  one_act : ∀ α < B, g 0 α = α
  /-- The maps are closed under composition. -/
  mul : ∀ i < N, ∀ j < N, ∃ c < N, ∀ α < B, g c α = g i (g j α)
  /-- The maps are closed under inverses. -/
  inv : ∀ i < N, ∃ c < N, ∀ α < B, g c (g i α) = α
  /-- The maps are pairwise distinct. -/
  inj : ∀ i < N, ∀ j < N, (∀ α < B, g i α = g j α) → i = j

/-- The orbit of `α`. -/
def actOrbit (N : ℕ) (g : ℕ → ℕ → ℕ) (α : ℕ) : Finset ℕ :=
  (Finset.range N).image fun i => g i α

/-- The indices of the maps fixing `α`. -/
def actStab (N : ℕ) (g : ℕ → ℕ → ℕ) (α : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun i => g i α = α

namespace IsActGroup

variable {N B : ℕ} {g : ℕ → ℕ → ℕ}

theorem act_inj (h : IsActGroup N B g) {i : ℕ} (hi : i < N) {x y : ℕ} (hx : x < B) (hy : y < B)
    (e : g i x = g i y) : x = y := by
  obtain ⟨c, _, hc⟩ := h.inv i hi
  rw [← hc x hx, e, hc y hy]

theorem mul_cancel (h : IsActGroup N B g) {i j j' c : ℕ} (hi : i < N) (hj : j < N) (hj' : j' < N)
    (hc : ∀ α < B, g c α = g i (g j α)) (hc' : ∀ α < B, g c α = g i (g j' α)) : j = j' :=
  h.inj j hj j' hj' fun α hα =>
    h.act_inj hi (h.act_lt j hj α hα) (h.act_lt j' hj' α hα) (by rw [← hc α hα, hc' α hα])

theorem orbit_subset (h : IsActGroup N B g) {α : ℕ} (hα : α < B) :
    actOrbit N g α ⊆ Finset.range B := by
  intro β hβ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
  exact Finset.mem_range.mpr (h.act_lt i (Finset.mem_range.mp hi) α hα)

/-- All fibers of `i ↦ g i α` have the size of the stabilizer. -/
theorem card_fiber (h : IsActGroup N B g) {α : ℕ} (hα : α < B) {j : ℕ} (hj : j < N) :
    ((Finset.range N).filter fun i => g i α = g j α).card = (actStab N g α).card := by
  obtain ⟨k, hk, hkact⟩ := h.inv j hj
  apply le_antisymm
  · have hmul := h.mul k hk
    choose! m hm hmact using hmul
    refine Finset.card_le_card_of_injOn m ?_ ?_
    · intro i hi
      simp only [actStab, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      exact ⟨hm i hi.1, by rw [hmact i hi.1 α hα, hi.2, hkact α hα]⟩
    · intro i hi i' hi' e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hi'
      exact h.mul_cancel hk hi.1 hi'.1 (hmact i hi.1) (by rw [e]; exact hmact i' hi'.1)
  · have hmul := h.mul j hj
    choose! m hm hmact using hmul
    refine Finset.card_le_card_of_injOn m ?_ ?_
    · intro i hi
      simp only [actStab, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      exact ⟨hm i hi.1, by rw [hmact i hi.1 α hα, hi.2]⟩
    · intro i hi i' hi' e
      simp only [actStab, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hi'
      exact h.mul_cancel hj hi.1 hi'.1 (hmact i hi.1) (by rw [e]; exact hmact i' hi'.1)

/-- Orbit–stabilizer. -/
theorem card_orbit_mul_card_stab (h : IsActGroup N B g) {α : ℕ} (hα : α < B) :
    (actOrbit N g α).card * (actStab N g α).card = N := by
  have h1 := Finset.card_eq_sum_card_image (fun i => g i α) (Finset.range N)
  have h2 : ∀ β ∈ (Finset.range N).image (fun i => g i α),
      ((Finset.range N).filter fun i => g i α = β).card = (actStab N g α).card := by
    intro β hβ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hβ
    exact h.card_fiber hα (Finset.mem_range.mp hj)
  rw [Finset.sum_const_nat h2, Finset.card_range] at h1
  exact h1.symm

/-- If the orbits of `α` and `α'` meet and `α` is the minimum of its orbit, then `α ≤ α'`. -/
theorem le_of_orbit_inter (h : IsActGroup N B g) {α α' : ℕ} (hα : α < B) (hα' : α' < B)
    (hmin : ∀ i < N, α ≤ g i α) {i j : ℕ} (hi : i < N) (hj : j < N) (e : g i α = g j α') :
    α ≤ α' := by
  obtain ⟨k, hk, hkact⟩ := h.inv j hj
  obtain ⟨c, hc, hcact⟩ := h.mul k hk i hi
  have h1 : g c α = α' := by rw [hcact α hα, e, hkact α' hα']
  rw [← h1]
  exact hmin c hc

/-- The union of the orbits of a list of distinct orbit minima. -/
theorem exists_union (h : IsActGroup N B g) {F : ℕ → ℕ}
    (hF : ∀ i < N, ∀ α < B, F (g i α) = F α) :
    ∀ seg : List (ℕ × ℕ), seg.Pairwise (fun a b => a.1 < b.1) →
      (∀ e ∈ seg, e.1 < B ∧ (∀ i < N, e.1 ≤ g i e.1) ∧ e.2 * (actStab N g e.1).card = N) →
      ∃ U : Finset ℕ, U ⊆ Finset.range B ∧ (∀ β ∈ U, ∃ e ∈ seg, β ∈ actOrbit N g e.1) ∧
        U.card = (seg.map Prod.snd).sum ∧ ∑ β ∈ U, F β = (seg.map fun e => e.2 * F e.1).sum
  | [], _, _ => ⟨∅, by simp⟩
  | e :: seg, hp, hall => by
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.mp hp
    obtain ⟨U, hU1, hU2, hU3, hU4⟩ :=
      h.exists_union hF seg hp2 fun e' he' => hall e' (List.mem_cons_of_mem _ he')
    obtain ⟨hα, hmin, hm⟩ := hall e List.mem_cons_self
    have hcard : (actOrbit N g e.1).card = e.2 := by
      have h1 := h.card_orbit_mul_card_stab hα
      have hpos : 0 < (actStab N g e.1).card := by
        rcases Nat.eq_zero_or_pos (actStab N g e.1).card with h0 | h0
        · rw [h0, Nat.mul_zero] at h1
          exact absurd h1.symm (Nat.pos_iff_ne_zero.mp h.pos)
        · exact h0
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans hm.symm)
    have hdisj : Disjoint (actOrbit N g e.1) U := by
      rw [Finset.disjoint_left]
      intro β hβ hβU
      obtain ⟨e', he', hβ'⟩ := hU2 β hβU
      obtain ⟨hα', hmin', _⟩ := hall e' (List.mem_cons_of_mem _ he')
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
      obtain ⟨j, hj, e2⟩ := Finset.mem_image.mp hβ'
      rw [Finset.mem_range] at hi hj
      have h1 : e'.1 ≤ e.1 := h.le_of_orbit_inter hα' hα hmin' hj hi e2
      have h2 : e.1 < e'.1 := hp1 e' he'
      omega
    refine ⟨actOrbit N g e.1 ∪ U, ?_, ?_, ?_, ?_⟩
    · exact Finset.union_subset (h.orbit_subset hα) hU1
    · intro β hβ
      rcases Finset.mem_union.mp hβ with hβ | hβ
      · exact ⟨e, List.mem_cons_self, hβ⟩
      · obtain ⟨e', he', hβ'⟩ := hU2 β hβ
        exact ⟨e', List.mem_cons_of_mem _ he', hβ'⟩
    · rw [Finset.card_union_of_disjoint hdisj, hcard, hU3, List.map_cons, List.sum_cons]
    · rw [Finset.sum_union hdisj, hU4, List.map_cons, List.sum_cons,
        Finset.sum_const_nat (m := F e.1), hcard]
      intro β hβ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
      exact hF i (Finset.mem_range.mp hi) e.1 hα

/-- A sum of an invariant function is a weighted sum over the minima of the orbits; the list of
minima is complete as soon as the orbit sizes add up to `B`. -/
theorem sum_eq (h : IsActGroup N B g) {F : ℕ → ℕ} (hF : ∀ i < N, ∀ α < B, F (g i α) = F α)
    {seg : List (ℕ × ℕ)} (hp : seg.Pairwise (fun a b => a.1 < b.1))
    (hall : ∀ e ∈ seg, e.1 < B ∧ (∀ i < N, e.1 ≤ g i e.1) ∧ e.2 * (actStab N g e.1).card = N)
    (hM : (seg.map Prod.snd).sum = B) :
    ∑ α ∈ Finset.range B, F α = (seg.map fun e => e.2 * F e.1).sum := by
  obtain ⟨U, hU1, _, hU3, hU4⟩ := h.exists_union hF seg hp hall
  have hU : U = Finset.range B :=
    Finset.eq_of_subset_of_card_le hU1 (by rw [Finset.card_range, hU3, hM])
  rw [← hU, hU4]

end IsActGroup

/-! ### Bit permutations -/

/-- `p` and `q` are inverse permutations of `[0, t)`. -/
noncomputable def checkBitPerm (t : ℕ) (p q : List ℕ) : Bool :=
  allRange t fun i => Nat.blt (nth 0 p i) t && (Nat.blt (nth 0 q i) t &&
    (Nat.beq (nth 0 q (nth 0 p i)) i && Nat.beq (nth 0 p (nth 0 q i)) i))

theorem checkBitPerm_spec {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) {i : ℕ}
    (hi : i < t) :
    nth 0 p i < t ∧ nth 0 q i < t ∧ nth 0 q (nth 0 p i) = i ∧ nth 0 p (nth 0 q i) = i := by
  have h1 := allRange_iff.mp h i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  exact h1

/-- The loop of `actBits`: move the lowest `n` bits of `α` to the positions listed in `p`
(position `0` beyond the end of `p`), accumulating into `acc`. -/
noncomputable def actAux (n : ℕ) : List ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih p α acc =>
      List.rec (motive := fun _ => ℕ)
        (ih [] (Nat.shiftRight α 1) (Nat.lor acc (Nat.land α 1)))
        (fun x xs _ =>
          ih xs (Nat.shiftRight α 1) (Nat.lor acc (Nat.shiftLeft (Nat.land α 1) x))) p) n

theorem actAux_zero (p : List ℕ) (α acc : ℕ) : actAux 0 p α acc = acc := rfl

theorem actAux_succ (n : ℕ) (p : List ℕ) (α acc : ℕ) :
    actAux (n + 1) p α acc = actAux n p.tail (α >>> 1) (acc ||| ((α &&& 1) <<< nth 0 p 0)) := by
  cases p <;> rfl

theorem testBit_actAux : ∀ (n : ℕ) (p : List ℕ) (α acc j : ℕ),
    (actAux n p α acc).testBit j = true ↔
      acc.testBit j = true ∨ ∃ i < n, nth 0 p i = j ∧ α.testBit i = true
  | 0, p, α, acc, j => by simp [actAux_zero]
  | n + 1, p, α, acc, j => by
    rw [actAux_succ, testBit_actAux n, Nat.exists_lt_succ_left, Nat.testBit_or, Bool.or_eq_true,
      or_assoc]
    refine or_congr Iff.rfl (or_congr ?_ (exists_congr fun i => and_congr Iff.rfl ?_))
    · rcases Nat.mod_two_eq_zero_or_one α with h | h
      · simp [Nat.testBit_zero, h]
      · simp only [Nat.and_one_is_mod, h, Nat.testBit_shiftLeft, ge_iff_le, Bool.and_eq_true,
          decide_eq_true_iff, Nat.testBit_one_eq_true_iff_self_eq_zero, Nat.testBit_zero,
          and_true]
        omega
    · rw [nth_tail, Nat.testBit_shiftRight, Nat.add_comm]

/-- Move bit `i` of `α` to position `p[i]`, for `i < t`. -/
noncomputable def actBits (t : ℕ) (p : List ℕ) (α : ℕ) : ℕ := actAux t p α 0

theorem testBit_actBits {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) (α j : ℕ) :
    (actBits t p α).testBit j = (decide (j < t) && α.testBit (nth 0 q j)) := by
  rw [Bool.eq_iff_iff, actBits, testBit_actAux, Bool.and_eq_true, decide_eq_true_iff]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨i, hi, rfl, hα⟩
    obtain ⟨h1, _, h3, _⟩ := checkBitPerm_spec h hi
    exact ⟨h1, by rw [h3]; exact hα⟩
  · rintro ⟨hj, hα⟩
    obtain ⟨_, h2, _, h4⟩ := checkBitPerm_spec h hj
    exact ⟨nth 0 q j, h2, h4, hα⟩

theorem actBits_lt {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) (α : ℕ) :
    actBits t p α < 2 ^ t :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_actBits h, decide_eq_false (Nat.not_lt.mpr hi), Bool.false_and]

theorem testBit_eq_false_of_lt {α t j : ℕ} (hα : α < 2 ^ t) (hj : ¬ j < t) :
    α.testBit j = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hα (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hj)))

/-! ### Groups of bit permutations -/

/-- The forward list of the `i`-th permutation. -/
noncomputable def pAt (perms : List (List ℕ × List ℕ)) (i : ℕ) : List ℕ :=
  (nth ([], []) perms i).1

/-- The backward list of the `i`-th permutation. -/
noncomputable def qAt (perms : List (List ℕ × List ℕ)) (i : ℕ) : List ℕ :=
  (nth ([], []) perms i).2

/-- The first `t` entries of `p` as a number in base `t`, most significant digit first. For lists
with entries below `t`, comparing codes is comparing the first `t` entries lexicographically. -/
noncomputable def permCode (t : ℕ) (p : List ℕ) : ℕ :=
  ((List.range t).map (nth 0 p)).foldl (fun acc d => Nat.add (Nat.mul acc t) d) 0

theorem permCode_congr {t : ℕ} {p p' : List ℕ} (h : ∀ x < t, nth 0 p x = nth 0 p' x) :
    permCode t p = permCode t p' := by
  unfold permCode
  rw [List.map_congr_left fun x hx => h x (List.mem_range.mp hx)]

/-- `a < l[0] < l[1] < …`. -/
def increasingFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: l => Nat.blt a b && increasingFrom b l

/-- `l[0] < l[1] < …`. -/
def increasing : List ℕ → Bool
  | [] => true
  | a :: l => increasingFrom a l

theorem increasingFrom_spec : ∀ {a : ℕ} {l : List ℕ}, increasingFrom a l = true →
    (∀ x ∈ l, a < x) ∧ l.Pairwise (· < ·)
  | _, [], _ => by simp
  | a, b :: l, h => by
    rw [increasingFrom, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := increasingFrom_spec h.2
    refine ⟨fun x hx => ?_, List.pairwise_cons.mpr ⟨h1, h2⟩⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (h1 x hx)

theorem increasing_spec {l : List ℕ} (h : increasing l = true) : l.Pairwise (· < ·) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a l =>
    obtain ⟨h1, h2⟩ := increasingFrom_spec (a := a) (l := l) h
    exact List.pairwise_cons.mpr ⟨h1, h2⟩

/-- `f l[j] r[j]` for all `j < l.length` (with `r[j] = d` beyond the end of `r`). -/
def allZip {α β : Type} (d : β) (f : α → β → Bool) : List α → List β → Bool
  | [], _ => true
  | a :: l, r => f a (r.headD d) && allZip d f l r.tail

theorem allZip_spec {α β : Type} (d' : α) (d : β) {f : α → β → Bool} :
    ∀ {l : List α} {r : List β}, allZip d f l r = true →
      ∀ j < l.length, f (nth d' l j) (nth d r j) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | a :: l, r, h, j, hj => by
    rw [allZip, Bool.and_eq_true] at h
    cases j with
    | zero => cases r <;> exact h.1
    | succ j =>
      have h1 := allZip_spec d' d h.2 j (Nat.lt_of_succ_lt_succ hj)
      cases r <;> exact h1

/-- `a[x] = b[c[x]]` for all `x < t`. -/
noncomputable def eqComp (t : ℕ) (a b c : List ℕ) : Bool :=
  allRange t fun x => Nat.beq (nth 0 a x) (nth 0 b (nth 0 c x))

/-- `a[x] = b[x]` for all `x < t`. -/
noncomputable def eqOn (t : ℕ) (a b : List ℕ) : Bool :=
  allRange t fun x => Nat.beq (nth 0 a x) (nth 0 b x)

/-- Group certificate. `perms` is a list of pairs `(p, q)` such that

* every pair consists of inverse permutations of `[0, t)` (`checkBitPerm`);
* `perms` is nonempty and its first entry is the identity;
* the codes `permCode t p` are strictly increasing along the list: the `p`'s are sorted
  strictly lexicographically by their first `t` entries (in particular they are distinct);
* `comp[i][j]` is an index `c` with `p_c[x] = p_i[p_j[x]]` for all `x < t`;
* `inv[i]` is an index `c` with `p_c[x] = q_i[x]` for all `x < t`. -/
noncomputable def checkBitGroup (t : ℕ) (perms : List (List ℕ × List ℕ)) (comp : List (List ℕ))
    (inv : List ℕ) : Bool :=
  perms.all (fun e => checkBitPerm t e.1 e.2) &&
  (Nat.blt 0 perms.length &&
  ((allRange t fun x => Nat.beq (nth 0 (pAt perms 0) x) x) &&
  (increasing (perms.map fun e => permCode t e.1) &&
  (allZip [] (fun ei row => allZip 0 (fun ej c =>
      Nat.blt c perms.length && eqComp t (pAt perms c) ei.1 ej.1) perms row) perms comp &&
  allZip 0 (fun ei c => Nat.blt c perms.length && eqOn t (pAt perms c) ei.2) perms inv))))

theorem checkBitGroup_spec {t : ℕ} {perms : List (List ℕ × List ℕ)} {comp : List (List ℕ)}
    {inv : List ℕ} (h : checkBitGroup t perms comp inv = true) :
    (∀ i < perms.length, checkBitPerm t (pAt perms i) (qAt perms i) = true) ∧
    0 < perms.length ∧
    (∀ x < t, nth 0 (pAt perms 0) x = x) ∧
    (∀ i < perms.length, ∀ j < perms.length,
      (∀ x < t, nth 0 (pAt perms i) x = nth 0 (pAt perms j) x) → i = j) ∧
    (∀ i < perms.length, ∀ j < perms.length, ∃ c < perms.length,
      ∀ x < t, nth 0 (pAt perms c) x = nth 0 (pAt perms i) (nth 0 (pAt perms j) x)) ∧
    (∀ i < perms.length, ∃ c < perms.length,
      ∀ x < t, nth 0 (pAt perms c) x = nth 0 (qAt perms i) x) := by
  simp only [checkBitGroup, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun i hi => ?_, Nat.blt_eq.mp h2, fun x hx => ?_, fun i hi j hj e => ?_,
    fun i hi j hj => ?_, fun i hi => ?_⟩
  · exact List.all_eq_true.mp h1 _ (nth_mem _ hi)
  · exact Nat.beq_eq.mp (allRange_iff.mp h3 x hx)
  · have hpw := List.pairwise_iff_getElem.mp (List.pairwise_map.mp (increasing_spec h4))
    have hcode : permCode t (pAt perms i) = permCode t (pAt perms j) := permCode_congr e
    rw [pAt, pAt, nth_eq_getElem _ hi, nth_eq_getElem _ hj] at hcode
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd hcode (Nat.ne_of_lt (hpw i j hi hj hij))
    · exact hij
    · exact absurd hcode.symm (Nat.ne_of_lt (hpw j i hj hi hij))
  · have h7 := allZip_spec ([], []) 0 (allZip_spec ([], []) [] h5 i hi) j hj
    rw [Bool.and_eq_true, Nat.blt_eq] at h7
    exact ⟨_, h7.1, fun x hx => Nat.beq_eq.mp (allRange_iff.mp h7.2 x hx)⟩
  · have h7 := allZip_spec ([], []) 0 h6 i hi
    rw [Bool.and_eq_true, Nat.blt_eq] at h7
    exact ⟨_, h7.1, fun x hx => Nat.beq_eq.mp (allRange_iff.mp h7.2 x hx)⟩

/-- The action of the `i`-th permutation of the list. -/
noncomputable def bitAct (t : ℕ) (perms : List (List ℕ × List ℕ)) (i α : ℕ) : ℕ :=
  actBits t (pAt perms i) α

theorem isActGroup_of_check {t : ℕ} {perms : List (List ℕ × List ℕ)} {comp : List (List ℕ)}
    {inv : List ℕ} (h : checkBitGroup t perms comp inv = true) :
    IsActGroup perms.length (2 ^ t) (bitAct t perms) := by
  obtain ⟨hperm, hpos, hone, hinj, hmul, hinv⟩ := checkBitGroup_spec h
  refine ⟨hpos, fun i hi α _ => actBits_lt (hperm i hi) α, fun α hα => ?_, fun i hi j hj => ?_,
    fun i hi => ?_, fun i hi j hj e => hinj i hi j hj fun x hx => ?_⟩
  · refine Nat.eq_of_testBit_eq fun y => ?_
    rw [bitAct, testBit_actBits (hperm 0 hpos)]
    by_cases hy : y < t
    · obtain ⟨_, _, h3, _⟩ := checkBitPerm_spec (hperm 0 hpos) hy
      rw [hone y hy] at h3
      rw [h3, decide_eq_true hy, Bool.true_and]
    · rw [decide_eq_false hy, Bool.false_and, testBit_eq_false_of_lt hα hy]
  · obtain ⟨c, hc, hcx⟩ := hmul i hi j hj
    refine ⟨c, hc, fun α _ => Nat.eq_of_testBit_eq fun y => ?_⟩
    rw [bitAct, bitAct, bitAct, testBit_actBits (hperm c hc), testBit_actBits (hperm i hi),
      testBit_actBits (hperm j hj)]
    by_cases hy : y < t
    · obtain ⟨_, i2, _, i4⟩ := checkBitPerm_spec (hperm i hi) hy
      obtain ⟨_, j2, _, j4⟩ := checkBitPerm_spec (hperm j hj) i2
      obtain ⟨_, _, c3, _⟩ := checkBitPerm_spec (hperm c hc) j2
      rw [hcx _ j2, j4, i4] at c3
      rw [c3, decide_eq_true i2, Bool.true_and]
    · rw [decide_eq_false hy, Bool.false_and, Bool.false_and]
  · obtain ⟨c, hc, hcx⟩ := hinv i hi
    refine ⟨c, hc, fun α hα => Nat.eq_of_testBit_eq fun y => ?_⟩
    rw [bitAct, bitAct, testBit_actBits (hperm c hc), testBit_actBits (hperm i hi)]
    by_cases hy : y < t
    · obtain ⟨_, c2, _, c4⟩ := checkBitPerm_spec (hperm c hc) hy
      rw [hcx _ c2] at c4
      rw [c4, decide_eq_true hy, decide_eq_true c2, Bool.true_and, Bool.true_and]
    · rw [decide_eq_false hy, Bool.false_and, testBit_eq_false_of_lt hα hy]
  · obtain ⟨i1, _, i3, _⟩ := checkBitPerm_spec (hperm i hi) hx
    obtain ⟨_, _, _, j4⟩ := checkBitPerm_spec (hperm j hj) i1
    have h1 := congrArg (fun β => β.testBit (nth 0 (pAt perms i) x))
      (e (2 ^ x) (Nat.pow_lt_pow_right (by omega) hx))
    simp only [bitAct, testBit_actBits (hperm i hi), testBit_actBits (hperm j hj),
      Nat.testBit_two_pow, i3, decide_eq_true i1, Bool.true_and, decide_true] at h1
    rw [← of_decide_eq_true h1.symm] at j4
    exact j4.symm

/-! ### Certified segments of orbit minima -/

/-- `α` is the minimum of its orbit, and the orbit has `m` elements (by orbit–stabilizer: `m`
times the number of permutations fixing `α` is the order of the group). -/
def IsRep (t : ℕ) (perms : List (List ℕ × List ℕ)) (α m : ℕ) : Prop :=
  (∀ e ∈ perms, α ≤ actBits t e.1 α) ∧
    m * perms.countP (fun e => Nat.ble (actBits t e.1 α) α) = perms.length

/-- One step of the loop over the group: fail if the image `img` of `α` is below `α`; count it
if it equals `α`. (A definition rather than an inlined recursor, so that the kernel evaluates
the loop iteratively.) -/
noncomputable def repStep (α img : ℕ) (k : ℕ → Bool) (cnt : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) (k cnt) (k (Nat.succ cnt)) (Nat.ble img α))
    (Nat.ble α img)

/-- The loop over the group: check that no image of `α` is below `α`, count the images equal to
`α`, and compare `m` times the final count with `N`. -/
noncomputable def repLoop (t N α m : ℕ) (perms : List (List ℕ × List ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun cnt => Nat.beq (Nat.mul m cnt) N)
    (fun e _ ih => repStep α (actBits t e.1 α) ih) perms

theorem repLoop_nil (t N α m cnt : ℕ) : repLoop t N α m [] cnt = Nat.beq (Nat.mul m cnt) N := rfl

theorem repLoop_cons (t N α m cnt : ℕ) (e : List ℕ × List ℕ) (l : List (List ℕ × List ℕ)) :
    repLoop t N α m (e :: l) cnt = repStep α (actBits t e.1 α) (repLoop t N α m l) cnt := rfl

theorem repLoop_spec {t N α m : ℕ} : ∀ (l : List (List ℕ × List ℕ)) (cnt : ℕ),
    repLoop t N α m l cnt = true → (∀ e ∈ l, α ≤ actBits t e.1 α) ∧
      m * (cnt + l.countP fun e => Nat.ble (actBits t e.1 α) α) = N
  | [], cnt, h => by
    rw [repLoop_nil, Nat.beq_eq] at h
    exact ⟨by simp, by simpa using h⟩
  | e :: l, cnt, h => by
    rw [repLoop_cons, repStep] at h
    cases h1 : Nat.ble α (actBits t e.1 α) with
    | false =>
      rw [h1] at h
      exact absurd h (by simp)
    | true =>
      rw [h1] at h
      have h1' := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.ble (actBits t e.1 α) α with
      | false =>
        rw [h2] at h
        obtain ⟨ha, hb⟩ := repLoop_spec l cnt h
        refine ⟨fun e' he' => ?_, ?_⟩
        · rcases List.mem_cons.mp he' with rfl | he'
          exacts [h1', ha e' he']
        · rw [List.countP_cons_of_neg (p := fun e : List ℕ × List ℕ => Nat.ble (actBits t e.1 α) α)
            (by rw [h2]; simp)]
          exact hb
      | true =>
        rw [h2] at h
        obtain ⟨ha, hb⟩ := repLoop_spec l (Nat.succ cnt) h
        refine ⟨fun e' he' => ?_, ?_⟩
        · rcases List.mem_cons.mp he' with rfl | he'
          exacts [h1', ha e' he']
        · rw [List.countP_cons_of_pos
            (p := fun e : List ℕ × List ℕ => Nat.ble (actBits t e.1 α) α) h2, ← hb]
          congr 1
          omega

/-- Lazy conjunction of three Booleans. (A definition, so that the kernel evaluates loops going
through it iteratively.) -/
noncomputable def and3 (a b c : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false c b) a

theorem and3_eq_true {a b c : Bool} : and3 a b c = true ↔ a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp [and3]

/-- The loop over a segment: the entries `(α, m)` have strictly increasing `α` in `[lo, hi)`, and
each passes `repLoop`. -/
noncomputable def segLoop (t N hi : ℕ) (perms : List (List ℕ × List ℕ)) (seg : List (ℕ × ℕ)) :
    ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun lo => Nat.ble lo hi)
    (fun e _ ih lo => Prod.rec (motive := fun _ => Bool)
      (fun α m => and3 (Nat.ble lo α) (repLoop t N α m perms 0) (ih (Nat.succ α))) e) seg

theorem segLoop_nil (t N hi lo : ℕ) (perms : List (List ℕ × List ℕ)) :
    segLoop t N hi perms [] lo = Nat.ble lo hi := rfl

theorem segLoop_cons (t N hi lo α m : ℕ) (perms : List (List ℕ × List ℕ)) (seg : List (ℕ × ℕ)) :
    segLoop t N hi perms ((α, m) :: seg) lo =
      and3 (Nat.ble lo α) (repLoop t N α m perms 0) (segLoop t N hi perms seg (Nat.succ α)) := rfl

theorem segLoop_spec {t hi : ℕ} {perms : List (List ℕ × List ℕ)} :
    ∀ (seg : List (ℕ × ℕ)) (lo : ℕ), segLoop t perms.length hi perms seg lo = true →
      lo ≤ hi ∧ seg.Pairwise (fun a b => a.1 < b.1) ∧
        ∀ e ∈ seg, lo ≤ e.1 ∧ e.1 < hi ∧ IsRep t perms e.1 e.2
  | [], lo, h => ⟨Nat.le_of_ble_eq_true h, List.Pairwise.nil, by simp⟩
  | (α, m) :: seg, lo, h => by
    rw [segLoop_cons, and3_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨g1, g2, g3⟩ := segLoop_spec seg _ h3
    have hlo : lo ≤ α := Nat.le_of_ble_eq_true h1
    have hrep : IsRep t perms α m := by
      have h4 := repLoop_spec perms 0 h2
      rw [Nat.zero_add] at h4
      exact h4
    refine ⟨Nat.le_trans hlo (Nat.le_of_succ_le g1),
      List.pairwise_cons.mpr ⟨fun e he => (g3 e he).1, g2⟩, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hlo, g1, hrep⟩
    · exact ⟨Nat.le_trans hlo (Nat.le_of_succ_le (g3 e he).1), (g3 e he).2⟩

/-- Segment check. `seg` lists pairs `(α, m)`. Checks: `lo ≤ hi ≤ 2 ^ t`; the `α`'s are strictly
increasing and lie in `[lo, hi)`; each `α` is the minimum of its orbit (`α ≤ actBits t p α` for
every `p` in `perms`); and `m` times the number of `p` in `perms` fixing `α` is `perms.length`
(so that `m` is the size of the orbit). -/
noncomputable def checkSeg (t : ℕ) (perms : List (List ℕ × List ℕ)) (lo hi : ℕ)
    (seg : List (ℕ × ℕ)) : Bool :=
  and3 (Nat.ble hi (Nat.pow 2 t)) (Nat.ble lo hi) (segLoop t perms.length hi perms seg lo)

/-- A certified part of an orbit sum: there is a list of orbit minima in `[lo, hi)`, with their
orbit sizes, with total orbit size `M` and weighted sum `W`. -/
def OrbitSeg (t : ℕ) (perms : List (List ℕ × List ℕ)) (F : ℕ → ℕ) (lo hi M W : ℕ) : Prop :=
  lo ≤ hi ∧ hi ≤ 2 ^ t ∧ ∃ seg : List (ℕ × ℕ), seg.Pairwise (fun a b => a.1 < b.1) ∧
    (∀ e ∈ seg, lo ≤ e.1 ∧ e.1 < hi ∧ IsRep t perms e.1 e.2) ∧
    (seg.map Prod.snd).sum = M ∧ (seg.map fun e => e.2 * F e.1).sum = W

theorem OrbitSeg.of_check {t : ℕ} {perms : List (List ℕ × List ℕ)} {F : ℕ → ℕ} {lo hi : ℕ}
    {seg : List (ℕ × ℕ)} {M W : ℕ} (h : checkSeg t perms lo hi seg = true)
    (hM : (seg.map Prod.snd).sum = M) (hW : (seg.map fun e => e.2 * F e.1).sum = W) :
    OrbitSeg t perms F lo hi M W := by
  rw [checkSeg, and3_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨_, g2, g3⟩ := segLoop_spec seg lo h3
  exact ⟨Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h1, seg, g2, g3, hM, hW⟩

theorem OrbitSeg.append {t : ℕ} {perms : List (List ℕ × List ℕ)} {F : ℕ → ℕ}
    {lo mid hi M₁ W₁ M₂ W₂ : ℕ} (h₁ : OrbitSeg t perms F lo mid M₁ W₁)
    (h₂ : OrbitSeg t perms F mid hi M₂ W₂) : OrbitSeg t perms F lo hi (M₁ + M₂) (W₁ + W₂) := by
  obtain ⟨a1, _, seg₁, p1, r1, m1, w1⟩ := h₁
  obtain ⟨a2, b2, seg₂, p2, r2, m2, w2⟩ := h₂
  refine ⟨Nat.le_trans a1 a2, b2, seg₁ ++ seg₂, ?_, fun e he => ?_, ?_, ?_⟩
  · exact List.pairwise_append.mpr ⟨p1, p2, fun a ha b hb =>
      Nat.lt_of_lt_of_le (r1 a ha).2.1 (r2 b hb).1⟩
  · rcases List.mem_append.mp he with he | he
    · exact ⟨(r1 e he).1, Nat.lt_of_lt_of_le (r1 e he).2.1 a2, (r1 e he).2.2⟩
    · exact ⟨Nat.le_trans a1 (r2 e he).1, (r2 e he).2⟩
  · rw [List.map_append, List.sum_append, m1, m2]
  · rw [List.map_append, List.sum_append, w1, w2]

/-- **Sum over orbit representatives.** If `F` is invariant under the group and the certified
orbits of minima in `[0, 2 ^ t)` have total size `2 ^ t`, then the sum of `F` over `[0, 2 ^ t)`
is the weighted sum over the minima. -/
theorem OrbitSeg.sum_eq {t : ℕ} {perms : List (List ℕ × List ℕ)} {comp : List (List ℕ)}
    {inv : List ℕ} {F : ℕ → ℕ} {W : ℕ} (hgrp : checkBitGroup t perms comp inv = true)
    (hF : ∀ e ∈ perms, ∀ α < 2 ^ t, F (actBits t e.1 α) = F α)
    (h : OrbitSeg t perms F 0 (2 ^ t) (2 ^ t) W) :
    ∑ α ∈ Finset.range (2 ^ t), F α = W := by
  obtain ⟨_, _, seg, hp, hall, hM, hW⟩ := h
  have hG := isActGroup_of_check hgrp
  rw [← hW]
  refine hG.sum_eq (fun i hi α hα => hF _ (nth_mem _ hi) α hα) hp (fun e he => ?_) hM
  obtain ⟨_, hlt, hmin, hcnt⟩ := hall e he
  have hmin' : ∀ i < perms.length, e.1 ≤ bitAct t perms i e.1 :=
    fun i hi => hmin _ (nth_mem _ hi)
  have hst : actStab perms.length (bitAct t perms) e.1 = (Finset.range perms.length).filter
      fun i => Nat.ble (actBits t (nth ([], []) perms i).1 e.1) e.1 = true := by
    refine Finset.filter_congr fun i hi => ?_
    have h1 := hmin' i (Finset.mem_range.mp hi)
    rw [Nat.ble_eq]
    exact ⟨fun h2 => Nat.le_of_eq h2, fun h2 => Nat.le_antisymm h2 h1⟩
  refine ⟨hlt, hmin', ?_⟩
  rw [hst, ← countP_eq_card_filter_range ([], []) (fun e' => Nat.ble (actBits t e'.1 e.1) e.1)]
  exact hcnt

end RACert
