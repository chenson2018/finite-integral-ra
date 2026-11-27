/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Split

/-!
# Projecting product rows

Each bit position denotes a choice of the middle rows. Lower and upper columns
bound each remaining cycle in every model at that position. If a particular
value of a cycle makes a quadruple impossible, remove that value from its
domain. Different quadruples can thereby force incompatible values of a cycle.
-/

@[expose] public section
namespace RACert.Problem

abbrev Bounds := ℕ → ℕ × ℕ

def initialBounds (k d H : ℕ) : Bounds :=
  fun c => (boundCol k d H false c, boundCol k d H true c)

def bounded (A : Bounds) (i : ℕ) (v : ℕ → Bool) :=
  ∀ c, ((A c).1.testBit i = true → litB v c = true) ∧
    (litB v c = true → (A c).2.testBit i = true)

theorem initial_bounded {i d : ℕ} (hi : i < 2 ^ d) (k H : ℕ) (w : Fin k → Bool) :
    bounded (initialBounds k d H) i (join k (i + 2 ^ d * H) w) := by
  intro c
  simp only [initialBounds, boundCol_bit hi]
  match c with
  | 0 | 1 => simp [litB]
  | j + 2 => simp only [litB, join]; split <;> simp

/-- Middle assignments on which this quadruple has disjoint witness bounds. -/
noncomputable def rowBad (P : Problem) (d : ℕ) (A : Bounds) (x : ℕ) : ℕ :=
  let r := x / P.k / P.k / P.k % P.k
  let u := x / P.k / P.k % P.k
  let t := x / P.k % P.k
  let p := x % P.k
  let bad (a b c e f g h j : ℕ) :=
    Nat.land (dotBits P (fun i => (A i).1) a b c e)
      (Nat.xor (ones d) (dotBits P (fun i => (A i).2) f g h j))
  Nat.lor (bad (cvN P.s r) p u t r u p (cvN P.s t))
    (bad r u p (cvN P.s t) (cvN P.s r) p u t)

theorem rowBad_sound {P : Problem} (hc : P.check = true) {v : ℕ → Bool}
    (hv : P.phi v = true) {A : Bounds} {i d : ℕ} (hi : i < 2 ^ d) (ha : bounded A i v)
    (x : ℕ) : (rowBad P d A x).testBit i = false := by
  have bounds (a b c e : ℕ) :
      ((dotBits P (fun c => (A c).1) a b c e).testBit i = true →
        dotB P.k (P.tbl v) a b c e = true) ∧
      (dotB P.k (P.tbl v) a b c e = true →
        (dotBits P (fun c => (A c).2) a b c e).testBit i = true) := by
    simp only [dotBits, unionBits_bit, testBit_land, List.any_eq_true, List.mem_range,
      Bool.and_eq_true, dotB_iff]
    constructor
    · rintro ⟨q,hq,hl,hr⟩
      exact ⟨q,hq,(ha _).1 hl,(ha _).1 hr⟩
    · rintro ⟨q,hq,hl,hr⟩
      exact ⟨q,hq,(ha _).2 hl,(ha _).2 hr⟩
  have eq := quadAt_of_phi hc hv x
  rw [quadAt, quadB, beq_iff_eq] at eq
  simp only [rowBad, testBit_lor, testBit_land, testBit_xor, testBit_ones, hi, decide_true,
    Bool.true_xor]
  apply Bool.eq_false_iff.mpr
  intro bad
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at bad
  rcases bad with ⟨h, hn⟩ | ⟨h, hn⟩
  · have h' := (bounds _ _ _ _).1 h
    rw [eq] at h'
    simp [(bounds _ _ _ _).2 h'] at hn
  · have h' := (bounds _ _ _ _).1 h
    rw [← eq] at h'
    simp [(bounds _ _ _ _).2 h'] at hn

/-- Probe a cycle at a fixed value; the result is valid on models having that value. -/
def pin (A : Bounds) (c z : ℕ) : Bounds := fun j => if j == c then (z,z) else A j

private theorem pin_bounded {A : Bounds} {i c z : ℕ} {v : ℕ → Bool} (h : bounded A i v)
    (he : z.testBit i = litB v c) : bounded (pin A c z) i v := by
  intro j
  by_cases hj : j = c
  · subst j; simp [pin, he]
  · simpa [pin, hj] using h j

/-- For a single product - row bit, each list witnesses impossible assignments under
one of its two possible values. A model must survive at least one list. -/
abbrev RowProbe := ℕ × List ℕ × List ℕ

noncomputable def probeBad (P : Problem) (d : ℕ) (A : Bounds) (p : RowProbe) : ℕ :=
  Nat.land (unionBits (rowBad P d (pin A p.1 0)) p.2.1)
    (unionBits (rowBad P d (pin A p.1 (ones d))) p.2.2)

theorem probeBad_sound {P : Problem} (hc : P.check = true) {v : ℕ → Bool}
    (hv : P.phi v = true) {A : Bounds} {i d : ℕ} (hi : i < 2 ^ d) (ha : bounded A i v)
    (p : RowProbe) : (probeBad P d A p).testBit i = false := by
  simp only [probeBad, testBit_land, unionBits_bit]
  cases he : litB v p.1 with
  | false =>
    have hp := pin_bounded (c := p.1) (z := 0) ha (by simp [he])
    simp [List.any_eq_false, rowBad_sound hc hv hi hp]
  | true =>
    have hp := pin_bounded (c := p.1) (z := ones d) ha (by simp [he, testBit_ones, hi])
    simp [List.any_eq_false, rowBad_sound hc hv hi hp]

noncomputable def projectedRows (P : Problem) (k d H : ℕ) (xs : List ℕ) (ps : List RowProbe) : ℕ :=
  let extra := ps.foldr (fun p acc => Nat.lor (probeBad P d (initialBounds k d H) p) acc) 0
  Nat.land (P.splitMask k d H xs) (Nat.xor (ones d) extra)

theorem coversProjected {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k d H mask : ℕ} (hk : k + d ≤ P.V) (hH : H < 2 ^ (P.V - (k + d)))
    {xs : List ℕ} {ps : List RowProbe} (he : P.projectedRows k d H xs ps = mask) :
    P.CoversSplit k d H mask := by
  intro i hi hm
  rw [← he, projectedRows, testBit_land] at hm
  cases hs : (P.splitMask k d H xs).testBit i with
  | false => exact coversSplit hc hr hk hH rfl i hi hs
  | true =>
    rw [leaf_eq hr (inner_lt hk hH hi), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _ hv
    have ha := initial_bounded hi k H w
    have hz (ps : List RowProbe) :
        (ps.foldr (fun p acc => Nat.lor (probeBad P d (initialBounds k d H) p) acc) 0).testBit i
          = false := by
      induction ps with
      | nil => exact Nat.zero_testBit _
      | cons p ps ih =>
        rw [List.foldr_cons, testBit_lor, ih, probeBad_sound hc hv hi ha]
        rfl
    rw [hs, testBit_xor, testBit_ones, hz] at hm
    simp [hi] at hm

/-- A representative has weight zero, one or two. The masks are shared by all
outer cycle sets stabilized by the same row permutation. -/
def rowWeight (keep twice i : ℕ) : ℕ :=
  (keep.testBit i).toNat + (twice.testBit i).toNat

def BalancedRows (d keep twice : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ i < 2 ^ d, g i < 2 ^ d ∧ g (g i) = i ∧
    rowWeight keep twice i + rowWeight keep twice (g i) = 2

noncomputable def checkBalanced (d keep twice : ℕ) (g : ℕ → ℕ) : Bool :=
  allRange (2 ^ d) fun i => Nat.blt (g i) (2 ^ d) && (Nat.beq (g (g i)) i &&
    Nat.beq (rowWeight keep twice i + rowWeight keep twice (g i)) 2)

theorem balancedRows_of_check {d keep twice : ℕ} {g : ℕ → ℕ}
    (h : checkBalanced d keep twice g = true) : BalancedRows d keep twice g := by
  simpa only [BalancedRows, checkBalanced, allRange_iff, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] using h

private theorem balanced_sum {d keep twice : ℕ} {g F : ℕ → ℕ} (h : BalancedRows d keep twice g)
    (hf : ∀ i < 2 ^ d, F (g i) = F i) :
    ∑ i ∈ Finset.range (2 ^ d), F i =
      ∑ i ∈ Finset.range (2 ^ d), rowWeight keep twice i * F i := by
  let W i := rowWeight keep twice i * F i
  have perm : ∑ i ∈ Finset.range (2 ^ d), W (g i) = ∑ i ∈ Finset.range (2 ^ d), W i := by
    apply Finset.sum_nbij' g g
    all_goals intro i hi
    all_goals have e := h i (Finset.mem_range.mp hi)
    all_goals first | exact Finset.mem_range.mpr e.1 | exact e.2.1 | rfl
  have dbl : (∑ i ∈ Finset.range (2 ^ d), F i) + (∑ i ∈ Finset.range (2 ^ d), F i) =
      (∑ i ∈ Finset.range (2 ^ d), W i) + (∑ i ∈ Finset.range (2 ^ d), W (g i)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have e := h i (Finset.mem_range.mp hi)
    simp only [W, hf i (Finset.mem_range.mp hi), ← Nat.add_mul, e.2.2, two_mul]
  rw [perm] at dbl
  change _ = ∑ i ∈ Finset.range (2 ^ d), W i
  omega

private theorem act_lor {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) (x y : ℕ) :
    actBits t p (Nat.lor x y) = Nat.lor (actBits t p x) (actBits t p y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_actBits h, testBit_lor]
  cases decide (i < t) <;> simp

private theorem row_lor {d i : ℕ} (hi : i < 2 ^ d) (H : ℕ) :
    Nat.lor i (2 ^ d * H) = i + 2 ^ d * H := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lor, testBit_add_two_pow_mul hi]
  have e := testBit_add_two_pow_mul (β' := 0) (ζ := H) (Nat.two_pow_pos d) j
  simp only [Nat.zero_add, Nat.zero_testBit] at e
  rw [e]
  split_ifs with hj
  · simp
  · rw [Nat.testBit_eq_false_of_lt (hi.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

/-- An atom symmetry may be used inside a fibre exactly when it fixes its outer assignment. -/
theorem row_invariant {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k d H : ℕ} (hk : k + d ≤ P.V) (hH : H < 2 ^ (P.V - (k + d)))
    {S : Sym} {e : List ℕ × List ℕ} (hs : P.checkSym k S e = true)
    (hp : checkBitPerm (P.V - k) e.1 e.2 = true)
    (fixH : actBits (P.V - k) e.1 (2 ^ d * H) = 2 ^ d * H)
    {i : ℕ} (hi : i < 2 ^ d) (hg : actBits (P.V - k) e.1 i < 2 ^ d) :
    P.leaf k (2 ^ d * H + actBits (P.V - k) e.1 i) = P.leaf k (2 ^ d * H + i) := by
  have eq := leaf_actBits hc hr (show k ≤ P.V by omega) hs hp (inner_lt hk hH hi)
  rw [← row_lor hi, act_lor hp, fixH, row_lor hg, row_lor hi] at eq
  simpa only [Nat.add_comm (2 ^ d * H)] using eq

/-- Sum a row interval, giving one shared cofactor its certified multiplicity. -/
noncomputable def weightedChunk (b m : ℕ) (qt : QTree) (ow : List QTree)
    (base mask keep twice lo len : ℕ) : ℕ :=
  Nat.rec 0 (fun j acc =>
    let i := Nat.add lo j
    bif Nat.testBit mask i then
      let w := rowWeight keep twice i
      bif Nat.beq w 0 then acc else Nat.add (Nat.mul w (leafE b m qt ow (Nat.add base i))) acc
    else acc) len

def rowSum (F : ℕ → ℕ) (lo len : ℕ) := ∑ i ∈ Finset.range len, F (lo + i)

theorem weightedChunk_eq {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {b m d H mask keep twice lo len W : ℕ} {qt : QTree} {ow : List QTree}
    (hel : P.checkElim b m qt ow = true) (hk : b + m + d ≤ P.V)
    (hH : H < 2 ^ (P.V - (b + m + d))) (hm : P.CoversSplit (b + m) d H mask)
    (hend : lo + len ≤ 2 ^ d)
    (h : weightedChunk b m qt ow (2 ^ d * H) mask keep twice lo len = W) :
    rowSum (fun i => rowWeight keep twice i * P.leaf (b + m) (2 ^ d * H + i)) lo len = W := by
  rw [← h]
  clear h
  induction len with
  | zero => simp [rowSum, weightedChunk]
  | succ n ih =>
    have hi : lo + n < 2 ^ d := by omega
    have hlt := inner_lt hk hH hi
    rw [Nat.add_comm (lo + n)] at hlt
    change _ = (bif mask.testBit (lo + n) then _ else _)
    have prev := ih (by omega)
    unfold rowSum at prev ⊢
    rw [Finset.sum_range_succ, prev]
    let acc := weightedChunk b m qt ow (2 ^ d * H) mask keep twice lo n
    change acc + rowWeight keep twice (lo + n) * P.leaf (b + m) (2 ^ d * H + (lo + n)) =
      (bif mask.testBit (lo + n) then
        (bif Nat.beq (rowWeight keep twice (lo + n)) 0 then acc else
          rowWeight keep twice (lo + n) * leafE b m qt ow (2 ^ d * H + (lo + n)) + acc)
        else acc)
    cases hb : mask.testBit (lo + n) with
    | false =>
      rw [Bool.cond_false, Nat.add_comm (2 ^ d * H), hm _ hi hb, Nat.mul_zero, Nat.add_zero]
    | true =>
      rw [Bool.cond_true, leafE_eq_leaf hc hr hel hlt]
      by_cases hw : rowWeight keep twice (lo + n) = 0
      · rw [hw, beq_true rfl, Bool.cond_true, Nat.zero_mul, Nat.add_zero]
      · rw [beq_false hw, Bool.cond_false, Nat.add_comm]

theorem rowSum_append {F : ℕ → ℕ} {lo n m A B : ℕ}
    (h₁ : rowSum F lo n = A) (h₂ : rowSum F (lo + n) m = B) :
    rowSum F lo (n + m) = A + B := by
  rw [← h₁, ← h₂]
  simp only [rowSum, Finset.sum_range_add, Nat.add_assoc]

theorem leaf_weighted {P : Problem} (hr : P.checkRows = true) {k d H keep twice W : ℕ}
    (hk : k + d ≤ P.V) (hH : H < 2 ^ (P.V - (k + d))) {g : ℕ → ℕ}
    (hb : BalancedRows d keep twice g)
    (hg : ∀ i < 2 ^ d, P.leaf k (2 ^ d * H + g i) = P.leaf k (2 ^ d * H + i))
    (hs : rowSum (fun i => rowWeight keep twice i * P.leaf k (2 ^ d * H + i)) 0 (2 ^ d) = W) :
    P.leaf (k + d) H = W := by
  rw [leaf_eq_inner hr hk hH, sumLeaves_eq_sum, balanced_sum hb hg]
  simpa only [rowSum, Nat.zero_add] using hs

end RACert.Problem
