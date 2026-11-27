/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Elim

/-!
# Splitting an orbit representative a second time

The outer symmetry group only needs to preserve the union of the low and middle variables.
Inside each orbit representative we can therefore branch on a non-invariant set of middle
variables. Small truth tables bound each side of associativity over every completion of the
low variables. A disjoint pair of bounds discharges the entire corresponding inner leaf.
-/

@[expose] public section

namespace RACert

/-- Assemble a segment from individually proved outer leaf counts. -/
theorem SegSum.cons {F : ℕ → ℕ} {i w v W : ℕ} {seg : List (ℕ × ℕ)} (hv : F i = v)
    (hs : SegSum F seg W) : SegSum F ((i, w) :: seg) (w * v + W) :=
  congrArg₂ (· + ·) (congrArg (w * ·) hv) hs

namespace Problem

/-- Disjoin tables indexed by a list. -/
def unionBits (f : ℕ → ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun i acc => Nat.lor (f i) acc) 0

private theorem unionBits_bit (f : ℕ → ℕ) (l : List ℕ) (i : ℕ) :
    (unionBits f l).testBit i = l.any fun j => (f j).testBit i := by
  induction l with
  | nil => simp [unionBits]
  | cons x xs ih => exact (testBit_lor ..).trans (congrArg (_ || ·) ih)

/-- Bit `i` corresponds to middle assignment `i`. Set the unknown low variables uniformly
to `z` and the remaining high variables to the bits of `H`. -/
def boundCol (k d H : ℕ) (z : Bool) : ℕ → ℕ
  | 0 => 0
  | 1 => ones d
  | j + 2 =>
    if j < k then (if z then ones d else 0)
    else if j - k < d then pat d (j - k)
    else if H.testBit (j - k - d) then ones d else 0

private theorem boundCol_bit {k d H i : ℕ} (hi : i < 2 ^ d) (z : Bool) (c : ℕ) :
    (boundCol k d H z c).testBit i =
      litB (join k (i + 2 ^ d * H) (fun _ => z)) c := by
  have hon : (ones d).testBit i = true := by simp [testBit_ones, hi]
  match c with
  | 0 => simp [boundCol, litB]
  | 1 => exact hon
  | j + 2 =>
    simp only [boundCol, litB, join]
    by_cases hj : j < k
    · cases z <;> simp [hj, hon]
    · simp only [hj, ↓reduceIte, testBit_add_two_pow_mul hi]
      split_ifs with hd hH <;> simp_all [testBit_pat]

noncomputable def dotBits (P : Problem) (col : ℕ → ℕ) (a b c e : ℕ) : ℕ :=
  unionBits (fun q => Nat.land (col (P.clsAt a b q)) (col (P.clsAt c e q))) (List.range P.k)

private theorem dotBits_bit (P : Problem) {d i : ℕ} (hi : i < 2 ^ d) (k H a b c e : ℕ)
    (z : Bool) :
    (dotBits P (boundCol k d H z) a b c e).testBit i =
      dotB P.k (P.tbl (join k (i + 2 ^ d * H) (fun _ => z))) a b c e := by
  simp only [dotBits, unionBits_bit, testBit_land, boundCol_bit hi, dotB, tbl]

private theorem dot_mono (P : Problem) {v w : ℕ → Bool} (h : ∀ j, v j = true → w j = true)
    {a b c e : ℕ} (hv : dotB P.k (P.tbl v) a b c e = true) :
    dotB P.k (P.tbl w) a b c e = true := by
  have hl : ∀ i, litB v i = true → litB w i = true
    | 0 | 1 => id
    | j + 2 => h j
  obtain ⟨q, hq, h₁, h₂⟩ := dotB_iff.mp hv
  exact dotB_iff.mpr ⟨q, hq, hl _ h₁, hl _ h₂⟩

/-- A definite witness on one side and no possible witness on the other. -/
noncomputable def impossible (P : Problem) (k d H x : ℕ) : ℕ :=
  let r := x / P.k / P.k / P.k % P.k
  let u := x / P.k / P.k % P.k
  let t := x / P.k % P.k
  let p := x % P.k
  let left z := dotBits P (boundCol k d H z) (cvN P.s r) p u t
  let right z := dotBits P (boundCol k d H z) r u p (cvN P.s t)
  Nat.lor (Nat.land (left false) (Nat.xor (ones d) (right true)))
    (Nat.land (right false) (Nat.xor (ones d) (left true)))

private theorem impossible_of_model {P : Problem} (hc : P.check = true) {k d H i : ℕ}
    (hi : i < 2 ^ d) (w : Fin k → Bool) (hv : P.phi (join k (i + 2 ^ d * H) w) = true) (x : ℕ) :
    (impossible P k d H x).testBit i = false := by
  have hlo : ∀ j, join k (i + 2 ^ d * H) (fun _ => false) j = true →
      join k (i + 2 ^ d * H) w j = true := by
    intro j
    simp only [join]
    split <;> simp
  have hhi : ∀ j, join k (i + 2 ^ d * H) w j = true →
      join k (i + 2 ^ d * H) (fun _ => true) j = true := by
    intro j
    simp only [join]
    split <;> simp
  have eq := quadAt_of_phi hc hv x
  rw [quadAt, quadB, beq_iff_eq] at eq
  simp only [impossible, testBit_lor, testBit_land, testBit_xor, testBit_ones, hi,
    decide_true, Bool.true_xor, dotBits_bit P hi]
  apply Bool.eq_false_iff.mpr
  intro bad
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at bad
  rcases bad with ⟨h, hn⟩ | ⟨h, hn⟩
  · have h' := dot_mono P hlo h
    rw [eq] at h'
    simp [dot_mono P hhi h'] at hn
  · have h' := dot_mono P hlo h
    rw [← eq] at h'
    simp [dot_mono P hhi h'] at hn

/-- Middle assignments that the supplied quadruples leave open. Any list of witnesses is sound. -/
noncomputable def splitMask (P : Problem) (k d H : ℕ) (xs : List ℕ) : ℕ :=
  Nat.xor (ones d) (unionBits (impossible P k d H) xs)

private theorem inner_lt {P : Problem} {k d H i : ℕ} (hk : k + d ≤ P.V)
    (hH : H < 2 ^ (P.V - (k + d))) (hi : i < 2 ^ d) : i + 2 ^ d * H < 2 ^ (P.V - k) := by
  rw [show P.V - k = d + (P.V - (k + d)) by omega, pow_add]
  calc
    _ < 2 ^ d * (H + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ _ := Nat.mul_le_mul_left _ hH

/-- Every missing bit represents a zero inner leaf. -/
def CoversSplit (P : Problem) (k d H mask : ℕ) : Prop :=
  ∀ i < 2 ^ d, mask.testBit i = false → P.leaf k (i + 2 ^ d * H) = 0

theorem coversSplit {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k d H mask : ℕ} (hk : k + d ≤ P.V) (hH : H < 2 ^ (P.V - (k + d)))
    {xs : List ℕ} (hm : P.splitMask k d H xs = mask) : P.CoversSplit k d H mask := by
  intro i hi hbit
  rw [leaf_eq hr (inner_lt hk hH hi), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hv
  rw [← hm, splitMask, testBit_xor, testBit_ones, unionBits_bit] at hbit
  have : xs.any (fun x => (impossible P k d H x).testBit i) = false := by
    simp [List.any_eq_false, impossible_of_model hc hi w hv]
  simp [this, hi] at hbit

/-- One outer leaf as a sum over the middle variables. -/
theorem leaf_eq_inner {P : Problem} (hr : P.checkRows = true) {k d H : ℕ}
    (hk : k + d ≤ P.V) (hH : H < 2 ^ (P.V - (k + d))) :
    P.leaf (k + d) H = P.sumLeaves k (2 ^ d * H) (2 ^ d) := by
  rw [leaf_split hr hH, Finset.sum_comm, sumLeaves_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [Nat.add_comm (2 ^ d * H), leaf_eq hr (inner_lt hk hH hi'), card_filter_fun_eq_sum]
  simp only [join_testBit]

/-- Evaluate only the live inner leaves in one chunk. -/
noncomputable def splitChunk (b m : ℕ) (qt : QTree) (ow : List QTree)
    (base mask lo len : ℕ) : ℕ :=
  Nat.rec 0 (fun j acc =>
    let i := Nat.add lo j
    bif Nat.testBit mask i then Nat.add (leafE b m qt ow (Nat.add base i)) acc else acc) len

theorem sumLeaves_splitChunk {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {b m d H mask lo len W : ℕ} {qt : QTree} {ow : List QTree}
    (hel : P.checkElim b m qt ow = true) (hk : b + m + d ≤ P.V)
    (hH : H < 2 ^ (P.V - (b + m + d))) (hm : P.CoversSplit (b + m) d H mask)
    (hend : lo + len ≤ 2 ^ d)
    (h : splitChunk b m qt ow (2 ^ d * H) mask lo len = W) :
    P.sumLeaves (b + m) (2 ^ d * H + lo) len = W := by
  rw [← h]
  clear h
  induction len with
  | zero => rfl
  | succ n ih =>
    have hi : lo + n < 2 ^ d := by omega
    rw [sumLeaves_succ, ih (by omega), Nat.add_assoc]
    change _ = (bif mask.testBit (lo + n) then _ else _)
    cases hh : mask.testBit (lo + n) with
    | false =>
      rw [Bool.cond_false, Nat.add_comm (2 ^ d * H), hm _ hi hh, Nat.zero_add]
      rfl
    | true =>
      have hlt := inner_lt hk hH hi
      rw [Nat.add_comm (lo + n)] at hlt
      rw [Bool.cond_true, ← leafE_eq_leaf hc hr hel hlt]
      rfl

end Problem

end RACert
