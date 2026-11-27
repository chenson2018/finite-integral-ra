/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Contract

/-!
# Independent residuals of oriented product-row equations

A retained monomial covers a discarded monomial if each of its factors is one
or is already required by the discarded term. This permits deleting dominated
witnesses and recognizing tautologies before checking that two coordinate
blocks are independent. The model counts of disjoint blocks multiply.
-/

@[expose] public section

namespace RACert.Residual

abbrev Terms := List (ℕ × ℕ)
abbrev Equations := List (Terms × Terms)

def side (v : ℕ → Bool) (s : Terms) : Bool :=
  s.any fun t => litB v t.1 && litB v t.2

def holds (v : ℕ → Bool) (fs : Equations) : Bool :=
  fs.all fun e => side v e.1 == side v e.2

def implies (s t : Terms) : Bool :=
  s.all fun e => e.1 == 0 || e.2 == 0 || t.any fun f =>
    [f.1, f.2].all fun j => j == 1 || j == e.1 || j == e.2

theorem implies_sound {s t : Terms} (h : implies s t = true) (v : ℕ → Bool)
    (hs : side v s = true) : side v t = true := by
  obtain ⟨e, he, hab⟩ := List.any_eq_true.mp hs
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hab
  have h₁ : e.1 ≠ 0 := by intro hz; rw [hz] at ha; contradiction
  have h₂ : e.2 ≠ 0 := by intro hz; rw [hz] at hb; contradiction
  have hr := List.all_eq_true.mp h e he
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true, beq_iff_eq,
    h₁, h₂, or_self, List.any_eq_true, Bool.and_eq_true, Prod.exists, false_or] at hr
  obtain ⟨i, j, hm, hi, hj⟩ := hr
  have val (c : ℕ) (hc : (c = 1 ∨ c = e.1) ∨ c = e.2) : litB v c = true := by
    rcases hc with (h|h)|h
    · rw [h]; rfl
    · rw [h]; exact ha
    · rw [h]; exact hb
  exact List.any_eq_true.mpr ⟨(i, j), hm, Bool.and_eq_true_iff.mpr ⟨val _ hi, val _ hj⟩⟩

def keep (p : ℕ → Bool) (s : Terms) : Terms :=
  s.filter fun e => p e.1 && p e.2

private theorem keep_eq {s : Terms} {p : ℕ → Bool} (h : implies s (keep p s) = true)
    (v : ℕ → Bool) : side v s = side v (keep p s) := by
  rw [Bool.eq_iff_iff]
  refine ⟨implies_sound h v, ?_⟩
  intro hs
  obtain ⟨e, he, ht⟩ := List.any_eq_true.mp hs
  exact List.any_eq_true.mpr ⟨e,(List.mem_filter.mp he).1, ht⟩

def lower (a : ℕ) (c : ℕ) : Bool := decide (c < a + 2)
def upper (a : ℕ) (c : ℕ) : Bool := decide (c < 2 ∨ a + 2 ≤ c)

def down (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => (j - a) + 2

def shift (a : ℕ) (s : Terms) : Terms :=
  s.map fun (i, j) => (down a i, down a j)

private theorem keep_congr {v w : ℕ → Bool} {p : ℕ → Bool} (s : Terms)
    (he : ∀ c, p c = true → litB v c = litB w c) :
    side v (keep p s) = side w (keep p s) := by
  unfold side
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  apply exists_congr
  intro e
  apply and_congr_right
  intro h
  apply Eq.to_iff
  apply congrArg (· = true)
  have hb := Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2
  simp only [he _ hb.1, he _ hb.2]

private theorem lower_side {a x : ℕ} (hx : x < 2 ^ a) (y : ℕ) (s : Terms) :
    side (x + 2 ^ a * y).testBit (keep (lower a) s) = side x.testBit (keep (lower a) s) := by
  apply keep_congr
  intro c hc
  match c with
  | 0 | 1 => rfl
  | j + 2 =>
    have hj : j < a := by simpa [lower] using hc
    simp [litB, testBit_add_two_pow_mul hx, hj]

private theorem upper_side {a x : ℕ} (hx : x < 2 ^ a) (y : ℕ) (s : Terms) :
    side (x + 2 ^ a * y).testBit (keep (upper a) s) =
      side y.testBit (shift a (keep (upper a) s)) := by
  simp only [side, shift, List.any_map]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  apply exists_congr
  intro e
  apply and_congr_right
  intro h
  apply Eq.to_iff
  apply congrArg (· = true)
  have he (c : ℕ) (hc : upper a c = true) :
      litB (x + 2 ^ a * y).testBit c = litB y.testBit (down a c) := by
    match c with
    | 0 | 1 => rfl
    | j + 2 =>
      have hj : a ≤ j := by simpa [upper] using hc
      simp [litB, down, testBit_add_two_pow_mul hx, Nat.not_lt.mpr hj]
  have hb := Bool.and_eq_true_iff.mp (List.mem_filter.mp h).2
  exact congrArg₂ and (he _ hb.1) (he _ hb.2)

inductive Owner where
  | trivial | left (l r : Terms) | right (l r : Terms) | invalid

def owner (a : ℕ) (l r : Terms) : Owner :=
  if implies l r && implies r l then .trivial
  else
    let ll := keep (lower a) l
    let lr := keep (lower a) r
    if implies l ll && implies r lr then .left ll lr
    else
      let ul := keep (upper a) l
      let ur := keep (upper a) r
      if implies l ul && implies r ur then .right (shift a ul) (shift a ur)
      else .invalid

private theorem owner_spec {a x : ℕ} (hx : x < 2 ^ a) (y : ℕ) (l r : Terms) :
    match owner a l r with
    | .trivial => side (x + 2 ^ a * y).testBit l = side (x + 2 ^ a * y).testBit r
    | .left s t => (side (x + 2 ^ a * y).testBit l == side (x + 2 ^ a * y).testBit r) =
        (side x.testBit s == side x.testBit t)
    | .right s t => (side (x + 2 ^ a * y).testBit l == side (x + 2 ^ a * y).testBit r) =
        (side y.testBit s == side y.testBit t)
    | .invalid => True := by
  by_cases ht : (implies l r && implies r l) = true
  · simp only [owner, ht, ↓reduceIte]
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp ht
    exact Bool.eq_iff_iff.mpr ⟨implies_sound h₁ _, implies_sound h₂ _⟩
  by_cases hl : (implies l (keep (lower a) l) && implies r (keep (lower a) r)) = true
  · simp only [owner, ht, hl, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hl
    rw [keep_eq h₁, keep_eq h₂, lower_side hx, lower_side hx]
  by_cases hu : (implies l (keep (upper a) l) && implies r (keep (upper a) r)) = true
  · simp only [owner, ht, hl, hu, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hu
    rw [keep_eq h₁, keep_eq h₂, upper_side hx, upper_side hx]
  · simp [owner, ht, hl, hu]

def partition (a : ℕ) : Equations → Option (Equations × Equations)
  | [] => some ([], [])
  | (l, r)::es => do
    let (ls, rs) ← partition a es
    match owner a l r with
    | .trivial => return (ls, rs)
    | .left s t => return ((s, t)::ls, rs)
    | .right s t => return (ls,(s, t)::rs)
    | .invalid => none

theorem partition_spec {a x : ℕ} (hx : x < 2 ^ a) (y : ℕ) (fs : Equations)
    {ls rs : Equations} (hp : partition a fs = some (ls, rs)) :
    holds (x + 2 ^ a * y).testBit fs = (holds x.testBit ls && holds y.testBit rs) := by
  induction fs generalizing ls rs with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    rfl
  | cons e fs ih =>
    obtain ⟨l, r⟩ := e
    cases h : partition a fs with
    | none => simp [partition, h] at hp
    | some p =>
      obtain ⟨ls', rs'⟩ := p
      have ht := ih h
      have he := owner_spec hx y l r
      cases ho : owner a l r <;>
        simp only [partition, h, ho, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp <;> rw [ho] at he
      all_goals obtain ⟨rfl, rfl⟩ := hp
      all_goals simp only [holds, List.all_cons] at ht ⊢
      all_goals rw [ht, he]; simp [Bool.and_assoc, Bool.and_left_comm]

def packed (b : ℕ) (fs : Equations) : ℕ :=
  let col : ℕ → ℕ
    | 0 => 0
    | 1 => ones b
    | j + 2 => if j < b then pat b j else 0
  let tab (s : Terms) := s.foldr (fun e acc => Nat.lor (Nat.land (col e.1) (col e.2)) acc) 0
  let bad := fs.foldr (fun e acc => Nat.lor (Nat.xor (tab e.1) (tab e.2)) acc) 0
  popcountF b (Nat.land (ones b) (Nat.xor (ones b) bad))

def total (b : ℕ) (fs : Equations) := ∑ x ∈ Finset.range (2 ^ b), (holds x.testBit fs).toNat

theorem packed_eq (b : ℕ) (fs : Equations) : packed b fs = total b fs := by
  unfold packed total
  rw [popcountF_eq_card_filter (land_lt_left (ones_lt b)), Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  let col (c : ℕ) : ℕ := match c with
    | 0 => 0 | 1 => ones b | j + 2 => if j < b then pat b j else 0
  have hc (c : ℕ) : (col c).testBit i = litB i.testBit c := by
    match c with
    | 0 | 1 => simp [col, litB, testBit_ones, hi']
    | j + 2 =>
      by_cases hj : j < b
      · simp [col, litB, hj, testBit_pat, hi']
      · have hz := Nat.testBit_eq_false_of_lt (hi'.trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj)))
        simp [col, litB, hj, hz]
  let tab (s : Terms) := s.foldr (fun e acc => Nat.lor (Nat.land (col e.1) (col e.2)) acc) 0
  have hs (s : Terms) : (tab s).testBit i = side i.testBit s := by
    induction s with
    | nil => simp [tab, side]
    | cons e s ih =>
      change (Nat.lor (Nat.land (col e.1) (col e.2)) (tab s)).testBit i = _
      rw [testBit_lor, testBit_land, hc, hc, ih]; rfl
  have hf (es : Equations) : (es.foldr (fun e acc => Nat.lor (Nat.xor (tab e.1) (tab e.2))
      acc) 0).testBit i = !holds i.testBit es := by
    induction es with
    | nil => simp [holds]
    | cons e es ih =>
      rw [List.foldr_cons, testBit_lor, testBit_xor, hs, hs, ih]
      change _ = !((_ == _) && holds i.testBit es)
      cases side i.testBit e.1 <;> cases side i.testBit e.2 <;> cases holds i.testBit es <;> rfl
  rw [testBit_land, testBit_ones, testBit_xor, testBit_ones, hf]
  cases holds i.testBit fs <;> simp [hi']

def count : List ℕ → Equations → Option ℕ
  | [], fs => some (packed 0 fs)
  | [b], fs => some (if fs.isEmpty then 2 ^ b else packed b fs)
  | b::c::bs, fs => do
    let (ls, rs) ← partition b fs
    let r ← count (c::bs) rs
    return (if ls.isEmpty then 2 ^ b else packed b ls) * r

private theorem count_one (b : ℕ) (ls : Equations) :
    (if ls.isEmpty then 2 ^ b else packed b ls) = total b ls := by
  cases ls with
  | nil => simp [total, holds]
  | cons => exact packed_eq ..

theorem count_sound : ∀ (bs : List ℕ) (fs : Equations) {n : ℕ}, count bs fs = some n →
    total bs.sum fs = n
  | [], fs, _, h => by
    obtain rfl := Option.some.inj h
    exact (packed_eq ..).symm
  | [b], fs, _, h => by
    rw [← Option.some.inj h]
    simpa using (count_one b fs).symm
  | b::c::bs, fs, _, h => by
    cases hp : partition b fs with
    | none => simp [count, hp] at h
    | some p =>
      obtain ⟨ls, rs⟩ := p
      cases hr : count (c::bs) rs with
      | none => simp [count, hp, hr] at h
      | some r =>
        change (do
          let (ll, rr) ← partition b fs
          let v ← count (c::bs) rr
          return (if ll.isEmpty then 2 ^ b else packed b ll) * v) = some _ at h
        rw [hp] at h
        change (do
          let v ← count (c::bs) rs
          return (if ls.isEmpty then 2 ^ b else packed b ls) * v) = some _ at h
        rw [hr] at h
        apply Option.some.inj at h
        rw [← h, count_one, ← count_sound (c::bs) rs hr]
        unfold total
        rw [List.sum_cons, sum_range_two_pow_add, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [partition_spec (Finset.mem_range.mp hx) y fs hp]
        cases holds x.testBit ls <;> cases holds y.testBit rs <;> rfl

end RACert.Residual

namespace RACert.Problem

def residualCode (k H : ℕ) (cs : List ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => if j < k then cs.getD j 0 else (H.testBit (j - k)).toNat

noncomputable def residualEqs (P : Problem) (k H : ℕ) (cs : List ℕ) : Residual.Equations :=
  let code := residualCode k H cs
  let terms (a b c d : ℕ) := (List.range P.k).map fun q =>
    (code (P.clsAt a b q), code (P.clsAt c d q))
  P.quads.map fun x =>
    let r := x / P.k / P.k / P.k % P.k
    let u := x / P.k / P.k % P.k
    let t := x / P.k % P.k
    let p := x % P.k
    (terms (cvN P.s r) p u t, terms r u p (cvN P.s t))

theorem leaf_contract_factors {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k b H : ℕ} (hH : H < 2 ^ (P.V - k)) {ss : List Identification} {ids cs : List ℕ}
    (hs : P.checkContraction (outerCode k H) ss = true)
    (hm : checkCoordinates k b ids cs (contraction (outerCode k H) ss) = true)
    {bs : List ℕ} {W : ℕ} (hb : bs.sum = b)
    (hw : Residual.count bs (P.residualEqs k H cs) = some W) : P.leaf k H = W := by
  rw [leaf_contracted_card hc hr hH hs hm, card_filter_fun_eq_sum, ← Residual.count_sound bs _ hw]
  unfold Residual.total
  rw [hb]
  apply Finset.sum_congr rfl
  intro x _
  have hh := hm
  simp only [checkCoordinates, Bool.and_eq_true, allRange_iff] at hh
  have he (c : ℕ) : litB x.testBit (residualCode k H cs c) =
      litB (join k H (decodeRow cs (fun i : Fin b => x.testBit i))) c := by
    match c with
    | 0 | 1 => rfl
    | j + 2 =>
      by_cases hj : j < k
      · simp only [residualCode, hj, ↓reduceIte, litB, join, decodeRow]
        cases hc' : cs.getD j 0 with
        | zero => rfl
        | succ t =>
          cases t with
          | zero => rfl
          | succ t =>
            have ht : t < b := by
              simpa only [hc', inRange, decide_eq_true_eq] using (hh.2 j hj).1
            simp [extFin, ht]
      · cases ht : H.testBit (j - k) <;> simp [residualCode, hj, ht, litB, join]
  simp only [residualEqs, Residual.holds, Residual.side, List.all_map, List.any_map,
    Function.comp_def, he, phi, quadAt, quadB, dotB, tbl]

end RACert.Problem
