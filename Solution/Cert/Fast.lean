/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Sym

/-!
# A leaf evaluator sharing work between leaves

`Problem.leaf` evaluates the formula on tables computed from the assignment `α` of the high
variables, so that the kernel sees different expressions for different `α` even when they denote
the same table. `Problem.leafS` computes the same number, but first classifies every class code
as false, true or a low variable (`kindOf`) and then builds the tables as expressions in the
truth-table columns `pat b j` only. It is written in continuation-passing style, so that these
expressions are passed along in a canonical form: the kernel then evaluates each distinct
expression once per declaration, and leaves checked in the same declaration (`checkLeaves`) share
most of their big-number operations.
-/

@[expose] public section

namespace RACert

/-- The kind of a class code when the high variables are given by `α`: `0` (false), `1` (true), or
`j + 2` for the low variable `j < b`. -/
noncomputable def kindOf (b α c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun m _ => Nat.rec (motive := fun _ => ℕ) 1
      (fun j _ => bif Nat.blt j b then Nat.add j 2
        else Nat.land (Nat.shiftRight α (Nat.sub j b)) 1) m) c

theorem kindOf_low {b α j : ℕ} (hj : j < b) : kindOf b α (j + 2) = j + 2 := by
  have h : Nat.blt j b = true := by rw [Nat.blt_eq]; exact hj
  change (bif Nat.blt j b then Nat.add j 2 else _) = _
  rw [h]
  rfl

theorem land_shiftRight_one (α n : ℕ) :
    Nat.land (Nat.shiftRight α n) 1 = if α.testBit n = true then 1 else 0 := by
  change (α >>> n) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (α / 2 ^ n) with h | h <;> simp [h]

theorem kindOf_high {b α j : ℕ} (hj : ¬ j < b) :
    kindOf b α (j + 2) = if α.testBit (j - b) = true then 1 else 0 := by
  have h : Nat.blt j b = false := by rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; exact hj
  change (bif Nat.blt j b then Nat.add j 2 else Nat.land (Nat.shiftRight α (Nat.sub j b)) 1) = _
  rw [h]
  exact land_shiftRight_one α (j - b)

/-- The three possible kinds of a class code, with their meaning. -/
theorem kindOf_cases (b α β c : ℕ) :
    (kindOf b α c = 0 ∧ litB (joinN b α β) c = false) ∨
      (kindOf b α c = 1 ∧ litB (joinN b α β) c = true) ∨
      ∃ j < b, kindOf b α c = j + 2 ∧ litB (joinN b α β) c = β.testBit j := by
  match c with
  | 0 => exact Or.inl ⟨rfl, rfl⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | j + 2 =>
    by_cases hj : j < b
    · exact Or.inr (Or.inr ⟨j, hj, kindOf_low hj, by simp [litB, joinN, hj]⟩)
    · rw [kindOf_high hj]
      cases hbit : α.testBit (j - b)
      · exact Or.inl ⟨by simp, by simp [litB, joinN, hj, hbit]⟩
      · exact Or.inr (Or.inl ⟨by simp, by simp [litB, joinN, hj, hbit]⟩)

/-- Disjunction of a table into an accumulator which is `0` or a table. -/
noncomputable def orS (acc t : ℕ) : ℕ := bif Nat.beq acc 0 then t else Nat.lor acc t

/-- Conjunction of two low variables, in a canonical order. -/
noncomputable def andS (b i j : ℕ) : ℕ :=
  bif Nat.ble i j then Nat.land (pat b i) (pat b j) else Nat.land (pat b j) (pat b i)

theorem orS_spec {b acc t : ℕ} (hacc : acc < top b) (ht : t < top b) (β : ℕ) :
    orS acc t < top b ∧ (orS acc t).testBit β = (acc.testBit β || t.testBit β) := by
  unfold orS
  by_cases h0 : acc = 0
  · rw [beq_true h0, h0]
    exact ⟨ht, by simp⟩
  · rw [beq_false h0]
    exact ⟨lor_lt hacc ht, testBit_lor _ _ _⟩

theorem andS_spec {b i j β : ℕ} (hi : i < b) (hj : j < b) (hβ : β < 2 ^ b) :
    andS b i j < top b ∧ (andS b i j).testBit β = (β.testBit i && β.testBit j) := by
  have e1 : (pat b i).testBit β = β.testBit i := by rw [testBit_pat hi]; simp [hβ]
  have e2 : (pat b j).testBit β = β.testBit j := by rw [testBit_pat hj]; simp [hβ]
  unfold andS
  cases Nat.ble i j
  · exact ⟨land_lt (pat_lt b i), by
      change (Nat.land (pat b j) (pat b i)).testBit β = _
      rw [testBit_land, e1, e2, Bool.and_comm]⟩
  · exact ⟨land_lt (pat_lt b j), by
      change (Nat.land (pat b i) (pat b j)).testBit β = _
      rw [testBit_land, e1, e2]⟩

theorem pat_spec {b j β : ℕ} (hj : j < b) (hβ : β < 2 ^ b) :
    pat b j < top b ∧ (pat b j).testBit β = β.testBit j :=
  ⟨pat_lt b j, by rw [testBit_pat hj]; simp [hβ]⟩

/-- One step of a disjunction of conjunctions: add the conjunction of the kinds `x` and `y` to the
accumulator `acc` and pass the result to the continuation. -/
noncomputable def stepK (T b x y acc : ℕ) (k : ℕ → ℕ) : ℕ :=
  bif Nat.beq acc T then k T
  else
    Nat.rec (motive := fun _ => ℕ) (k acc)
      (fun x' _ => Nat.rec (motive := fun _ => ℕ)
        (Nat.rec (motive := fun _ => ℕ) (k acc)
          (fun y' _ => Nat.rec (motive := fun _ => ℕ) (k T)
            (fun j _ => k (orS acc (pat b j))) y') y)
        (fun i _ => Nat.rec (motive := fun _ => ℕ) (k acc)
          (fun y' _ => Nat.rec (motive := fun _ => ℕ) (k (orS acc (pat b i)))
            (fun j _ => k (orS acc (andS b i j))) y') y) x') x

/-- The value passed on by `stepK`. -/
noncomputable def stepD (T b x y acc : ℕ) : ℕ := stepK T b x y acc id

theorem stepK_eq (T b x y acc : ℕ) (k : ℕ → ℕ) : stepK T b x y acc k = k (stepD T b x y acc) := by
  unfold stepD stepK
  cases Nat.beq acc T
  · match x, y with
    | 0, _ => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 1, _ + 2 => rfl
    | _ + 2, 0 => rfl
    | _ + 2, 1 => rfl
    | _ + 2, _ + 2 => rfl
  · rfl

theorem stepD_top {T b x y acc : ℕ} (h : acc = T) : stepD T b x y acc = T := by
  unfold stepD stepK
  rw [beq_true h]
  rfl

section StepD

variable {T b acc : ℕ} (h : acc ≠ T)
include h

theorem stepD_zero (y : ℕ) : stepD T b 0 y acc = acc := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_one_zero : stepD T b 1 0 acc = acc := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_one_one : stepD T b 1 1 acc = T := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_one_var (j : ℕ) : stepD T b 1 (j + 2) acc = orS acc (pat b j) := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_var_zero (i : ℕ) : stepD T b (i + 2) 0 acc = acc := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_var_one (i : ℕ) : stepD T b (i + 2) 1 acc = orS acc (pat b i) := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_var_var (i j : ℕ) : stepD T b (i + 2) (j + 2) acc = orS acc (andS b i j) := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

end StepD

theorem stepD_spec {b α β c c' acc : ℕ} (hβ : β < 2 ^ b) (hacc : acc ≤ top b) :
    stepD (top b) b (kindOf b α c) (kindOf b α c') acc ≤ top b ∧
      sem (top b) (stepD (top b) b (kindOf b α c) (kindOf b α c') acc) β =
        (sem (top b) acc β || (litB (joinN b α β) c && litB (joinN b α β) c')) := by
  by_cases hT : acc = top b
  · rw [stepD_top hT, sem_top, hT, sem_top]
    exact ⟨le_refl _, rfl⟩
  have hlt : acc < top b := lt_of_le_of_ne hacc hT
  have hsem : sem (top b) acc β = acc.testBit β := sem_of_ne hT β
  have key : ∀ {t : ℕ}, t < top b →
      orS acc t ≤ top b ∧ sem (top b) (orS acc t) β = (sem (top b) acc β || t.testBit β) := by
    intro t ht
    obtain ⟨h1, h2⟩ := orS_spec hlt ht β
    exact ⟨h1.le, by rw [sem_of_ne h1.ne, h2, hsem]⟩
  rcases kindOf_cases b α β c with ⟨e, l⟩ | ⟨e, l⟩ | ⟨i, hi, e, l⟩ <;> rw [e, l]
  · rw [stepD_zero hT]
    exact ⟨hacc, by simp⟩
  · rcases kindOf_cases b α β c' with ⟨e', l'⟩ | ⟨e', l'⟩ | ⟨j, hj, e', l'⟩ <;> rw [e', l']
    · rw [stepD_one_zero hT]
      exact ⟨hacc, by simp⟩
    · rw [stepD_one_one hT, sem_top]
      exact ⟨le_refl _, by simp⟩
    · rw [stepD_one_var hT]
      obtain ⟨p1, p2⟩ := pat_spec hj hβ
      obtain ⟨h1, h2⟩ := key p1
      exact ⟨h1, by rw [h2, p2, Bool.true_and]⟩
  · rcases kindOf_cases b α β c' with ⟨e', l'⟩ | ⟨e', l'⟩ | ⟨j, hj, e', l'⟩ <;> rw [e', l']
    · rw [stepD_var_zero hT]
      exact ⟨hacc, by simp⟩
    · rw [stepD_var_one hT]
      obtain ⟨p1, p2⟩ := pat_spec hi hβ
      obtain ⟨h1, h2⟩ := key p1
      exact ⟨h1, by rw [h2, p2, Bool.and_true]⟩
    · rw [stepD_var_var hT]
      obtain ⟨p1, p2⟩ := andS_spec hi hj hβ
      obtain ⟨h1, h2⟩ := key p1
      exact ⟨h1, by rw [h2, p2]⟩

/-- `acc ∨ ⋁ q, l1[q] ∧ l2[q]` on lists of kinds, in continuation-passing style. -/
noncomputable def dotK (T b : ℕ) (l1 : List ℕ) : List ℕ → ℕ → (ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ → (ℕ → ℕ) → ℕ) (fun _ acc k => k acc)
    (fun x _ ih l2 acc k =>
      List.rec (motive := fun _ => ℕ) (k acc)
        (fun y ys _ => stepK T b x y acc (fun acc' => ih ys acc' k)) l2) l1

/-- The value passed on by `dotK`. -/
noncomputable def dotD (T b : ℕ) (l1 l2 : List ℕ) (acc : ℕ) : ℕ := dotK T b l1 l2 acc id

theorem dotK_cons_cons (T b x y : ℕ) (xs ys : List ℕ) (acc : ℕ) (k : ℕ → ℕ) :
    dotK T b (x :: xs) (y :: ys) acc k = stepK T b x y acc (fun acc' => dotK T b xs ys acc' k) :=
  rfl

theorem dotK_eq (T b : ℕ) (l1 l2 : List ℕ) (acc : ℕ) (k : ℕ → ℕ) :
    dotK T b l1 l2 acc k = k (dotD T b l1 l2 acc) := by
  induction l1 generalizing l2 acc k with
  | nil => rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      unfold dotD
      rw [dotK_cons_cons, dotK_cons_cons, stepK_eq, stepK_eq, ih, ih ys _ id]
      rfl

theorem dotD_nil (T b : ℕ) (l2 : List ℕ) (acc : ℕ) : dotD T b [] l2 acc = acc := rfl

theorem dotD_cons_nil (T b x : ℕ) (xs : List ℕ) (acc : ℕ) : dotD T b (x :: xs) [] acc = acc := rfl

theorem dotD_cons_cons (T b x y : ℕ) (xs ys : List ℕ) (acc : ℕ) :
    dotD T b (x :: xs) (y :: ys) acc = dotD T b xs ys (stepD T b x y acc) := by
  unfold dotD
  rw [dotK_cons_cons, stepK_eq, dotK_eq]

theorem dotD_spec {b α β : ℕ} (hβ : β < 2 ^ b) (c1 c2 : List ℕ) {acc : ℕ} (hacc : acc ≤ top b) :
    dotD (top b) b (c1.map (kindOf b α)) (c2.map (kindOf b α)) acc ≤ top b ∧
      sem (top b) (dotD (top b) b (c1.map (kindOf b α)) (c2.map (kindOf b α)) acc) β =
        (sem (top b) acc β ||
          (c1.zip c2).any fun p => litB (joinN b α β) p.1 && litB (joinN b α β) p.2) := by
  induction c1 generalizing c2 acc with
  | nil => simp [dotD_nil, hacc]
  | cons i c1 ih =>
    cases c2 with
    | nil => simp [dotD_cons_nil, hacc]
    | cons j c2 =>
      obtain ⟨h1, h2⟩ := stepD_spec (α := α) (c := i) (c' := j) hβ hacc
      obtain ⟨g1, g2⟩ := ih c2 h1
      rw [List.map_cons, List.map_cons, dotD_cons_cons]
      refine ⟨g1, ?_⟩
      rw [g2, h2, List.zip_cons_cons, List.any_cons, Bool.or_assoc]

/-- The kinds of all triples. -/
noncomputable def krowsOf (b α : ℕ) (cls : List (List (List ℕ))) : List (List (List ℕ)) :=
  map' (map' (map' (kindOf b α))) cls

theorem rowAt_krowsOf (b α : ℕ) (cls : List (List (List ℕ))) (a c : ℕ) :
    rowAt (krowsOf b α cls) a c = (nth [] (nth [] cls a) c).map (kindOf b α) := by
  have e : krowsOf b α cls = cls.map (List.map (List.map (kindOf b α))) := by
    unfold krowsOf
    rw [map'_eq]
    congr 1
    funext l
    rw [map'_eq]
    congr 1
    funext l'
    rw [map'_eq]
  rw [rowAt, e]
  have h1 := nth_map (List.map (List.map (kindOf b α))) [] cls a
  rw [List.map_nil] at h1
  rw [h1]
  have h2 := nth_map (List.map (kindOf b α)) [] (nth [] cls a) c
  rw [List.map_nil] at h2
  exact h2

/-- Inequality of two values which are tables or constants; the result is a plain bit mask. -/
noncomputable def neqS (T on L R : ℕ) : ℕ :=
  bif Nat.beq L T then (bif Nat.beq R T then 0 else Nat.xor on R)
  else bif Nat.beq R T then Nat.xor on L
  else bif Nat.beq L R then 0
  else bif Nat.ble L R then Nat.xor L R else Nat.xor R L

/-- Accumulate a mask of violations. -/
noncomputable def badS (bad q : ℕ) : ℕ :=
  bif Nat.beq q 0 then bad else bif Nat.beq bad 0 then q else Nat.lor bad q

theorem neqS_spec {b L R β : ℕ} (hL : L ≤ top b) (hR : R ≤ top b) (hβ : β < 2 ^ b) :
    neqS (top b) (ones b) L R < top b ∧
      (neqS (top b) (ones b) L R).testBit β = (sem (top b) L β ^^ sem (top b) R β) := by
  have hT := top_pos b
  have ho : ones b < 2 ^ 2 ^ b := ones_lt b
  have hob : (ones b).testBit β = true := by rw [testBit_ones]; simpa using hβ
  unfold neqS
  by_cases hLT : L = top b
  · rw [beq_true hLT]
    by_cases hRT : R = top b
    · rw [beq_true hRT, hLT, hRT, sem_top]
      exact ⟨hT, by simp⟩
    · rw [beq_false hRT, hLT, sem_top, sem_of_ne hRT]
      have hR' : R < 2 ^ 2 ^ b := lt_of_le_of_ne hR hRT
      simp only [Bool.cond_true, Bool.cond_false]
      exact ⟨xor_lt ho hR', by rw [testBit_xor, hob]⟩
  · rw [beq_false hLT]
    have hL' : L < 2 ^ 2 ^ b := lt_of_le_of_ne hL hLT
    by_cases hRT : R = top b
    · rw [beq_true hRT, hRT, sem_top, sem_of_ne hLT]
      simp only [Bool.cond_true, Bool.cond_false]
      exact ⟨xor_lt ho hL', by rw [testBit_xor, hob, Bool.xor_comm]⟩
    · rw [beq_false hRT, sem_of_ne hLT, sem_of_ne hRT]
      have hR' : R < 2 ^ 2 ^ b := lt_of_le_of_ne hR hRT
      by_cases hLR : L = R
      · rw [beq_true hLR, hLR]
        exact ⟨hT, by simp⟩
      · rw [beq_false hLR]
        cases Nat.ble L R
        · simp only [Bool.cond_false]
          exact ⟨xor_lt hR' hL', by rw [testBit_xor, Bool.xor_comm]⟩
        · simp only [Bool.cond_true, Bool.cond_false]
          exact ⟨xor_lt hL' hR', by rw [testBit_xor]⟩

theorem badS_spec {b bad q : ℕ} (hbad : bad < top b) (hq : q < top b) (β : ℕ) :
    badS bad q < top b ∧ (badS bad q).testBit β = (bad.testBit β || q.testBit β) := by
  unfold badS
  by_cases hq0 : q = 0
  · rw [beq_true hq0, hq0]
    exact ⟨hbad, by simp⟩
  · rw [beq_false hq0]
    by_cases hb0 : bad = 0
    · rw [beq_true hb0, hb0]
      exact ⟨hq, by simp⟩
    · rw [beq_false hb0]
      exact ⟨lor_lt hbad hq, testBit_lor _ _ _⟩

namespace Problem

variable (P : Problem)

/-- Add the violations of the quadruple `(r, u, t, p)` to `bad`. -/
noncomputable def quadK4 (T on b : ℕ) (krows : List (List (List ℕ))) (r u t p bad : ℕ)
    (k : ℕ → ℕ) : ℕ :=
  dotK T b (rowAt krows (cvN P.s r) p) (rowAt krows u t) 0 fun L =>
    dotK T b (rowAt krows r u) (rowAt krows p (cvN P.s t)) 0 fun R =>
      k (badS bad (neqS T on L R))

/-- The value passed on by `quadK4`. -/
noncomputable def quadD4 (T on b : ℕ) (krows : List (List (List ℕ))) (r u t p bad : ℕ) : ℕ :=
  badS bad (neqS T on (dotD T b (rowAt krows (cvN P.s r) p) (rowAt krows u t) 0)
    (dotD T b (rowAt krows r u) (rowAt krows p (cvN P.s t)) 0))

theorem quadK4_eq (T on b : ℕ) (krows : List (List (List ℕ))) (r u t p bad : ℕ) (k : ℕ → ℕ) :
    P.quadK4 T on b krows r u t p bad k = k (P.quadD4 T on b krows r u t p bad) := by
  unfold quadK4 quadD4
  rw [dotK_eq, dotK_eq]

/-- Add the violations of the quadruple with code `x` to `bad`. -/
noncomputable def quadK (T on b : ℕ) (krows : List (List (List ℕ))) (x bad : ℕ) (k : ℕ → ℕ) : ℕ :=
  P.quadK4 T on b krows (Nat.mod (Nat.div (Nat.div (Nat.div x P.k) P.k) P.k) P.k)
    (Nat.mod (Nat.div (Nat.div x P.k) P.k) P.k) (Nat.mod (Nat.div x P.k) P.k) (Nat.mod x P.k) bad k

/-- The value passed on by `quadK`. -/
noncomputable def quadD (T on b : ℕ) (krows : List (List (List ℕ))) (x bad : ℕ) : ℕ :=
  P.quadD4 T on b krows (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k) (x / P.k % P.k)
    (x % P.k) bad

theorem quadK_eq (T on b : ℕ) (krows : List (List (List ℕ))) (x bad : ℕ) (k : ℕ → ℕ) :
    P.quadK T on b krows x bad k = k (P.quadD T on b krows x bad) :=
  P.quadK4_eq T on b krows _ _ _ _ bad k

/-- Accumulate the violations of all quadruples, stopping once every assignment is violated. -/
noncomputable def evalK (T on b : ℕ) (krows : List (List (List ℕ))) (quads : List ℕ) :
    ℕ → (ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => ℕ → (ℕ → ℕ) → ℕ) (fun bad k => k bad)
    (fun x _ ih bad k => bif Nat.beq bad on then k on
      else P.quadK T on b krows x bad (fun bad' => ih bad' k)) quads

/-- The value passed on by `evalK`. -/
noncomputable def evalD (T on b : ℕ) (krows : List (List (List ℕ))) (quads : List ℕ) (bad : ℕ) :
    ℕ :=
  P.evalK T on b krows quads bad id

theorem evalK_cons (T on b : ℕ) (krows : List (List (List ℕ))) (x : ℕ) (quads : List ℕ) (bad : ℕ)
    (k : ℕ → ℕ) : P.evalK T on b krows (x :: quads) bad k =
      bif Nat.beq bad on then k on
      else P.quadK T on b krows x bad (fun bad' => P.evalK T on b krows quads bad' k) := rfl

theorem evalK_eq (T on b : ℕ) (krows : List (List (List ℕ))) (quads : List ℕ) (bad : ℕ)
    (k : ℕ → ℕ) : P.evalK T on b krows quads bad k = k (P.evalD T on b krows quads bad) := by
  induction quads generalizing bad k with
  | nil => rfl
  | cons x quads ih =>
    unfold evalD
    rw [evalK_cons, evalK_cons]
    cases Nat.beq bad on
    · simp only [Bool.cond_false]
      rw [quadK_eq, quadK_eq, ih, ih _ id]
      rfl
    · rfl

theorem evalD_nil (T on b : ℕ) (krows : List (List (List ℕ))) (bad : ℕ) :
    P.evalD T on b krows [] bad = bad := rfl

theorem evalD_cons (T on b : ℕ) (krows : List (List (List ℕ))) (x : ℕ) (quads : List ℕ)
    (bad : ℕ) : P.evalD T on b krows (x :: quads) bad =
      bif Nat.beq bad on then on else P.evalD T on b krows quads (P.quadD T on b krows x bad) := by
  unfold evalD
  rw [evalK_cons]
  cases Nat.beq bad on
  · simp only [Bool.cond_false]
    rw [quadK_eq, evalK_eq]
  · rfl

variable {P}

theorem dotD_rows_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < P.k) (hb₁ : b₁ < P.k) (ha₂ : a₂ < P.k) (hb₂ : b₂ < P.k) :
    dotD (top b) b (rowAt (krowsOf b α P.cls) a₁ b₁) (rowAt (krowsOf b α P.cls) a₂ b₂) 0 ≤ top b ∧
      sem (top b) (dotD (top b) b (rowAt (krowsOf b α P.cls) a₁ b₁)
        (rowAt (krowsOf b α P.cls) a₂ b₂) 0) β =
        dotB P.k (P.tbl (joinN b α β)) a₁ b₁ a₂ b₂ := by
  rw [rowAt_krowsOf, rowAt_krowsOf]
  obtain ⟨h1, h2⟩ := dotD_spec (α := α) hβ (nth [] (nth [] P.cls a₁) b₁)
    (nth [] (nth [] P.cls a₂) b₂) (Nat.zero_le (top b))
  refine ⟨h1, ?_⟩
  rw [h2, sem_zero (top_pos b), Bool.false_or,
    zip_any_eq_range (litB (joinN b α β)) P.k _ _ (checkRows_spec hrows ha₁ hb₁)
      (checkRows_spec hrows ha₂ hb₂)]
  rfl

theorem quadD_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b) (x : ℕ) {bad : ℕ}
    (hbad : bad < top b) :
    P.quadD (top b) (ones b) b (krowsOf b α P.cls) x bad < top b ∧
      (P.quadD (top b) (ones b) b (krowsOf b α P.cls) x bad).testBit β =
        (bad.testBit β || !P.quadAt (joinN b α β) x) := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  obtain ⟨hL1, hL2⟩ := dotD_rows_spec hrows (α := α) hβ (cvN_lt (hm (x / P.k / P.k / P.k))) (hm x)
    (hm (x / P.k / P.k)) (hm (x / P.k))
  obtain ⟨hR1, hR2⟩ := dotD_rows_spec hrows (α := α) hβ (hm (x / P.k / P.k / P.k))
    (hm (x / P.k / P.k)) (hm x) (cvN_lt (hm (x / P.k)))
  obtain ⟨h1, h2⟩ := neqS_spec hL1 hR1 hβ
  obtain ⟨g1, g2⟩ := badS_spec hbad h1 β
  rw [quadD, quadD4]
  refine ⟨g1, ?_⟩
  rw [g2, h2, hL2, hR2, quadAt, quadB]
  cases dotB P.k (P.tbl (joinN b α β)) (cvN P.s (x / P.k / P.k / P.k % P.k)) (x % P.k)
      (x / P.k / P.k % P.k) (x / P.k % P.k) <;>
    cases dotB P.k (P.tbl (joinN b α β)) (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k)
      (x % P.k) (cvN P.s (x / P.k % P.k)) <;> rfl

theorem evalD_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b) (quads : List ℕ)
    {bad : ℕ} (hbad : bad < top b) :
    P.evalD (top b) (ones b) b (krowsOf b α P.cls) quads bad < top b ∧
      (P.evalD (top b) (ones b) b (krowsOf b α P.cls) quads bad).testBit β =
        (bad.testBit β || quads.any fun x => !P.quadAt (joinN b α β) x) := by
  induction quads generalizing bad with
  | nil => exact ⟨hbad, by rw [evalD_nil]; simp⟩
  | cons x quads ih =>
    rw [evalD_cons]
    by_cases hon : bad = ones b
    · rw [beq_true hon]
      simp only [Bool.cond_true]
      rw [hon, testBit_ones]
      exact ⟨ones_lt_top b, by simp [hβ]⟩
    · rw [beq_false hon]
      simp only [Bool.cond_false]
      obtain ⟨hq1, hq2⟩ := quadD_spec hrows (α := α) hβ x hbad
      obtain ⟨h1, h2⟩ := ih hq1
      refine ⟨h1, ?_⟩
      rw [h2, hq2, List.any_cons, Bool.or_assoc]

variable (P)

/-- The number of models whose high variables are given by `α`, computed with shared tables. -/
noncomputable def leafS (b α : ℕ) : ℕ :=
  P.evalK (top b) (ones b) b (krowsOf b α P.cls) P.quads 0
    fun bad => popcount b (Nat.xor (ones b) bad)

variable {P}

theorem leafS_eq_leaf (hrows : P.checkRows = true) {b α : ℕ} (hα : α < 2 ^ (P.V - b)) :
    P.leafS b α = P.leaf b α := by
  have hbad : ∀ β < 2 ^ b, _ := fun β hβ =>
    evalD_spec hrows (α := α) hβ P.quads (top_pos b)
  have h0 := (hbad 0 (Nat.pow_pos (by decide))).1
  rw [leaf_eq hrows hα, leafS, evalK_eq]
  refine popcount_eq_card_filter_fun (xor_lt (ones_lt b) h0) (fun w => P.phi (join b α w)) ?_
  intro β hβ
  rw [testBit_xor, testBit_ones, (hbad β hβ).2, join_testBit, phi]
  simp only [hβ, decide_true, Nat.zero_testBit, Bool.false_or, Bool.true_xor]
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

end Problem

/-! ### Memoised residuals

The value of one side of a quadruple's condition only depends on the high variables occurring in
it. Masking `α` with these variables (`m`) and passing the result on in a canonical form makes
the expression `dotRL P b x (α &&& m)` identical for all leaves agreeing on these variables, so
that the kernel evaluates it once per declaration. Quadruples are processed in blocks, and the
accumulated violations of a block are again shared between leaves agreeing on the block. -/

/-- Reduce a small number and pass it on as a canonical expression. -/
noncomputable def forceK (r : ℕ) (k : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) r

theorem forceK_eq (r : ℕ) (k : ℕ → ℕ) : forceK r k = k r := by
  cases r <;> rfl

/-- Every high variable in `row` is selected by the mask `m`. -/
noncomputable def covers (b m : ℕ) (row : List ℕ) : Bool :=
  row.all fun c => Nat.blt c (Nat.add b 2) || Nat.testBit m (Nat.sub (Nat.sub c 2) b)

theorem kindOf_land {b α m c : ℕ}
    (h : (Nat.blt c (Nat.add b 2) || Nat.testBit m (c - 2 - b)) = true) :
    kindOf b (Nat.land α m) c = kindOf b α c := by
  match c with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
    by_cases hj : j < b
    · rw [kindOf_low hj, kindOf_low hj]
    · have hlt : Nat.blt (j + 2) (Nat.add b 2) = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
        change ¬ j + 2 < b + 2
        omega
      rw [hlt, Bool.false_or] at h
      have h' : m.testBit (j - b) = true := by simpa using h
      rw [kindOf_high hj, kindOf_high hj]
      change (if (α &&& m).testBit (j - b) = true then 1 else 0) = _
      rw [Nat.testBit_and, h', Bool.and_true]

theorem map_kindOf_land {b α m : ℕ} {row : List ℕ} (h : covers b m row = true) :
    row.map (kindOf b (Nat.land α m)) = row.map (kindOf b α) := by
  apply List.map_congr_left
  intro c hc
  exact kindOf_land (List.all_eq_true.mp h c hc)

/-- Equality of lists of numbers, as a Boolean. -/
def listBeq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && listBeq xs ys
  | _, _ => false

theorem listBeq_eq : ∀ {l₁ l₂ : List ℕ}, listBeq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    rw [listBeq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, listBeq_eq h.2]
  | [], _ :: _, h => by simp [listBeq] at h
  | _ :: _, [], h => by simp [listBeq] at h

namespace Problem

variable (P : Problem)

/-- The left side of the condition of the quadruple with code `x`, the high variables being `r`. -/
noncomputable def dotRL (b x r : ℕ) : ℕ :=
  dotD (top b) b
    (rowAt (krowsOf b r P.cls) (cvN P.s (Nat.mod (Nat.div (Nat.div (Nat.div x P.k) P.k) P.k) P.k))
      (Nat.mod x P.k))
    (rowAt (krowsOf b r P.cls) (Nat.mod (Nat.div (Nat.div x P.k) P.k) P.k)
      (Nat.mod (Nat.div x P.k) P.k)) 0

/-- The right side of the condition of the quadruple with code `x`, the high variables being
`r`. -/
noncomputable def dotRR (b x r : ℕ) : ℕ :=
  dotD (top b) b
    (rowAt (krowsOf b r P.cls) (Nat.mod (Nat.div (Nat.div (Nat.div x P.k) P.k) P.k) P.k)
      (Nat.mod (Nat.div (Nat.div x P.k) P.k) P.k))
    (rowAt (krowsOf b r P.cls) (Nat.mod x P.k) (cvN P.s (Nat.mod (Nat.div x P.k) P.k))) 0

theorem quadD_eq_dotR (b α x bad : ℕ) :
    P.quadD (top b) (ones b) b (krowsOf b α P.cls) x bad =
      badS bad (neqS (top b) (ones b) (P.dotRL b x α) (P.dotRR b x α)) := rfl

/-- The masks of an entry `(x, m₁, m₂)` select the high variables of the two sides of `x`. -/
noncomputable def coversQuad (b : ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  covers b e.2.1 (nth [] (nth [] P.cls
      (cvN P.s (Nat.mod (Nat.div (Nat.div (Nat.div e.1 P.k) P.k) P.k) P.k))) (Nat.mod e.1 P.k)) &&
    (covers b e.2.1 (nth [] (nth [] P.cls (Nat.mod (Nat.div (Nat.div e.1 P.k) P.k) P.k))
      (Nat.mod (Nat.div e.1 P.k) P.k)) &&
    (covers b e.2.2 (nth [] (nth [] P.cls
      (Nat.mod (Nat.div (Nat.div (Nat.div e.1 P.k) P.k) P.k) P.k))
      (Nat.mod (Nat.div (Nat.div e.1 P.k) P.k) P.k)) &&
    covers b e.2.2 (nth [] (nth [] P.cls (Nat.mod e.1 P.k))
      (cvN P.s (Nat.mod (Nat.div e.1 P.k) P.k)))))

variable {P}

theorem dotR_land {b α : ℕ} {e : ℕ × ℕ × ℕ} (h : P.coversQuad b e = true) :
    P.dotRL b e.1 (Nat.land α e.2.1) = P.dotRL b e.1 α ∧
      P.dotRR b e.1 (Nat.land α e.2.2) = P.dotRR b e.1 α := by
  simp only [coversQuad, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  constructor
  · unfold dotRL
    rw [rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf, map_kindOf_land h1,
      map_kindOf_land h2]
  · unfold dotRR
    rw [rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf, map_kindOf_land h3,
      map_kindOf_land h4]

variable (P)

/-- Accumulate the violations of a block of quadruples `(x, m₁, m₂)`. -/
noncomputable def blockK (b on α : ℕ) (blk : List (ℕ × ℕ × ℕ)) : ℕ → (ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => ℕ → (ℕ → ℕ) → ℕ) (fun acc k => k acc)
    (fun e _ ih acc k =>
      forceK (Nat.land α e.2.1) fun r₁ => forceK (Nat.land α e.2.2) fun r₂ =>
        ih (badS acc (neqS (top b) on (P.dotRL b e.1 r₁) (P.dotRR b e.1 r₂))) k) blk

/-- The value passed on by `blockK`. -/
noncomputable def blockD (b on α : ℕ) (blk : List (ℕ × ℕ × ℕ)) (acc : ℕ) : ℕ :=
  P.blockK b on α blk acc id

theorem blockK_cons (b on α : ℕ) (e : ℕ × ℕ × ℕ) (blk : List (ℕ × ℕ × ℕ)) (acc : ℕ)
    (k : ℕ → ℕ) : P.blockK b on α (e :: blk) acc k =
      forceK (Nat.land α e.2.1) fun r₁ => forceK (Nat.land α e.2.2) fun r₂ =>
        P.blockK b on α blk
          (badS acc (neqS (top b) on (P.dotRL b e.1 r₁) (P.dotRR b e.1 r₂))) k := rfl

theorem blockK_eq (b on α : ℕ) (blk : List (ℕ × ℕ × ℕ)) (acc : ℕ) (k : ℕ → ℕ) :
    P.blockK b on α blk acc k = k (P.blockD b on α blk acc) := by
  induction blk generalizing acc k with
  | nil => rfl
  | cons e blk ih =>
    unfold blockD
    rw [blockK_cons, blockK_cons, forceK_eq, forceK_eq, forceK_eq, forceK_eq, ih, ih _ id]
    rfl

theorem blockD_nil (b on α acc : ℕ) : P.blockD b on α [] acc = acc := rfl

theorem blockD_cons (b on α : ℕ) (e : ℕ × ℕ × ℕ) (blk : List (ℕ × ℕ × ℕ)) (acc : ℕ) :
    P.blockD b on α (e :: blk) acc = P.blockD b on α blk (badS acc (neqS (top b) on
      (P.dotRL b e.1 (Nat.land α e.2.1)) (P.dotRR b e.1 (Nat.land α e.2.2)))) := by
  unfold blockD
  rw [blockK_cons, forceK_eq, forceK_eq]

/-- Accumulate the violations of all blocks, stopping once every assignment is violated. -/
noncomputable def evalB (b on α : ℕ) (qm : List (List (ℕ × ℕ × ℕ))) : ℕ → (ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => ℕ → (ℕ → ℕ) → ℕ) (fun bad k => k bad)
    (fun blk _ ih bad k => bif Nat.beq bad on then k on
      else P.blockK b on α blk 0 (fun v => ih (badS bad v) k)) qm

/-- The value passed on by `evalB`. -/
noncomputable def evalBD (b on α : ℕ) (qm : List (List (ℕ × ℕ × ℕ))) (bad : ℕ) : ℕ :=
  P.evalB b on α qm bad id

theorem evalB_cons (b on α : ℕ) (blk : List (ℕ × ℕ × ℕ)) (qm : List (List (ℕ × ℕ × ℕ)))
    (bad : ℕ) (k : ℕ → ℕ) : P.evalB b on α (blk :: qm) bad k =
      bif Nat.beq bad on then k on
      else P.blockK b on α blk 0 (fun v => P.evalB b on α qm (badS bad v) k) := rfl

theorem evalB_eq (b on α : ℕ) (qm : List (List (ℕ × ℕ × ℕ))) (bad : ℕ) (k : ℕ → ℕ) :
    P.evalB b on α qm bad k = k (P.evalBD b on α qm bad) := by
  induction qm generalizing bad k with
  | nil => rfl
  | cons blk qm ih =>
    unfold evalBD
    rw [evalB_cons, evalB_cons]
    cases Nat.beq bad on
    · simp only [Bool.cond_false]
      rw [blockK_eq, blockK_eq, ih, ih _ id]
      rfl
    · rfl

theorem evalBD_nil (b on α bad : ℕ) : P.evalBD b on α [] bad = bad := rfl

theorem evalBD_cons (b on α : ℕ) (blk : List (ℕ × ℕ × ℕ)) (qm : List (List (ℕ × ℕ × ℕ)))
    (bad : ℕ) : P.evalBD b on α (blk :: qm) bad =
      bif Nat.beq bad on then on
      else P.evalBD b on α qm (badS bad (P.blockD b on α blk 0)) := by
  unfold evalBD
  rw [evalB_cons]
  cases Nat.beq bad on
  · simp only [Bool.cond_false]
    rw [blockK_eq, evalB_eq]
  · rfl

/-- The certificate for the memoised evaluation: the blocks `qm` list the quadruples of the
problem, each with masks selecting the high variables of its two sides. -/
noncomputable def checkQM (b : ℕ) (qm : List (List (ℕ × ℕ × ℕ))) : Bool :=
  listBeq (qm.flatten.map Prod.fst) P.quads && qm.all fun blk => blk.all (P.coversQuad b)

variable {P}

theorem blockD_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b)
    (blk : List (ℕ × ℕ × ℕ)) (hblk : blk.all (P.coversQuad b) = true) {acc : ℕ}
    (hacc : acc < top b) :
    P.blockD b (ones b) α blk acc < top b ∧
      (P.blockD b (ones b) α blk acc).testBit β =
        (acc.testBit β || blk.any fun e => !P.quadAt (joinN b α β) e.1) := by
  induction blk generalizing acc with
  | nil => exact ⟨hacc, by rw [blockD_nil]; simp⟩
  | cons e blk ih =>
    rw [List.all_cons, Bool.and_eq_true] at hblk
    obtain ⟨e1, e2⟩ := dotR_land (α := α) hblk.1
    rw [blockD_cons, e1, e2, ← quadD_eq_dotR]
    obtain ⟨hq1, hq2⟩ := quadD_spec hrows (α := α) hβ e.1 hacc
    obtain ⟨h1, h2⟩ := ih hblk.2 hq1
    refine ⟨h1, ?_⟩
    rw [h2, hq2, List.any_cons, Bool.or_assoc]

theorem evalBD_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b)
    (qm : List (List (ℕ × ℕ × ℕ))) (hqm : (qm.all fun blk => blk.all (P.coversQuad b)) = true)
    {bad : ℕ} (hbad : bad < top b) :
    P.evalBD b (ones b) α qm bad < top b ∧
      (P.evalBD b (ones b) α qm bad).testBit β =
        (bad.testBit β || (qm.flatten.map Prod.fst).any fun x => !P.quadAt (joinN b α β) x) := by
  induction qm generalizing bad with
  | nil => exact ⟨hbad, by rw [evalBD_nil]; simp⟩
  | cons blk qm ih =>
    rw [List.all_cons, Bool.and_eq_true] at hqm
    rw [evalBD_cons]
    by_cases hon : bad = ones b
    · rw [beq_true hon]
      simp only [Bool.cond_true]
      rw [hon, testBit_ones]
      exact ⟨ones_lt_top b, by simp [hβ]⟩
    · rw [beq_false hon]
      simp only [Bool.cond_false]
      obtain ⟨hb1, hb2⟩ := blockD_spec hrows (α := α) hβ blk hqm.1 (top_pos b)
      obtain ⟨hs1, hs2⟩ := badS_spec hbad hb1 β
      obtain ⟨h1, h2⟩ := ih hqm.2 hs1
      refine ⟨h1, ?_⟩
      rw [h2, hs2, hb2, List.flatten_cons, List.map_append, List.any_append]
      simp only [List.any_map, Nat.zero_testBit, Bool.false_or, Bool.or_assoc]
      rfl

variable (P)

/-- The number of models whose high variables are given by `α`, computed with memoised
residuals. -/
noncomputable def leafR (b : ℕ) (qm : List (List (ℕ × ℕ × ℕ))) (α : ℕ) : ℕ :=
  P.evalB b (ones b) α qm 0 fun bad => popcount b (Nat.xor (ones b) bad)

variable {P}

theorem leafR_eq_leaf (hrows : P.checkRows = true) {b : ℕ} {qm : List (List (ℕ × ℕ × ℕ))}
    (hqm : P.checkQM b qm = true) {α : ℕ} (hα : α < 2 ^ (P.V - b)) :
    P.leafR b qm α = P.leaf b α := by
  rw [checkQM, Bool.and_eq_true] at hqm
  have hquads := listBeq_eq hqm.1
  have hbad : ∀ β < 2 ^ b, _ := fun β hβ =>
    evalBD_spec hrows (α := α) hβ qm hqm.2 (top_pos b)
  have h0 := (hbad 0 (Nat.pow_pos (by decide))).1
  rw [leaf_eq hrows hα, leafR, evalB_eq]
  refine popcount_eq_card_filter_fun (xor_lt (ones_lt b) h0) (fun w => P.phi (join b α w)) ?_
  intro β hβ
  rw [testBit_xor, testBit_ones, (hbad β hβ).2, hquads, join_testBit, phi]
  simp only [hβ, decide_true, Nat.zero_testBit, Bool.false_or, Bool.true_xor]
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

/-- Check the values of a list of leaves `(α, value)` with the memoised evaluator. -/
noncomputable def checkLeavesR (P : Problem) (b : ℕ) (qm : List (List (ℕ × ℕ × ℕ))) :
    List (ℕ × ℕ) → Bool
  | [] => true
  | e :: es =>
    Nat.blt e.1 (2 ^ (P.V - b)) && (Nat.beq (P.leafR b qm e.1) e.2 && checkLeavesR P b qm es)

theorem checkLeavesR_spec (hrows : P.checkRows = true) {b : ℕ} {qm : List (List (ℕ × ℕ × ℕ))}
    (hqm : P.checkQM b qm = true) :
    ∀ {live : List (ℕ × ℕ)}, P.checkLeavesR b qm live = true → LiveProofs P b live
  | [], _ => trivial
  | e :: es, h => by
    rw [checkLeavesR, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact ⟨(leafR_eq_leaf hrows hqm h.1).symm.trans h.2.1, checkLeavesR_spec hrows hqm h.2.2⟩

/-- Check the values of a list of leaves `(α, value)`. -/
noncomputable def checkLeaves (P : Problem) (b : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | e :: es =>
    Nat.blt e.1 (2 ^ (P.V - b)) && (Nat.beq (P.leafS b e.1) e.2 && checkLeaves P b es)

theorem checkLeaves_spec (hrows : P.checkRows = true) {b : ℕ} :
    ∀ {live : List (ℕ × ℕ)}, P.checkLeaves b live = true → LiveProofs P b live
  | [], _ => trivial
  | e :: es, h => by
    rw [checkLeaves, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact ⟨(leafS_eq_leaf hrows h.1).symm.trans h.2.1, checkLeaves_spec hrows h.2.2⟩

end Problem

end RACert
