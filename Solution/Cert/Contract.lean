/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Cert.Row

/-!
# Contracting equal or forced cycle variables

Inside a fixed outer assignment, a quadruple can force a cycle or identify two
cycles. Each identification is checked by excluding the two unequal values.
The final coordinate map is a bijection on models. The contracted count can be
evaluated as one packed table or split into independent components in `Factors`.
-/

@[expose] public section
namespace RACert.Problem

/-- Codes 0 and 1 denote constants, and code j + 2 denotes coordinate j. -/
def outerCode (k H : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => if j < k then j + 2 else (H.testBit (j - k)).toNat

private theorem lit_toNat (v : ℕ → Bool) (x : Bool) : litB v x.toNat = x := by
  cases x <;> rfl

private theorem outerCode_valid (k H : ℕ) (w : Fin k → Bool) (c : ℕ) :
    litB (join k H w) (outerCode k H c) = litB (join k H w) c := by
  match c with
  | 0 | 1 => rfl
  | j + 2 =>
    by_cases hj : j < k
    · simp [outerCode, hj]
    · cases he : H.testBit (j - k) <;> simp [outerCode, hj, he, litB, join]

abbrev Identification := ℕ × ℕ × ℕ

def replaceCode (f : ℕ → ℕ) (x y : ℕ) : ℕ → ℕ :=
  fun c => if f c == x then y else f c

def contraction (f : ℕ → ℕ) : List Identification → ℕ → ℕ
  | [] => f
  | (x,y,_)::ss => contraction (replaceCode f x y) ss

/-- The witness bounds on a cofactor with one code false and the other true. -/
def unequalBounds (f : ℕ → ℕ) (z o : ℕ) : Bounds := fun c =>
  let j := f c
  if j == 0 || j == z then (0,0)
  else if j == 1 || j == o then (1,1)
  else (0,1)

noncomputable def excludes (P : Problem) (f : ℕ → ℕ) (z o q : ℕ) : Bool :=
  z == 1 || o == 0 || (P.rowBad 0 (unequalBounds f z o) q).testBit 0

private theorem excludes_sound {P : Problem} (hc : P.check = true) {v : ℕ → Bool}
    (hv : P.phi v = true) {f : ℕ → ℕ} (hf : ∀ c, litB v (f c) = litB v c)
    {z o q : ℕ} (he : P.excludes f z o q = true) (hz : litB v z = false)
    (ho : litB v o = true) : False := by
  have hz1 : z ≠ 1 := by rintro rfl; contradiction
  have ho0 : o ≠ 0 := by rintro rfl; contradiction
  have hzo : o ≠ z := by rintro rfl; simp_all
  have hb : bounded (unequalBounds f z o) 0 v := by
    intro c
    rw [← hf c]
    by_cases h0 : f c = 0
    · simp [unequalBounds, h0, litB]
    by_cases h1 : f c = z
    · simp [unequalBounds, h1, hz]
    by_cases h2 : f c = 1
    · simp [unequalBounds, h2, Ne.symm hz1, litB]
    by_cases h3 : f c = o
    · simp [unequalBounds, h3, ho0, hzo, ho]
    simp [unequalBounds, h0, h1, h2, h3]
  have := rowBad_sound hc hv (d := 0) (by decide) hb q
  simp [excludes, hz1, ho0, this] at he

noncomputable def checkContraction (P : Problem) (f : ℕ → ℕ) : List Identification → Bool
  | [] => true
  | (x,y,q)::ss => P.excludes f x y q && (P.excludes f y x q &&
      P.checkContraction (replaceCode f x y) ss)

theorem contraction_valid {P : Problem} (hc : P.check = true) {v : ℕ → Bool}
    (hv : P.phi v = true) {f : ℕ → ℕ} (hf : ∀ c, litB v (f c) = litB v c)
    (ss : List Identification) (hs : P.checkContraction f ss = true) :
    ∀ c, litB v (contraction f ss c) = litB v c := by
  induction ss generalizing f with
  | nil => exact hf
  | cons s ss ih =>
    obtain ⟨x,y,q⟩ := s
    rw [checkContraction, Bool.and_eq_true, Bool.and_eq_true] at hs
    have eq : litB v x = litB v y := by
      cases hx : litB v x <;> cases hy : litB v y <;> try rfl
      · exact (excludes_sound hc hv hf hs.1 hx hy).elim
      · exact (excludes_sound hc hv hf hs.2.1 hy hx).elim
    apply ih _ hs.2.2
    intro c
    by_cases he : f c = x
    · simp only [replaceCode, he, beq_self_eq_true, ↓reduceIte]
      exact eq.symm.trans (he ▸ hf c)
    · simpa [replaceCode, he] using hf c

def decodeRow {k b : ℕ} (cs : List ℕ) (u : Fin b → Bool) (i : Fin k) : Bool :=
  litB (extFin b u) (cs.getD i.val 0)

def encodeRow {k b : ℕ} (ids : List ℕ) (w : Fin k → Bool) (j : Fin b) : Bool :=
  extFin k w (ids.getD j.val 0)

def expandCode (ids : List ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => ids.getD j 0 + 2

def inRange (b : ℕ) : ℕ → Bool
  | 0 | 1 => true
  | j + 2 => decide (j < b)

noncomputable def checkCoordinates (k b : ℕ) (ids cs : List ℕ) (f : ℕ → ℕ) : Bool :=
  (allRange b fun j => decide (ids.getD j 0 < k) && (cs.getD (ids.getD j 0) 0 == j + 2)) &&
  (allRange k fun i => inRange b (cs.getD i 0) && (expandCode ids (cs.getD i 0) == f (i + 2)))

private theorem inverses {k b H : ℕ} {ids cs : List ℕ} {f : ℕ → ℕ}
    (hh : checkCoordinates k b ids cs f = true) :
    (∀ u : Fin b → Bool, encodeRow ids (decodeRow (k := k) cs u) = u) ∧
    (∀ w : Fin k → Bool, (∀ c, litB (join k H w) (f c) = litB (join k H w) c) →
      decodeRow cs (encodeRow (b := b) ids w) = w) := by
  simp only [checkCoordinates, Bool.and_eq_true, allRange_iff, decide_eq_true_iff,
    beq_iff_eq] at hh
  constructor
  · intro u
    funext j
    have hj := hh.1 j j.isLt
    simp only [encodeRow, extFin, hj.1, ↓reduceDIte, decodeRow, hj.2, litB, j.isLt]
  · intro w hw
    funext i
    have hi := hh.2 i i.isLt
    have e := hw (i.val + 2)
    rw [← hi.2] at e
    change litB (extFin b (encodeRow ids w)) (cs.getD i.val 0) = w i
    simp only [litB, join, i.isLt, ↓reduceDIte] at e
    cases he : cs.getD i.val 0 with
    | zero => simpa only [he, expandCode, litB] using e
    | succ j =>
      cases j with
      | zero => simpa only [he, expandCode, litB] using e
      | succ j =>
        have hj : j < b := by simpa only [he, inRange, decide_eq_true_eq] using hi.1
        have hj' := (hh.1 j hj).1
        simpa only [he, expandCode, litB, join, extFin, encodeRow, hj, hj', ↓reduceDIte] using e

/-- The packed column of an input code after contraction. -/
def compactCol (k b H : ℕ) (cs : List ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => ones b
  | j + 2 => if j < k then match cs.getD j 0 with
      | 0 => 0
      | 1 => ones b
      | t + 2 => pat b t
    else if H.testBit (j - k) then ones b else 0

private theorem compactCol_bit {k b H β : ℕ} {cs : List ℕ} (hβ : β < 2 ^ b)
    (hc : ∀ i < k, inRange b (cs.getD i 0) = true) (c : ℕ) :
    (compactCol k b H cs c).testBit β =
      litB (join k H (decodeRow cs (fun i : Fin b => β.testBit i))) c := by
  match c with
  | 0 | 1 => simp [compactCol, litB, testBit_ones, hβ]
  | j + 2 =>
    by_cases hj : j < k
    · simp only [compactCol, hj, ↓reduceIte, litB, join, decodeRow]
      cases he : cs.getD j 0 with
      | zero => simp
      | succ i =>
        cases i with
        | zero => simp [testBit_ones, hβ]
        | succ i =>
          have hi : i < b := by simpa only [he, inRange, decide_eq_true_eq] using hc j hj
          simp [extFin, hi, testBit_pat, hβ]
    · cases he : H.testBit (j - k) <;> simp [compactCol, hj, he, litB, join, testBit_ones, hβ]

noncomputable def compactCount (P : Problem) (k b H : ℕ) (cs : List ℕ) : ℕ :=
  let col := compactCol k b H cs
  let bad := unionBits (fun x =>
    let r := x / P.k / P.k / P.k % P.k
    let u := x / P.k / P.k % P.k
    let t := x / P.k % P.k
    let p := x % P.k
    Nat.xor (dotBits P col (cvN P.s r) p u t) (dotBits P col r u p (cvN P.s t))) P.quads
  popcountF b (Nat.land (ones b) (Nat.xor (ones b) bad))

theorem leaf_contracted_card {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k b H : ℕ} (hH : H < 2 ^ (P.V - k)) {ss : List Identification} {ids cs : List ℕ}
    (hs : P.checkContraction (outerCode k H) ss = true)
    (hm : checkCoordinates k b ids cs (contraction (outerCode k H) ss) = true) :
    P.leaf k H = (Finset.univ.filter fun u : Fin b → Bool =>
      P.phi (join k H (decodeRow cs u)) = true).card := by
  let F (w : Fin k → Bool) := P.phi (join k H w)
  let G (u : Fin b → Bool) := F (decodeRow cs u)
  have hi := inverses (H := H) hm
  have eq : (Finset.univ.filter fun w => F w = true).card =
      (Finset.univ.filter fun u => G u = true).card := by
    apply Finset.card_bij' (fun w _ => encodeRow ids w) (fun u _ => decodeRow cs u)
    · intro w hw
      have hv := (Finset.mem_filter.mp hw).2
      have he := hi.2 w (contraction_valid hc hv (outerCode_valid k H w) ss hs)
      simpa [G, he] using hv
    · intro u hu
      simpa [G] using hu
    · intro w hw
      exact hi.2 w (contraction_valid hc (Finset.mem_filter.mp hw).2 (outerCode_valid k H w) ss hs)
    · intro u _
      exact hi.1 u
  rw [leaf_eq hr hH, ← show (Finset.univ.filter fun w => F w = true).card = _ from rfl, eq]

theorem leaf_contract {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k b H : ℕ} (hH : H < 2 ^ (P.V - k)) {ss : List Identification} {ids cs : List ℕ}
    (hs : P.checkContraction (outerCode k H) ss = true)
    (hm : checkCoordinates k b ids cs (contraction (outerCode k H) ss) = true) :
    P.leaf k H = P.compactCount k b H cs := by
  let F (w : Fin k → Bool) := P.phi (join k H w)
  let G (u : Fin b → Bool) := F (decodeRow cs u)
  rw [leaf_contracted_card hc hr hH hs hm]
  symm
  unfold compactCount
  apply popcountF_eq_card_filter_fun (land_lt_left (ones_lt b)) G
  intro β hβ
  have ranges := hm
  simp only [checkCoordinates, Bool.and_eq_true, allRange_iff] at ranges
  have hl := compactCol_bit (k := k) (b := b) (H := H) (cs := cs) hβ
    (fun i h => (ranges.2 i h).1)
  simp only [testBit_land, testBit_ones, hβ, decide_true, testBit_xor, unionBits_bit,
    Bool.true_and, Bool.true_xor, G, F, phi, quadAt, quadB, dotBits, unionBits_bit, hl, dotB, tbl]
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', List.any_eq_false, List.all_eq_true, beq_iff_eq]
  apply forall₂_congr
  intro q _
  generalize ((List.range _).any _) = l
  generalize ((List.range _).any _) = r
  cases l <;> cases r <;> decide

/-- A contradiction revealed by earlier identifications discharges the whole cofactor. -/
theorem leaf_contract_zero {P : Problem} (hc : P.check = true) (hr : P.checkRows = true)
    {k H : ℕ} (hH : H < 2 ^ (P.V - k)) {ss : List Identification} {q : ℕ}
    (hs : P.checkContraction (outerCode k H) ss = true)
    (he : P.excludes (contraction (outerCode k H) ss) 0 1 q = true) :
    P.leaf k H = 0 := by
  rw [leaf_eq hr hH, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hv
  exact excludes_sound hc hv (contraction_valid hc hv (outerCode_valid k H w) ss hs) he rfl rfl

end RACert.Problem
