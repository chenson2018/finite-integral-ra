/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Defs

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0

open RACert RACert.Problem

def os4 : Sym := { h := [0, 1, 3, 2, 4, 5, 6], hi := [0, 1, 3, 2, 4, 5, 6], vp := [1, 0, 2, 3, 24, 5, 6, 7, 26, 28, 29, 14, 31, 15, 11, 13, 16, 17, 18, 19, 20, 22, 21, 23, 4, 25, 8, 30, 9, 10, 27, 12, 32, 33, 34, 38, 39, 40, 35, 36, 37, 41, 42, 43, 45, 44, 48, 49, 46, 47], vq := [1, 0, 2, 3, 24, 5, 6, 7, 26, 28, 29, 14, 31, 15, 11, 13, 16, 17, 18, 19, 20, 22, 21, 23, 4, 25, 8, 30, 9, 10, 27, 12, 32, 33, 34, 38, 39, 40, 35, 36, 37, 41, 42, 43, 45, 44, 48, 49, 46, 47] }
def op4 : List ℕ × List ℕ := ([0, 4, 5, 6, 1, 2, 3, 7, 8, 9, 11, 10, 14, 15, 12, 13], [0, 4, 5, 6, 1, 2, 3, 7, 8, 9, 11, 10, 14, 15, 12, 13])
theorem orient4 {h v n : ℕ} (hh : h < 2 ^ 16) (hi : actBits 16 op4.1 h = v) (hv : P.leaf 34 v = n) : P.leaf 34 h = n := by
  subst v
  exact (leaf_actBits (S := os4) (e := op4) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os5 : Sym := { h := [0, 3, 1, 2, 4, 6, 5], hi := [0, 2, 3, 1, 4, 6, 5], vp := [24, 26, 28, 29, 1, 15, 31, 14, 0, 2, 3, 7, 6, 5, 13, 11, 17, 16, 18, 19, 22, 20, 21, 23, 8, 30, 4, 25, 9, 10, 27, 12, 32, 33, 34, 38, 39, 40, 43, 44, 45, 49, 48, 35, 37, 36, 42, 41, 47, 46], vq := [8, 4, 9, 10, 26, 13, 12, 11, 24, 28, 29, 15, 31, 14, 7, 5, 17, 16, 18, 19, 21, 22, 20, 23, 0, 27, 1, 30, 2, 3, 25, 6, 32, 33, 34, 43, 45, 44, 35, 36, 37, 47, 46, 38, 39, 40, 49, 48, 42, 41] }
def op5 : List ℕ × List ℕ := ([0, 4, 5, 6, 9, 10, 11, 15, 14, 1, 3, 2, 8, 7, 13, 12], [0, 9, 11, 10, 1, 2, 3, 13, 12, 4, 5, 6, 15, 14, 8, 7])
theorem orient5 {h v n : ℕ} (hh : h < 2 ^ 16) (hi : actBits 16 op5.1 h = v) (hv : P.leaf 34 v = n) : P.leaf 34 h = n := by
  subst v
  exact (leaf_actBits (S := os5) (e := op5) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os24 : Sym := { h := [0, 1, 3, 4, 2, 5, 6], hi := [0, 1, 4, 2, 3, 5, 6], vp := [1, 2, 0, 3, 24, 5, 6, 7, 28, 26, 29, 14, 31, 15, 16, 17, 11, 13, 18, 19, 20, 22, 23, 21, 25, 4, 30, 8, 27, 32, 9, 33, 10, 12, 38, 34, 39, 40, 35, 41, 42, 36, 37, 43, 48, 49, 45, 44, 47, 46], vq := [2, 0, 1, 3, 25, 5, 6, 7, 27, 30, 32, 16, 33, 17, 11, 13, 14, 15, 18, 19, 20, 23, 21, 22, 4, 24, 9, 28, 8, 10, 26, 12, 29, 31, 35, 38, 41, 42, 34, 36, 37, 39, 40, 43, 47, 46, 49, 48, 44, 45] }
def op24 : List ℕ × List ℕ := ([4, 0, 5, 6, 1, 7, 8, 2, 3, 9, 14, 15, 11, 10, 13, 12], [1, 4, 7, 8, 0, 2, 3, 5, 6, 9, 13, 12, 15, 14, 10, 11])
theorem orient24 {h v n : ℕ} (hh : h < 2 ^ 16) (hi : actBits 16 op24.1 h = v) (hv : P.leaf 34 v = n) : P.leaf 34 h = n := by
  subst v
  exact (leaf_actBits (S := os24) (e := op24) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os25 : Sym := { h := [0, 3, 1, 4, 2, 6, 5], hi := [0, 2, 4, 1, 3, 6, 5], vp := [24, 28, 26, 29, 1, 15, 31, 14, 2, 0, 3, 7, 6, 5, 17, 16, 13, 11, 18, 19, 22, 20, 23, 21, 30, 8, 25, 4, 27, 32, 9, 33, 10, 12, 38, 34, 39, 40, 43, 49, 48, 44, 45, 35, 42, 41, 37, 36, 46, 47], vq := [9, 4, 8, 10, 27, 13, 12, 11, 25, 30, 32, 17, 33, 16, 7, 5, 15, 14, 18, 19, 21, 23, 20, 22, 0, 26, 2, 28, 1, 3, 24, 6, 29, 31, 35, 43, 47, 46, 34, 36, 37, 45, 44, 38, 41, 42, 48, 49, 40, 39] }
def op25 : List ℕ × List ℕ := ([4, 0, 5, 6, 9, 15, 14, 10, 11, 1, 8, 7, 3, 2, 12, 13], [1, 9, 13, 12, 0, 2, 3, 11, 10, 4, 7, 8, 14, 15, 6, 5])
theorem orient25 {h v n : ℕ} (hh : h < 2 ^ 16) (hi : actBits 16 op25.1 h = v) (hv : P.leaf 34 v = n) : P.leaf 34 h = n := by
  subst v
  exact (leaf_actBits (S := os25) (e := op25) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os32 : Sym := { h := [0, 3, 4, 1, 2, 5, 6], hi := [0, 3, 4, 1, 2, 5, 6], vp := [28, 24, 26, 29, 30, 14, 31, 15, 25, 27, 32, 16, 33, 17, 5, 7, 11, 13, 18, 19, 22, 23, 20, 21, 1, 8, 2, 9, 0, 3, 4, 6, 10, 12, 38, 43, 48, 49, 34, 40, 39, 45, 44, 35, 42, 41, 47, 46, 36, 37], vq := [28, 24, 26, 29, 30, 14, 31, 15, 25, 27, 32, 16, 33, 17, 5, 7, 11, 13, 18, 19, 22, 23, 20, 21, 1, 8, 2, 9, 0, 3, 4, 6, 10, 12, 38, 43, 48, 49, 34, 40, 39, 45, 44, 35, 42, 41, 47, 46, 36, 37] }
def op32 : List ℕ × List ℕ := ([4, 9, 14, 15, 0, 6, 5, 11, 10, 1, 8, 7, 13, 12, 2, 3], [4, 9, 14, 15, 0, 6, 5, 11, 10, 1, 8, 7, 13, 12, 2, 3])
theorem orient32 {h v n : ℕ} (hh : h < 2 ^ 16) (hi : actBits 16 op32.1 h = v) (hv : P.leaf 34 v = n) : P.leaf 34 h = n := by
  subst v
  exact (leaf_actBits (S := os32) (e := op32) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def sym0 : Sym := { h := [0, 1, 2, 4, 3, 5, 6], hi := [0, 1, 2, 4, 3, 5, 6], vp := [0, 2, 1, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 16, 17, 14, 15, 18, 19, 20, 21, 23, 22, 25, 24, 27, 26, 30, 32, 28, 33, 29, 31, 35, 34, 36, 37, 38, 41, 42, 39, 40, 43, 46, 47, 44, 45, 49, 48], vq := [0, 2, 1, 3, 4, 5, 6, 7, 9, 8, 10, 11, 12, 13, 16, 17, 14, 15, 18, 19, 20, 21, 23, 22, 25, 24, 27, 26, 30, 32, 28, 33, 29, 31, 35, 34, 36, 37, 38, 41, 42, 39, 40, 43, 46, 47, 44, 45, 49, 48] }
def perm0 : List ℕ × List ℕ := ([1, 0, 3, 2, 6, 8, 4, 9, 5, 7, 11, 10, 12, 13, 14, 17, 18, 15, 16, 19, 22, 23, 20, 21, 25, 24], [1, 0, 3, 2, 6, 8, 4, 9, 5, 7, 11, 10, 12, 13, 14, 17, 18, 15, 16, 19, 22, 23, 20, 21, 25, 24])
def keep0 : ℕ := 0xb0fb000000000000ffffb0fb0000000000000000000000000000000000000000ffffffffb0fb0000ffffffffffffb0fb00000000000000000000000000000000ffffffffffffffffffffffffffffffffb0fb000000000000ffffb0fb00000000ffffffffffffffffffffffffffffffffffffffffb0fb0000ffffffffffffb0fb
def twice0 : ℕ := 0x20f2000000000000ffff20f20000000000000000000000000000000000000000ffffffff20f20000ffffffffffff20f200000000000000000000000000000000ffffffffffffffffffffffffffffffff20f2000000000000ffff20f200000000ffffffffffffffffffffffffffffffffffffffff20f20000ffffffffffff20f2
theorem bal0 : BalancedRows 10 keep0 twice0 (actBits 26 perm0.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow0 {H : ℕ} (hh : H < 2 ^ 16) (hs : actBits 26 perm0.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 24 (1024 * H + actBits 26 perm0.1 j) = P.leaf 24 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym0) (e := perm0) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal0 j hj).1

def sym1 : Sym := { h := [0, 1, 2, 4, 3, 6, 5], hi := [0, 1, 2, 4, 3, 6, 5], vp := [0, 2, 1, 3, 4, 7, 6, 5, 9, 8, 10, 13, 12, 11, 17, 16, 15, 14, 18, 19, 20, 21, 23, 22, 25, 24, 27, 26, 30, 32, 28, 33, 29, 31, 35, 34, 37, 36, 38, 42, 41, 40, 39, 43, 47, 46, 45, 44, 48, 49], vq := [0, 2, 1, 3, 4, 7, 6, 5, 9, 8, 10, 13, 12, 11, 17, 16, 15, 14, 18, 19, 20, 21, 23, 22, 25, 24, 27, 26, 30, 32, 28, 33, 29, 31, 35, 34, 37, 36, 38, 42, 41, 40, 39, 43, 47, 46, 45, 44, 48, 49] }
def perm1 : List ℕ × List ℕ := ([1, 0, 3, 2, 6, 8, 4, 9, 5, 7, 11, 10, 13, 12, 14, 18, 17, 16, 15, 19, 23, 22, 21, 20, 24, 25], [1, 0, 3, 2, 6, 8, 4, 9, 5, 7, 11, 10, 13, 12, 14, 18, 17, 16, 15, 19, 23, 22, 21, 20, 24, 25])
def keep1 : ℕ := 0xb0fb000000000000ffffb0fb0000000000000000000000000000000000000000ffffffffb0fb0000ffffffffffffb0fb00000000000000000000000000000000ffffffffffffffffffffffffffffffffb0fb000000000000ffffb0fb00000000ffffffffffffffffffffffffffffffffffffffffb0fb0000ffffffffffffb0fb
def twice1 : ℕ := 0x20f2000000000000ffff20f20000000000000000000000000000000000000000ffffffff20f20000ffffffffffff20f200000000000000000000000000000000ffffffffffffffffffffffffffffffff20f2000000000000ffff20f200000000ffffffffffffffffffffffffffffffffffffffff20f20000ffffffffffff20f2
theorem bal1 : BalancedRows 10 keep1 twice1 (actBits 26 perm1.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow1 {H : ℕ} (hh : H < 2 ^ 16) (hs : actBits 26 perm1.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 24 (1024 * H + actBits 26 perm1.1 j) = P.leaf 24 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym1) (e := perm1) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal1 j hj).1

def sym2 : Sym := { h := [0, 2, 1, 3, 4, 5, 6], hi := [0, 2, 1, 3, 4, 5, 6], vp := [4, 8, 9, 10, 0, 11, 12, 13, 1, 2, 3, 5, 6, 7, 14, 15, 16, 17, 18, 19, 21, 20, 22, 23, 26, 27, 24, 25, 28, 29, 30, 31, 32, 33, 34, 35, 37, 36, 43, 44, 45, 46, 47, 38, 39, 40, 41, 42, 48, 49], vq := [4, 8, 9, 10, 0, 11, 12, 13, 1, 2, 3, 5, 6, 7, 14, 15, 16, 17, 18, 19, 21, 20, 22, 23, 26, 27, 24, 25, 28, 29, 30, 31, 32, 33, 34, 35, 37, 36, 43, 44, 45, 46, 47, 38, 39, 40, 41, 42, 48, 49] }
def perm2 : List ℕ × List ℕ := ([2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 19, 20, 21, 22, 23, 14, 15, 16, 17, 18, 24, 25], [2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 19, 20, 21, 22, 23, 14, 15, 16, 17, 18, 24, 25])
def keep2 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def twice2 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce
theorem bal2 : BalancedRows 10 keep2 twice2 (actBits 26 perm2.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow2 {H : ℕ} (hh : H < 2 ^ 16) (hs : actBits 26 perm2.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 24 (1024 * H + actBits 26 perm2.1 j) = P.leaf 24 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym2) (e := perm2) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal2 j hj).1

def sym3 : Sym := { h := [0, 2, 1, 3, 4, 6, 5], hi := [0, 2, 1, 3, 4, 6, 5], vp := [4, 8, 9, 10, 0, 13, 12, 11, 1, 2, 3, 7, 6, 5, 15, 14, 17, 16, 18, 19, 21, 20, 22, 23, 26, 27, 24, 25, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 43, 45, 44, 47, 46, 38, 40, 39, 42, 41, 49, 48], vq := [4, 8, 9, 10, 0, 13, 12, 11, 1, 2, 3, 7, 6, 5, 15, 14, 17, 16, 18, 19, 21, 20, 22, 23, 26, 27, 24, 25, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 43, 45, 44, 47, 46, 38, 40, 39, 42, 41, 49, 48] }
def perm3 : List ℕ × List ℕ := ([2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 19, 21, 20, 23, 22, 14, 16, 15, 18, 17, 25, 24], [2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 19, 21, 20, 23, 22, 14, 16, 15, 18, 17, 25, 24])
def keep3 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def twice3 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce
theorem bal3 : BalancedRows 10 keep3 twice3 (actBits 26 perm3.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow3 {H : ℕ} (hh : H < 2 ^ 16) (hs : actBits 26 perm3.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 24 (1024 * H + actBits 26 perm3.1 j) = P.leaf 24 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym3) (e := perm3) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal3 j hj).1

def sym4 : Sym := { h := [0, 2, 1, 4, 3, 5, 6], hi := [0, 2, 1, 4, 3, 5, 6], vp := [4, 9, 8, 10, 0, 11, 12, 13, 2, 1, 3, 5, 6, 7, 16, 17, 14, 15, 18, 19, 21, 20, 23, 22, 27, 26, 25, 24, 30, 32, 28, 33, 29, 31, 35, 34, 37, 36, 43, 46, 47, 44, 45, 38, 41, 42, 39, 40, 49, 48], vq := [4, 9, 8, 10, 0, 11, 12, 13, 2, 1, 3, 5, 6, 7, 16, 17, 14, 15, 18, 19, 21, 20, 23, 22, 27, 26, 25, 24, 30, 32, 28, 33, 29, 31, 35, 34, 37, 36, 43, 46, 47, 44, 45, 38, 41, 42, 39, 40, 49, 48] }
def perm4 : List ℕ × List ℕ := ([3, 2, 1, 0, 6, 8, 4, 9, 5, 7, 11, 10, 13, 12, 19, 22, 23, 20, 21, 14, 17, 18, 15, 16, 25, 24], [3, 2, 1, 0, 6, 8, 4, 9, 5, 7, 11, 10, 13, 12, 19, 22, 23, 20, 21, 14, 17, 18, 15, 16, 25, 24])
def keep4 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffff8aef000000000000ffff8aef00000000ffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def twice4 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff08ae000000000000ffff08ae00000000ffffffffffffffffffffffffffffffffffffffff08ae0000ffffffffffff08ae
theorem bal4 : BalancedRows 10 keep4 twice4 (actBits 26 perm4.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow4 {H : ℕ} (hh : H < 2 ^ 16) (hs : actBits 26 perm4.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 24 (1024 * H + actBits 26 perm4.1 j) = P.leaf 24 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym4) (e := perm4) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal4 j hj).1

def sym5 : Sym := { h := [0, 2, 1, 4, 3, 6, 5], hi := [0, 2, 1, 4, 3, 6, 5], vp := [4, 9, 8, 10, 0, 13, 12, 11, 2, 1, 3, 7, 6, 5, 17, 16, 15, 14, 18, 19, 21, 20, 23, 22, 27, 26, 25, 24, 30, 32, 28, 33, 29, 31, 35, 34, 36, 37, 43, 47, 46, 45, 44, 38, 42, 41, 40, 39, 48, 49], vq := [4, 9, 8, 10, 0, 13, 12, 11, 2, 1, 3, 7, 6, 5, 17, 16, 15, 14, 18, 19, 21, 20, 23, 22, 27, 26, 25, 24, 30, 32, 28, 33, 29, 31, 35, 34, 36, 37, 43, 47, 46, 45, 44, 38, 42, 41, 40, 39, 48, 49] }
def perm5 : List ℕ × List ℕ := ([3, 2, 1, 0, 6, 8, 4, 9, 5, 7, 11, 10, 12, 13, 19, 23, 22, 21, 20, 14, 18, 17, 16, 15, 24, 25], [3, 2, 1, 0, 6, 8, 4, 9, 5, 7, 11, 10, 12, 13, 19, 23, 22, 21, 20, 14, 18, 17, 16, 15, 24, 25])
def keep5 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffff8aef000000000000ffff8aef00000000ffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def twice5 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff08ae000000000000ffff08ae00000000ffffffffffffffffffffffffffffffffffffffff08ae0000ffffffffffff08ae
theorem bal5 : BalancedRows 10 keep5 twice5 (actBits 26 perm5.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow5 {H : ℕ} (hh : H < 2 ^ 16) (hs : actBits 26 perm5.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 24 (1024 * H + actBits 26 perm5.1 j) = P.leaf 24 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym5) (e := perm5) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal5 j hj).1

end RACert.S4N1.C0
