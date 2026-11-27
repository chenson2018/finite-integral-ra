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
