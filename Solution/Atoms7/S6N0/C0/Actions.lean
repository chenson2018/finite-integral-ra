/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0

open RACert RACert.Problem

def sym0 : Sym := { h := [0, 1, 2, 3, 4, 6, 5], hi := [0, 1, 2, 3, 4, 6, 5], vp := [0, 1, 2, 4, 3, 5, 6, 7, 8, 9, 11, 10, 12, 13, 14, 16, 15, 17, 19, 18, 20, 21, 22, 23, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 36, 37, 39, 38, 40, 42, 41, 44, 43, 45, 46, 48, 47, 50, 49, 51, 53, 52, 54, 55], vq := [0, 1, 2, 4, 3, 5, 6, 7, 8, 9, 11, 10, 12, 13, 14, 16, 15, 17, 19, 18, 20, 21, 22, 23, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 36, 37, 39, 38, 40, 42, 41, 44, 43, 45, 46, 48, 47, 50, 49, 51, 53, 52, 54, 55] }
def perm0 : List ℕ × List ℕ := ([1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 10, 11, 13, 12, 14, 16, 15, 18, 17, 19, 20, 22, 21, 24, 23, 25, 27, 26, 28, 29], [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 10, 11, 13, 12, 14, 16, 15, 18, 17, 19, 20, 22, 21, 24, 23, 25, 27, 26, 28, 29])
def keep0 : ℕ := 0xb0fb0000ffffb0fb0000000000000000ffffffffffffffffb0fb0000ffffb0fb0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb0fb0000ffffb0fb0000000000000000ffffffffffffffffb0fb0000ffffb0fb
def twice0 : ℕ := 0x20f20000ffff20f20000000000000000ffffffffffffffff20f20000ffff20f20000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20f20000ffff20f20000000000000000ffffffffffffffff20f20000ffff20f2
theorem bal0 : BalancedRows 10 keep0 twice0 (actBits 30 perm0.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow0 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm0.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm0.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym0) (e := perm0) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal0 j hj).1

def sym1 : Sym := { h := [0, 1, 2, 4, 3, 5, 6], hi := [0, 1, 2, 4, 3, 5, 6], vp := [0, 2, 1, 3, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 17, 18, 19, 14, 15, 16, 20, 21, 23, 22, 24, 25, 26, 27, 28, 29, 32, 33, 30, 31, 34, 35, 37, 36, 38, 39, 40, 43, 44, 41, 42, 45, 46, 49, 50, 47, 48, 51, 52, 53, 55, 54], vq := [0, 2, 1, 3, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 17, 18, 19, 14, 15, 16, 20, 21, 23, 22, 24, 25, 26, 27, 28, 29, 32, 33, 30, 31, 34, 35, 37, 36, 38, 39, 40, 43, 44, 41, 42, 45, 46, 49, 50, 47, 48, 51, 52, 53, 55, 54] }
def perm1 : List ℕ × List ℕ := ([0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 11, 10, 12, 13, 14, 17, 18, 15, 16, 19, 20, 23, 24, 21, 22, 25, 26, 27, 29, 28], [0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 11, 10, 12, 13, 14, 17, 18, 15, 16, 19, 20, 23, 24, 21, 22, 25, 26, 27, 29, 28])
def keep1 : ℕ := 0xffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffff
def twice1 : ℕ := 0xffff000000000000ffffffff00000000ffffffffffff00000000000000000000ffff000000000000ffffffff00000000ffffffffffff00000000000000000000ffff000000000000ffffffff00000000ffffffffffff00000000000000000000ffff000000000000ffffffff00000000ffffffffffff0000
theorem bal1 : BalancedRows 10 keep1 twice1 (actBits 30 perm1.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow1 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm1.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm1.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym1) (e := perm1) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal1 j hj).1

def sym2 : Sym := { h := [0, 1, 2, 4, 3, 6, 5], hi := [0, 1, 2, 4, 3, 6, 5], vp := [0, 2, 1, 4, 3, 5, 7, 6, 9, 8, 11, 10, 13, 12, 17, 19, 18, 14, 16, 15, 20, 21, 23, 22, 25, 24, 27, 26, 29, 28, 33, 32, 31, 30, 35, 34, 37, 36, 39, 38, 40, 44, 43, 42, 41, 45, 46, 50, 49, 48, 47, 51, 53, 52, 55, 54], vq := [0, 2, 1, 4, 3, 5, 7, 6, 9, 8, 11, 10, 13, 12, 17, 19, 18, 14, 16, 15, 20, 21, 23, 22, 25, 24, 27, 26, 29, 28, 33, 32, 31, 30, 35, 34, 37, 36, 39, 38, 40, 44, 43, 42, 41, 45, 46, 50, 49, 48, 47, 51, 53, 52, 55, 54] }
def perm2 : List ℕ × List ℕ := ([1, 0, 3, 2, 7, 6, 5, 4, 9, 8, 11, 10, 13, 12, 14, 18, 17, 16, 15, 19, 20, 24, 23, 22, 21, 25, 27, 26, 29, 28], [1, 0, 3, 2, 7, 6, 5, 4, 9, 8, 11, 10, 13, 12, 14, 18, 17, 16, 15, 19, 20, 24, 23, 22, 21, 25, 27, 26, 29, 28])
def keep2 : ℕ := 0xb0fb000000000000ffff0000b0fb0000ffffb0fbffff0000ffffffffffffb0fb0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb0fb000000000000ffff0000b0fb0000ffffb0fbffff0000ffffffffffffb0fb
def twice2 : ℕ := 0x20f2000000000000ffff000020f20000ffff20f2ffff0000ffffffffffff20f20000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff20f2000000000000ffff000020f20000ffff20f2ffff0000ffffffffffff20f2
theorem bal2 : BalancedRows 10 keep2 twice2 (actBits 30 perm2.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow2 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm2.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm2.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym2) (e := perm2) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal2 j hj).1

def sym3 : Sym := { h := [0, 1, 3, 2, 4, 5, 6], hi := [0, 1, 3, 2, 4, 5, 6], vp := [1, 0, 2, 3, 4, 6, 5, 7, 12, 14, 15, 16, 8, 17, 9, 10, 11, 13, 18, 19, 20, 22, 21, 23, 24, 25, 26, 27, 30, 31, 28, 29, 32, 33, 34, 35, 36, 40, 41, 42, 37, 38, 39, 43, 44, 45, 46, 47, 48, 52, 53, 54, 49, 50, 51, 55], vq := [1, 0, 2, 3, 4, 6, 5, 7, 12, 14, 15, 16, 8, 17, 9, 10, 11, 13, 18, 19, 20, 22, 21, 23, 24, 25, 26, 27, 30, 31, 28, 29, 32, 33, 34, 35, 36, 40, 41, 42, 37, 38, 39, 43, 44, 45, 46, 47, 48, 52, 53, 54, 49, 50, 51, 55] }
def perm3 : List ℕ × List ℕ := ([0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 10, 14, 15, 16, 11, 12, 13, 17, 18, 19, 20, 21, 22, 26, 27, 28, 23, 24, 25, 29], [0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 10, 14, 15, 16, 11, 12, 13, 17, 18, 19, 20, 21, 22, 26, 27, 28, 23, 24, 25, 29])
def keep3 : ℕ := 0xf000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0ffff
def twice3 : ℕ := 0xf000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff00000f000ff00fff0
theorem bal3 : BalancedRows 10 keep3 twice3 (actBits 30 perm3.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow3 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm3.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm3.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym3) (e := perm3) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal3 j hj).1

def sym4 : Sym := { h := [0, 1, 3, 2, 4, 6, 5], hi := [0, 1, 3, 2, 4, 6, 5], vp := [1, 0, 2, 4, 3, 6, 5, 7, 12, 14, 16, 15, 8, 17, 9, 11, 10, 13, 19, 18, 20, 22, 21, 23, 25, 24, 27, 26, 31, 30, 29, 28, 33, 32, 35, 34, 36, 40, 42, 41, 37, 39, 38, 44, 43, 45, 46, 48, 47, 53, 52, 54, 50, 49, 51, 55], vq := [1, 0, 2, 4, 3, 6, 5, 7, 12, 14, 16, 15, 8, 17, 9, 11, 10, 13, 19, 18, 20, 22, 21, 23, 25, 24, 27, 26, 31, 30, 29, 28, 33, 32, 35, 34, 36, 40, 42, 41, 37, 39, 38, 44, 43, 45, 46, 48, 47, 53, 52, 54, 50, 49, 51, 55] }
def perm4 : List ℕ × List ℕ := ([1, 0, 5, 4, 3, 2, 7, 6, 9, 8, 10, 14, 16, 15, 11, 13, 12, 18, 17, 19, 20, 22, 21, 27, 26, 28, 24, 23, 25, 29], [1, 0, 5, 4, 3, 2, 7, 6, 9, 8, 10, 14, 16, 15, 11, 13, 12, 18, 17, 19, 20, 22, 21, 27, 26, 28, 24, 23, 25, 29])
def keep4 : ℕ := 0xb000f0b0fbf0fffb0000000000000000ffffffffffffffffb000f0b0fbf0fffb0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb000f0b0fbf0fffb0000000000000000ffffffffffffffffb000f0b0fbf0fffb
def twice4 : ℕ := 0x2000f020f2f0fff20000000000000000ffffffffffffffff2000f020f2f0fff20000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2000f020f2f0fff20000000000000000ffffffffffffffff2000f020f2f0fff2
theorem bal4 : BalancedRows 10 keep4 twice4 (actBits 30 perm4.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow4 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm4.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm4.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym4) (e := perm4) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal4 j hj).1

def sym7 : Sym := { h := [0, 2, 1, 3, 4, 5, 6], hi := [0, 2, 1, 3, 4, 5, 6], vp := [5, 8, 9, 10, 11, 0, 12, 13, 1, 2, 3, 4, 6, 7, 14, 15, 16, 17, 18, 19, 21, 20, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 46, 47, 48, 49, 50, 51, 40, 41, 42, 43, 44, 45, 52, 53, 54, 55], vq := [5, 8, 9, 10, 11, 0, 12, 13, 1, 2, 3, 4, 6, 7, 14, 15, 16, 17, 18, 19, 21, 20, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 46, 47, 48, 49, 50, 51, 40, 41, 42, 43, 44, 45, 52, 53, 54, 55] }
def perm7 : List ℕ × List ℕ := ([2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 21, 22, 23, 24, 25, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29], [2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 21, 22, 23, 24, 25, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29])
def keep7 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def twice7 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce
theorem bal7 : BalancedRows 10 keep7 twice7 (actBits 30 perm7.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow7 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm7.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm7.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym7) (e := perm7) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal7 j hj).1

def sym8 : Sym := { h := [0, 2, 1, 3, 4, 6, 5], hi := [0, 2, 1, 3, 4, 6, 5], vp := [5, 8, 9, 11, 10, 0, 12, 13, 1, 2, 4, 3, 6, 7, 14, 16, 15, 17, 19, 18, 21, 20, 22, 23, 25, 24, 29, 28, 27, 26, 31, 30, 33, 32, 35, 34, 36, 37, 39, 38, 46, 48, 47, 50, 49, 51, 40, 42, 41, 44, 43, 45, 53, 52, 54, 55], vq := [5, 8, 9, 11, 10, 0, 12, 13, 1, 2, 4, 3, 6, 7, 14, 16, 15, 17, 19, 18, 21, 20, 22, 23, 25, 24, 29, 28, 27, 26, 31, 30, 33, 32, 35, 34, 36, 37, 39, 38, 46, 48, 47, 50, 49, 51, 40, 42, 41, 44, 43, 45, 53, 52, 54, 55] }
def perm8 : List ℕ × List ℕ := ([3, 2, 1, 0, 5, 4, 7, 6, 9, 8, 10, 11, 13, 12, 20, 22, 21, 24, 23, 25, 14, 16, 15, 18, 17, 19, 27, 26, 28, 29], [3, 2, 1, 0, 5, 4, 7, 6, 9, 8, 10, 11, 13, 12, 20, 22, 21, 24, 23, 25, 14, 16, 15, 18, 17, 19, 27, 26, 28, 29])
def keep8 : ℕ := 0x8aef0000ffff8aef0000000000000000ffffffffffffffff8aef0000ffff8aef0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffff8aef0000000000000000ffffffffffffffff8aef0000ffff8aef
def twice8 : ℕ := 0x8ae0000ffff08ae0000000000000000ffffffffffffffff08ae0000ffff08ae0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08ae0000ffff08ae0000000000000000ffffffffffffffff08ae0000ffff08ae
theorem bal8 : BalancedRows 10 keep8 twice8 (actBits 30 perm8.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow8 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm8.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm8.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym8) (e := perm8) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal8 j hj).1

def sym9 : Sym := { h := [0, 2, 1, 4, 3, 5, 6], hi := [0, 2, 1, 4, 3, 5, 6], vp := [5, 9, 8, 10, 11, 0, 13, 12, 2, 1, 3, 4, 7, 6, 17, 18, 19, 14, 15, 16, 21, 20, 23, 22, 24, 25, 28, 29, 26, 27, 32, 33, 30, 31, 34, 35, 37, 36, 38, 39, 46, 49, 50, 47, 48, 51, 40, 43, 44, 41, 42, 45, 52, 53, 55, 54], vq := [5, 9, 8, 10, 11, 0, 13, 12, 2, 1, 3, 4, 7, 6, 17, 18, 19, 14, 15, 16, 21, 20, 23, 22, 24, 25, 28, 29, 26, 27, 32, 33, 30, 31, 34, 35, 37, 36, 38, 39, 46, 49, 50, 47, 48, 51, 40, 43, 44, 41, 42, 45, 52, 53, 55, 54] }
def perm9 : List ℕ × List ℕ := ([2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 11, 10, 12, 13, 20, 23, 24, 21, 22, 25, 14, 17, 18, 15, 16, 19, 26, 27, 29, 28], [2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 11, 10, 12, 13, 20, 23, 24, 21, 22, 25, 14, 17, 18, 15, 16, 19, 26, 27, 29, 28])
def keep9 : ℕ := 0x8cef000000000000ffff8cef00000000ffffffff8cef0000ffffffffffff8cef8cef000000000000ffff8cef00000000ffffffff8cef0000ffffffffffff8cef8cef000000000000ffff8cef00000000ffffffff8cef0000ffffffffffff8cef8cef000000000000ffff8cef00000000ffffffff8cef0000ffffffffffff8cef
def twice9 : ℕ := 0x8ce000000000000ffff08ce00000000ffffffff08ce0000ffffffffffff08ce08ce000000000000ffff08ce00000000ffffffff08ce0000ffffffffffff08ce08ce000000000000ffff08ce00000000ffffffff08ce0000ffffffffffff08ce08ce000000000000ffff08ce00000000ffffffff08ce0000ffffffffffff08ce
theorem bal9 : BalancedRows 10 keep9 twice9 (actBits 30 perm9.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow9 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm9.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm9.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym9) (e := perm9) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal9 j hj).1

def sym10 : Sym := { h := [0, 2, 1, 4, 3, 6, 5], hi := [0, 2, 1, 4, 3, 6, 5], vp := [5, 9, 8, 11, 10, 0, 13, 12, 2, 1, 4, 3, 7, 6, 17, 19, 18, 14, 16, 15, 21, 20, 23, 22, 25, 24, 29, 28, 27, 26, 33, 32, 31, 30, 35, 34, 37, 36, 39, 38, 46, 50, 49, 48, 47, 51, 40, 44, 43, 42, 41, 45, 53, 52, 55, 54], vq := [5, 9, 8, 11, 10, 0, 13, 12, 2, 1, 4, 3, 7, 6, 17, 19, 18, 14, 16, 15, 21, 20, 23, 22, 25, 24, 29, 28, 27, 26, 33, 32, 31, 30, 35, 34, 37, 36, 39, 38, 46, 50, 49, 48, 47, 51, 40, 44, 43, 42, 41, 45, 53, 52, 55, 54] }
def perm10 : List ℕ × List ℕ := ([3, 2, 1, 0, 7, 6, 5, 4, 9, 8, 11, 10, 13, 12, 20, 24, 23, 22, 21, 25, 14, 18, 17, 16, 15, 19, 27, 26, 29, 28], [3, 2, 1, 0, 7, 6, 5, 4, 9, 8, 11, 10, 13, 12, 20, 24, 23, 22, 21, 25, 14, 18, 17, 16, 15, 19, 27, 26, 29, 28])
def keep10 : ℕ := 0x8aef000000000000ffff00008aef0000ffff8aefffff0000ffffffffffff8aef0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef000000000000ffff00008aef0000ffff8aefffff0000ffffffffffff8aef
def twice10 : ℕ := 0x8ae000000000000ffff000008ae0000ffff08aeffff0000ffffffffffff08ae0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff08ae000000000000ffff000008ae0000ffff08aeffff0000ffffffffffff08ae
theorem bal10 : BalancedRows 10 keep10 twice10 (actBits 30 perm10.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow10 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm10.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm10.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym10) (e := perm10) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal10 j hj).1

end RACert.S6N0.C0
