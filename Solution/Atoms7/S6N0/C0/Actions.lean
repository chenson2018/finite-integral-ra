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

def os4 : Sym := { h := [0, 1, 2, 3, 5, 4, 6], hi := [0, 1, 2, 3, 5, 4, 6], vp := [0, 1, 3, 2, 4, 5, 6, 26, 8, 10, 9, 11, 12, 28, 15, 14, 16, 30, 32, 34, 20, 21, 22, 24, 23, 25, 7, 27, 13, 29, 17, 31, 18, 35, 19, 33, 36, 38, 37, 39, 41, 40, 42, 43, 45, 44, 47, 46, 48, 49, 51, 50, 52, 54, 53, 55], vq := [0, 1, 3, 2, 4, 5, 6, 26, 8, 10, 9, 11, 12, 28, 15, 14, 16, 30, 32, 34, 20, 21, 22, 24, 23, 25, 7, 27, 13, 29, 17, 31, 18, 35, 19, 33, 36, 38, 37, 39, 41, 40, 42, 43, 45, 44, 47, 46, 48, 49, 51, 50, 52, 54, 53, 55] }
def op4 : List ℕ × List ℕ := ([0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 11, 10, 12, 13, 15, 14, 16, 18, 17, 19], [0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 11, 10, 12, 13, 15, 14, 16, 18, 17, 19])
theorem orient4 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op4.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os4) (e := op4) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os6 : Sym := { h := [0, 1, 2, 3, 5, 6, 4], hi := [0, 1, 2, 3, 6, 4, 5], vp := [0, 1, 3, 4, 2, 5, 6, 26, 8, 10, 11, 9, 12, 28, 15, 16, 14, 30, 34, 32, 20, 21, 22, 24, 25, 23, 27, 7, 29, 13, 31, 17, 35, 18, 33, 19, 36, 38, 39, 37, 41, 42, 40, 45, 43, 44, 47, 48, 46, 51, 49, 50, 54, 52, 53, 55], vq := [0, 1, 4, 2, 3, 5, 6, 27, 8, 11, 9, 10, 12, 29, 16, 14, 15, 31, 33, 35, 20, 21, 22, 25, 23, 24, 7, 26, 13, 28, 17, 30, 19, 34, 18, 32, 36, 39, 37, 38, 42, 40, 41, 44, 45, 43, 48, 46, 47, 50, 51, 49, 53, 54, 52, 55] }
def op6 : List ℕ × List ℕ := ([0, 2, 3, 1, 5, 6, 4, 9, 7, 8, 11, 12, 10, 15, 13, 14, 18, 16, 17, 19], [0, 3, 1, 2, 6, 4, 5, 8, 9, 7, 12, 10, 11, 14, 15, 13, 17, 18, 16, 19])
theorem orient6 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op6.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os6) (e := op6) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os72 : Sym := { h := [0, 1, 2, 5, 3, 4, 6], hi := [0, 1, 2, 4, 5, 3, 6], vp := [0, 3, 1, 2, 4, 5, 26, 6, 10, 8, 9, 11, 28, 12, 30, 32, 34, 15, 14, 16, 20, 21, 24, 22, 23, 25, 7, 27, 13, 29, 18, 35, 17, 31, 19, 33, 38, 36, 37, 39, 41, 43, 45, 40, 42, 44, 47, 49, 51, 46, 48, 50, 52, 54, 55, 53], vq := [0, 2, 3, 1, 4, 5, 7, 26, 9, 10, 8, 11, 13, 28, 18, 17, 19, 32, 30, 34, 20, 21, 23, 24, 22, 25, 6, 27, 12, 29, 14, 33, 15, 35, 16, 31, 37, 38, 36, 39, 43, 40, 44, 41, 45, 42, 49, 46, 50, 47, 51, 48, 52, 55, 53, 54] }
def op72 : List ℕ × List ℕ := ([2, 0, 1, 3, 5, 7, 9, 4, 6, 8, 11, 13, 15, 10, 12, 14, 16, 18, 19, 17], [1, 2, 0, 3, 7, 4, 8, 5, 9, 6, 13, 10, 14, 11, 15, 12, 16, 19, 17, 18])
theorem orient72 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op72.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os72) (e := op72) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os74 : Sym := { h := [0, 1, 2, 5, 3, 6, 4], hi := [0, 1, 2, 4, 6, 3, 5], vp := [0, 3, 1, 4, 2, 5, 26, 6, 10, 8, 11, 9, 28, 12, 30, 34, 32, 15, 16, 14, 20, 21, 24, 22, 25, 23, 27, 7, 29, 13, 35, 18, 31, 17, 33, 19, 38, 36, 39, 37, 41, 45, 43, 42, 40, 44, 47, 51, 49, 48, 46, 50, 54, 52, 55, 53], vq := [0, 2, 4, 1, 3, 5, 7, 27, 9, 11, 8, 10, 13, 29, 19, 17, 18, 33, 31, 35, 20, 21, 23, 25, 22, 24, 6, 26, 12, 28, 14, 32, 16, 34, 15, 30, 37, 39, 36, 38, 44, 40, 43, 42, 45, 41, 50, 46, 49, 48, 51, 47, 53, 55, 52, 54] }
def op74 : List ℕ × List ℕ := ([2, 0, 3, 1, 5, 9, 7, 6, 4, 8, 11, 15, 13, 12, 10, 14, 18, 16, 19, 17], [1, 3, 0, 2, 8, 4, 7, 6, 9, 5, 14, 10, 13, 12, 15, 11, 17, 19, 16, 18])
theorem orient74 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op74.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os74) (e := op74) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os80 : Sym := { h := [0, 1, 2, 5, 6, 3, 4], hi := [0, 1, 2, 5, 6, 3, 4], vp := [0, 3, 4, 1, 2, 5, 26, 27, 10, 11, 8, 9, 28, 29, 34, 30, 32, 35, 31, 33, 20, 21, 24, 25, 22, 23, 6, 7, 12, 13, 15, 18, 16, 19, 14, 17, 38, 39, 36, 37, 45, 41, 43, 42, 44, 40, 51, 47, 49, 48, 50, 46, 54, 55, 52, 53], vq := [0, 3, 4, 1, 2, 5, 26, 27, 10, 11, 8, 9, 28, 29, 34, 30, 32, 35, 31, 33, 20, 21, 24, 25, 22, 23, 6, 7, 12, 13, 15, 18, 16, 19, 14, 17, 38, 39, 36, 37, 45, 41, 43, 42, 44, 40, 51, 47, 49, 48, 50, 46, 54, 55, 52, 53] }
def op80 : List ℕ × List ℕ := ([2, 3, 0, 1, 9, 5, 7, 6, 8, 4, 15, 11, 13, 12, 14, 10, 18, 19, 16, 17], [2, 3, 0, 1, 9, 5, 7, 6, 8, 4, 15, 11, 13, 12, 14, 10, 18, 19, 16, 17])
theorem orient80 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op80.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os80) (e := op80) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os84 : Sym := { h := [0, 1, 5, 2, 3, 4, 6], hi := [0, 1, 3, 4, 5, 2, 6], vp := [3, 0, 1, 2, 4, 26, 5, 6, 28, 30, 32, 34, 10, 15, 8, 9, 11, 12, 14, 16, 20, 24, 21, 22, 23, 25, 7, 27, 18, 35, 13, 29, 17, 31, 19, 33, 38, 41, 43, 45, 36, 37, 39, 40, 42, 44, 47, 49, 51, 52, 54, 55, 46, 48, 50, 53], vq := [1, 2, 3, 0, 4, 6, 7, 26, 14, 15, 12, 16, 17, 30, 18, 13, 19, 32, 28, 34, 20, 22, 23, 24, 21, 25, 5, 27, 8, 31, 9, 33, 10, 35, 11, 29, 40, 41, 36, 42, 43, 37, 44, 38, 45, 39, 52, 46, 53, 47, 54, 48, 49, 55, 50, 51] }
def op84 : List ℕ × List ℕ := ([2, 5, 7, 9, 0, 1, 3, 4, 6, 8, 11, 13, 15, 16, 18, 19, 10, 12, 14, 17], [4, 5, 0, 6, 7, 1, 8, 2, 9, 3, 16, 10, 17, 11, 18, 12, 13, 19, 14, 15])
theorem orient84 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op84.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os84) (e := op84) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os85 : Sym := { h := [0, 5, 1, 2, 3, 4, 6], hi := [0, 2, 3, 4, 5, 1, 6], vp := [26, 28, 30, 32, 34, 3, 10, 15, 0, 1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 16, 24, 20, 21, 22, 23, 25, 18, 35, 7, 27, 13, 29, 17, 31, 19, 33, 38, 41, 43, 45, 47, 49, 51, 52, 54, 55, 36, 37, 39, 40, 42, 44, 46, 48, 50, 53], vq := [8, 9, 10, 5, 11, 12, 13, 28, 14, 15, 6, 16, 17, 30, 18, 7, 19, 32, 26, 34, 21, 22, 23, 24, 20, 25, 0, 29, 1, 31, 2, 33, 3, 35, 4, 27, 46, 47, 36, 48, 49, 37, 50, 38, 51, 39, 52, 40, 53, 41, 54, 42, 43, 55, 44, 45] }
def op85 : List ℕ × List ℕ := ([2, 5, 7, 9, 11, 13, 15, 16, 18, 19, 0, 1, 3, 4, 6, 8, 10, 12, 14, 17], [10, 11, 0, 12, 13, 1, 14, 2, 15, 3, 16, 4, 17, 5, 18, 6, 7, 19, 8, 9])
theorem orient85 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op85.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os85) (e := op85) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os86 : Sym := { h := [0, 1, 5, 2, 3, 6, 4], hi := [0, 1, 3, 4, 6, 2, 5], vp := [3, 0, 1, 4, 2, 26, 5, 6, 28, 30, 34, 32, 10, 15, 8, 11, 9, 12, 16, 14, 20, 24, 21, 22, 25, 23, 27, 7, 35, 18, 29, 13, 31, 17, 33, 19, 38, 41, 45, 43, 36, 39, 37, 42, 40, 44, 47, 51, 49, 54, 52, 55, 48, 46, 50, 53], vq := [1, 2, 4, 0, 3, 6, 7, 27, 14, 16, 12, 15, 17, 31, 19, 13, 18, 33, 29, 35, 20, 22, 23, 25, 21, 24, 5, 26, 8, 30, 9, 32, 11, 34, 10, 28, 40, 42, 36, 41, 44, 37, 43, 39, 45, 38, 53, 46, 52, 48, 54, 47, 50, 55, 49, 51] }
def op86 : List ℕ × List ℕ := ([2, 5, 9, 7, 0, 3, 1, 6, 4, 8, 11, 15, 13, 18, 16, 19, 12, 10, 14, 17], [4, 6, 0, 5, 8, 1, 7, 3, 9, 2, 17, 10, 16, 12, 18, 11, 14, 19, 13, 15])
theorem orient86 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op86.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os86) (e := op86) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os87 : Sym := { h := [0, 5, 1, 2, 3, 6, 4], hi := [0, 2, 3, 4, 6, 1, 5], vp := [26, 28, 30, 34, 32, 3, 10, 15, 0, 1, 4, 2, 5, 6, 8, 11, 9, 12, 16, 14, 24, 20, 21, 22, 25, 23, 35, 18, 27, 7, 29, 13, 31, 17, 33, 19, 38, 41, 45, 43, 47, 51, 49, 54, 52, 55, 36, 39, 37, 42, 40, 44, 48, 46, 50, 53], vq := [8, 9, 11, 5, 10, 12, 13, 29, 14, 16, 6, 15, 17, 31, 19, 7, 18, 33, 27, 35, 21, 22, 23, 25, 20, 24, 0, 28, 1, 30, 2, 32, 4, 34, 3, 26, 46, 48, 36, 47, 50, 37, 49, 39, 51, 38, 53, 40, 52, 42, 54, 41, 44, 55, 43, 45] }
def op87 : List ℕ × List ℕ := ([2, 5, 9, 7, 11, 15, 13, 18, 16, 19, 0, 3, 1, 6, 4, 8, 12, 10, 14, 17], [10, 12, 0, 11, 14, 1, 13, 3, 15, 2, 17, 4, 16, 6, 18, 5, 8, 19, 7, 9])
theorem orient87 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op87.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os87) (e := op87) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os92 : Sym := { h := [0, 1, 5, 2, 6, 3, 4], hi := [0, 1, 3, 5, 6, 2, 4], vp := [3, 0, 4, 1, 2, 26, 5, 27, 28, 34, 30, 32, 10, 35, 11, 8, 9, 29, 31, 33, 20, 24, 21, 25, 22, 23, 6, 7, 15, 18, 12, 13, 16, 19, 14, 17, 38, 45, 41, 43, 39, 36, 37, 42, 44, 40, 51, 47, 49, 54, 55, 52, 48, 50, 46, 53], vq := [1, 3, 4, 0, 2, 6, 26, 27, 15, 16, 12, 14, 30, 31, 34, 28, 32, 35, 29, 33, 20, 22, 24, 25, 21, 23, 5, 7, 8, 17, 10, 18, 11, 19, 9, 13, 41, 42, 36, 40, 45, 38, 43, 39, 44, 37, 54, 47, 52, 48, 53, 46, 51, 55, 49, 50] }
def op92 : List ℕ × List ℕ := ([2, 9, 5, 7, 3, 0, 1, 6, 8, 4, 15, 11, 13, 18, 19, 16, 12, 14, 10, 17], [5, 6, 0, 4, 9, 2, 7, 3, 8, 1, 18, 11, 16, 12, 17, 10, 15, 19, 13, 14])
theorem orient92 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op92.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os92) (e := op92) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os93 : Sym := { h := [0, 5, 1, 2, 6, 3, 4], hi := [0, 2, 3, 5, 6, 1, 4], vp := [26, 28, 34, 30, 32, 3, 10, 35, 0, 4, 1, 2, 5, 27, 11, 8, 9, 29, 31, 33, 24, 20, 21, 25, 22, 23, 15, 18, 6, 7, 12, 13, 16, 19, 14, 17, 38, 45, 41, 43, 51, 47, 49, 54, 55, 52, 39, 36, 37, 42, 44, 40, 48, 50, 46, 53], vq := [8, 10, 11, 5, 9, 12, 28, 29, 15, 16, 6, 14, 30, 31, 34, 26, 32, 35, 27, 33, 21, 22, 24, 25, 20, 23, 0, 13, 1, 17, 3, 18, 4, 19, 2, 7, 47, 48, 36, 46, 51, 38, 49, 39, 50, 37, 54, 41, 52, 42, 53, 40, 45, 55, 43, 44] }
def op93 : List ℕ × List ℕ := ([2, 9, 5, 7, 15, 11, 13, 18, 19, 16, 3, 0, 1, 6, 8, 4, 12, 14, 10, 17], [11, 12, 0, 10, 15, 2, 13, 3, 14, 1, 18, 5, 16, 6, 17, 4, 9, 19, 7, 8])
theorem orient93 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op93.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os93) (e := op93) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os324 : Sym := { h := [0, 1, 5, 6, 2, 3, 4], hi := [0, 1, 4, 5, 6, 2, 3], vp := [3, 4, 0, 1, 2, 26, 27, 5, 34, 28, 30, 32, 35, 10, 29, 31, 33, 11, 8, 9, 20, 24, 25, 21, 22, 23, 6, 7, 15, 18, 16, 19, 12, 13, 14, 17, 45, 38, 41, 43, 39, 42, 44, 36, 37, 40, 51, 54, 55, 47, 49, 52, 48, 50, 53, 46], vq := [2, 3, 4, 0, 1, 7, 26, 27, 18, 19, 13, 17, 32, 33, 34, 28, 30, 35, 29, 31, 20, 23, 24, 25, 21, 22, 5, 6, 9, 14, 10, 15, 11, 16, 8, 12, 43, 44, 37, 40, 45, 38, 41, 39, 42, 36, 55, 49, 52, 50, 53, 46, 51, 54, 47, 48] }
def op324 : List ℕ × List ℕ := ([9, 2, 5, 7, 3, 6, 8, 0, 1, 4, 15, 18, 19, 11, 13, 16, 12, 14, 17, 10], [7, 8, 1, 4, 9, 2, 5, 3, 6, 0, 19, 13, 16, 14, 17, 10, 15, 18, 11, 12])
theorem orient324 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op324.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os324) (e := op324) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os325 : Sym := { h := [0, 5, 1, 6, 2, 3, 4], hi := [0, 2, 4, 5, 6, 1, 3], vp := [26, 34, 28, 30, 32, 3, 35, 10, 4, 0, 1, 2, 27, 5, 29, 31, 33, 11, 8, 9, 24, 20, 25, 21, 22, 23, 15, 18, 6, 7, 16, 19, 12, 13, 14, 17, 45, 38, 41, 43, 51, 54, 55, 47, 49, 52, 39, 42, 44, 36, 37, 40, 48, 50, 53, 46], vq := [9, 10, 11, 5, 8, 13, 28, 29, 18, 19, 7, 17, 32, 33, 34, 26, 30, 35, 27, 31, 21, 23, 24, 25, 20, 22, 0, 12, 2, 14, 3, 15, 4, 16, 1, 6, 49, 50, 37, 46, 51, 38, 47, 39, 48, 36, 55, 43, 52, 44, 53, 40, 45, 54, 41, 42] }
def op325 : List ℕ × List ℕ := ([9, 2, 5, 7, 15, 18, 19, 11, 13, 16, 3, 6, 8, 0, 1, 4, 12, 14, 17, 10], [13, 14, 1, 10, 15, 2, 11, 3, 12, 0, 19, 7, 16, 8, 17, 4, 9, 18, 5, 6])
theorem orient325 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op325.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os325) (e := op325) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

def os348 : Sym := { h := [0, 5, 6, 1, 2, 3, 4], hi := [0, 3, 4, 5, 6, 1, 2], vp := [34, 26, 28, 30, 32, 35, 3, 10, 27, 29, 31, 33, 4, 11, 0, 1, 2, 5, 8, 9, 24, 25, 20, 21, 22, 23, 15, 18, 16, 19, 6, 7, 12, 13, 14, 17, 45, 51, 54, 55, 38, 41, 43, 47, 49, 52, 39, 42, 44, 48, 50, 53, 36, 37, 40, 46], vq := [14, 15, 16, 6, 12, 17, 30, 31, 18, 19, 7, 13, 32, 33, 34, 26, 28, 35, 27, 29, 22, 23, 24, 25, 20, 21, 1, 8, 2, 9, 3, 10, 4, 11, 0, 5, 52, 53, 40, 46, 54, 41, 47, 42, 48, 36, 55, 43, 49, 44, 50, 37, 45, 51, 38, 39] }
def op348 : List ℕ × List ℕ := ([9, 15, 18, 19, 2, 5, 7, 11, 13, 16, 3, 6, 8, 12, 14, 17, 0, 1, 4, 10], [16, 17, 4, 10, 18, 5, 11, 6, 12, 0, 19, 7, 13, 8, 14, 1, 9, 15, 2, 3])
theorem orient348 {h v n : ℕ} (hh : h < 2 ^ 20) (hi : actBits 20 op348.1 h = v) (hv : P.leaf 36 v = n) : P.leaf 36 h = n := by
  subst v
  exact (leaf_actBits (S := os348) (e := op348) check rows (by decide) (by decide +kernel) (by decide +kernel) hh).symm.trans hv

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

def sym12 : Sym := { h := [0, 3, 2, 1, 4, 6, 5], hi := [0, 3, 2, 1, 4, 6, 5], vp := [12, 6, 14, 16, 15, 8, 1, 17, 5, 9, 11, 10, 0, 13, 2, 4, 3, 7, 19, 18, 22, 21, 20, 23, 25, 24, 31, 30, 29, 28, 27, 26, 33, 32, 35, 34, 36, 46, 48, 47, 40, 42, 41, 53, 52, 54, 37, 39, 38, 50, 49, 51, 44, 43, 45, 55], vq := [12, 6, 14, 16, 15, 8, 1, 17, 5, 9, 11, 10, 0, 13, 2, 4, 3, 7, 19, 18, 22, 21, 20, 23, 25, 24, 31, 30, 29, 28, 27, 26, 33, 32, 35, 34, 36, 46, 48, 47, 40, 42, 41, 53, 52, 54, 37, 39, 38, 50, 49, 51, 44, 43, 45, 55] }
def perm12 : List ℕ × List ℕ := ([5, 4, 3, 2, 1, 0, 7, 6, 9, 8, 10, 20, 22, 21, 14, 16, 15, 27, 26, 28, 11, 13, 12, 24, 23, 25, 18, 17, 19, 29], [5, 4, 3, 2, 1, 0, 7, 6, 9, 8, 10, 20, 22, 21, 14, 16, 15, 27, 26, 28, 11, 13, 12, 24, 23, 25, 18, 17, 19, 29])
def keep12 : ℕ := 0x8088a8aaeaeefeff0000000000000000ffffffffffffffff8088a8aaeaeefeff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8088a8aaeaeefeff0000000000000000ffffffffffffffff8088a8aaeaeefeff
def twice12 : ℕ := 0x8088a8aaeaeefe0000000000000000ffffffffffffffff008088a8aaeaeefe0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff008088a8aaeaeefe0000000000000000ffffffffffffffff008088a8aaeaeefe
theorem bal12 : BalancedRows 10 keep12 twice12 (actBits 30 perm12.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow12 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm12.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm12.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym12) (e := perm12) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal12 j hj).1

def sym13 : Sym := { h := [0, 3, 4, 1, 2, 5, 6], hi := [0, 3, 4, 1, 2, 5, 6], vp := [14, 6, 12, 15, 16, 17, 1, 8, 7, 13, 18, 19, 2, 9, 0, 3, 4, 5, 10, 11, 22, 23, 20, 21, 24, 25, 30, 31, 32, 33, 26, 27, 28, 29, 34, 35, 40, 46, 52, 53, 36, 41, 42, 47, 48, 54, 37, 43, 44, 49, 50, 55, 38, 39, 45, 51], vq := [14, 6, 12, 15, 16, 17, 1, 8, 7, 13, 18, 19, 2, 9, 0, 3, 4, 5, 10, 11, 22, 23, 20, 21, 24, 25, 30, 31, 32, 33, 26, 27, 28, 29, 34, 35, 40, 46, 52, 53, 36, 41, 42, 47, 48, 54, 37, 43, 44, 49, 50, 55, 38, 39, 45, 51] }
def perm13 : List ℕ × List ℕ := ([4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 14, 20, 26, 27, 10, 15, 16, 21, 22, 28, 11, 17, 18, 23, 24, 29, 12, 13, 19, 25], [4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 14, 20, 26, 27, 10, 15, 16, 21, 22, 28, 11, 17, 18, 23, 24, 29, 12, 13, 19, 25])
def keep13 : ℕ := 0x8000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffeffff8000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffeffff8000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffeffff8000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffeffff
def twice13 : ℕ := 0x8000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffe00008000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffe00008000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffe00008000c000e000f000f800fc00fe00ff00ff80ffc0ffe0fff0fff8fffcfffe
theorem bal13 : BalancedRows 10 keep13 twice13 (actBits 30 perm13.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow13 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm13.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm13.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym13) (e := perm13) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal13 j hj).1

def sym14 : Sym := { h := [0, 3, 4, 1, 2, 6, 5], hi := [0, 3, 4, 1, 2, 6, 5], vp := [14, 6, 12, 16, 15, 17, 1, 8, 7, 13, 19, 18, 2, 9, 0, 4, 3, 5, 11, 10, 22, 23, 20, 21, 25, 24, 31, 30, 33, 32, 27, 26, 29, 28, 35, 34, 40, 46, 53, 52, 36, 42, 41, 48, 47, 54, 37, 44, 43, 50, 49, 55, 39, 38, 45, 51], vq := [14, 6, 12, 16, 15, 17, 1, 8, 7, 13, 19, 18, 2, 9, 0, 4, 3, 5, 11, 10, 22, 23, 20, 21, 25, 24, 31, 30, 33, 32, 27, 26, 29, 28, 35, 34, 40, 46, 53, 52, 36, 42, 41, 48, 47, 54, 37, 44, 43, 50, 49, 55, 39, 38, 45, 51] }
def perm14 : List ℕ × List ℕ := ([5, 4, 7, 6, 1, 0, 3, 2, 9, 8, 14, 20, 27, 26, 10, 16, 15, 22, 21, 28, 11, 18, 17, 24, 23, 29, 13, 12, 19, 25], [5, 4, 7, 6, 1, 0, 3, 2, 9, 8, 14, 20, 27, 26, 10, 16, 15, 22, 21, 28, 11, 18, 17, 24, 23, 29, 13, 12, 19, 25])
def keep14 : ℕ := 0x8000a000e000f000f080f0a0f0e0f0f0f8f0faf0fef0fff0fff8fffafffeffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000a000e000f000f080f0a0f0e0f0f0f8f0faf0fef0fff0fff8fffafffeffff
def twice14 : ℕ := 0x8000a000e000f000f080f0a0f0e0f0f0f8f0faf0fef0fff0fff8fffafffe0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00008000a000e000f000f080f0a0f0e0f0f0f8f0faf0fef0fff0fff8fffafffe
theorem bal14 : BalancedRows 10 keep14 twice14 (actBits 30 perm14.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow14 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm14.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm14.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym14) (e := perm14) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal14 j hj).1

def sym16 : Sym := { h := [0, 4, 2, 3, 1, 6, 5], hi := [0, 4, 2, 3, 1, 6, 5], vp := [13, 17, 7, 19, 18, 9, 14, 2, 8, 5, 11, 10, 12, 0, 6, 16, 15, 1, 4, 3, 23, 21, 22, 20, 25, 24, 33, 32, 29, 28, 31, 30, 27, 26, 35, 34, 46, 37, 50, 49, 40, 53, 52, 44, 43, 55, 36, 48, 47, 39, 38, 51, 42, 41, 54, 45], vq := [13, 17, 7, 19, 18, 9, 14, 2, 8, 5, 11, 10, 12, 0, 6, 16, 15, 1, 4, 3, 23, 21, 22, 20, 25, 24, 33, 32, 29, 28, 31, 30, 27, 26, 35, 34, 46, 37, 50, 49, 40, 53, 52, 44, 43, 55, 36, 48, 47, 39, 38, 51, 42, 41, 54, 45] }
def perm16 : List ℕ × List ℕ := ([7, 6, 3, 2, 5, 4, 1, 0, 9, 8, 20, 11, 24, 23, 14, 27, 26, 18, 17, 29, 10, 22, 21, 13, 12, 25, 16, 15, 28, 19], [7, 6, 3, 2, 5, 4, 1, 0, 9, 8, 20, 11, 24, 23, 14, 27, 26, 18, 17, 29, 10, 22, 21, 13, 12, 25, 16, 15, 28, 19])
def keep16 : ℕ := 0x8088000088888088a8aa8888aaaaa8aaeaeeaaaaeeeeeaeefeffeeeefffffeff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8088000088888088a8aa8888aaaaa8aaeaeeaaaaeeeeeaeefeffeeeefffffeff
def twice16 : ℕ := 0x8000008888008088a88888aaaa88a8aaeaaaaaeeeeaaeaeefeeeeeffffeefe0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff008000008888008088a88888aaaa88a8aaeaaaaaeeeeaaeaeefeeeeeffffeefe
theorem bal16 : BalancedRows 10 keep16 twice16 (actBits 30 perm16.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow16 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm16.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm16.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym16) (e := perm16) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal16 j hj).1

def sym17 : Sym := { h := [0, 4, 3, 2, 1, 5, 6], hi := [0, 4, 3, 2, 1, 5, 6], vp := [17, 13, 7, 18, 19, 14, 9, 2, 12, 6, 15, 16, 8, 1, 5, 10, 11, 0, 3, 4, 23, 22, 21, 20, 24, 25, 32, 33, 30, 31, 28, 29, 26, 27, 34, 35, 46, 40, 52, 53, 37, 49, 50, 43, 44, 55, 36, 47, 48, 41, 42, 54, 38, 39, 51, 45], vq := [17, 13, 7, 18, 19, 14, 9, 2, 12, 6, 15, 16, 8, 1, 5, 10, 11, 0, 3, 4, 23, 22, 21, 20, 24, 25, 32, 33, 30, 31, 28, 29, 26, 27, 34, 35, 46, 40, 52, 53, 37, 49, 50, 43, 44, 55, 36, 47, 48, 41, 42, 54, 38, 39, 51, 45] }
def perm17 : List ℕ × List ℕ := ([6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 20, 14, 26, 27, 11, 23, 24, 17, 18, 29, 10, 21, 22, 15, 16, 28, 12, 13, 25, 19], [6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 20, 14, 26, 27, 11, 23, 24, 17, 18, 29, 10, 21, 22, 15, 16, 28, 12, 13, 25, 19])
def keep17 : ℕ := 0x8000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffeffff8000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffeffff8000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffeffff8000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffeffff
def twice17 : ℕ := 0x8000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffe00008000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffe00008000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffe00008000880088808888c888cc88ccc8cccceccceecceeeceeeefeeeffeefffe
theorem bal17 : BalancedRows 10 keep17 twice17 (actBits 30 perm17.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow17 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm17.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm17.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym17) (e := perm17) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal17 j hj).1

def sym18 : Sym := { h := [0, 4, 3, 2, 1, 6, 5], hi := [0, 4, 3, 2, 1, 6, 5], vp := [17, 13, 7, 19, 18, 14, 9, 2, 12, 6, 16, 15, 8, 1, 5, 11, 10, 0, 4, 3, 23, 22, 21, 20, 25, 24, 33, 32, 31, 30, 29, 28, 27, 26, 35, 34, 46, 40, 53, 52, 37, 50, 49, 44, 43, 55, 36, 48, 47, 42, 41, 54, 39, 38, 51, 45], vq := [17, 13, 7, 19, 18, 14, 9, 2, 12, 6, 16, 15, 8, 1, 5, 11, 10, 0, 4, 3, 23, 22, 21, 20, 25, 24, 33, 32, 31, 30, 29, 28, 27, 26, 35, 34, 46, 40, 53, 52, 37, 50, 49, 44, 43, 55, 36, 48, 47, 42, 41, 54, 39, 38, 51, 45] }
def perm18 : List ℕ × List ℕ := ([7, 6, 5, 4, 3, 2, 1, 0, 9, 8, 20, 14, 27, 26, 11, 24, 23, 18, 17, 29, 10, 22, 21, 16, 15, 28, 13, 12, 25, 19], [7, 6, 5, 4, 3, 2, 1, 0, 9, 8, 20, 14, 27, 26, 11, 24, 23, 18, 17, 29, 10, 22, 21, 16, 15, 28, 13, 12, 25, 19])
def keep18 : ℕ := 0x8000808088808888a888a8a8aaa8aaaaeaaaeaeaeeeaeeeefeeefefefffeffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000808088808888a888a8a8aaa8aaaaeaaaeaeaeeeaeeeefeeefefefffeffff
def twice18 : ℕ := 0x8000808088808888a888a8a8aaa8aaaaeaaaeaeaeeeaeeeefeeefefefffe0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00008000808088808888a888a8a8aaa8aaaaeaaaeaeaeeeaeeeefeeefefefffe
theorem bal18 : BalancedRows 10 keep18 twice18 (actBits 30 perm18.1) :=
  balancedRows_of_check (by decide +kernel)
theorem invRow18 {H : ℕ} (hh : H < 2 ^ 20) (hs : actBits 30 perm18.1 (1024 * H) = 1024 * H) : ∀ j < 1024, P.leaf 26 (1024 * H + actBits 30 perm18.1 j) = P.leaf 26 (1024 * H + j) :=
  fun j hj => row_invariant (d := 10) (S := sym18) (e := perm18) check rows (by decide) hh (by decide +kernel) (by decide +kernel) hs hj (bal18 j hj).1

end RACert.S6N0.C0
