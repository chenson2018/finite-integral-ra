/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace S42

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(113634, 48), (113635, 48), (113636, 48), (113637, 48), (113638, 48), (113639, 48), (113640, 48), (113641, 48), (113642, 48), (113643, 48), (113644, 48), (113645, 48), (113646, 48), (113647, 48), (113648, 48), (113649, 48), (113650, 48), (113651, 48), (113652, 48), (113653, 48), (113654, 48), (113655, 48), (113656, 48), (113657, 48), (113658, 48), (113659, 48), (113660, 48), (113661, 48), (113662, 48), (113663, 48), (113856, 24), (113857, 48), (113858, 48), (113859, 48), (113860, 48), (113861, 48), (113862, 48), (113863, 48), (113864, 48), (113865, 48), (113866, 48), (113867, 48), (113868, 48), (113869, 48), (113870, 48), (113871, 48), (113873, 48), (113874, 24), (113875, 48), (113876, 48), (113877, 48), (113878, 48), (113879, 48), (113880, 48), (113881, 48), (113882, 48), (113883, 48), (113884, 48), (113885, 48), (113886, 48), (113887, 48), (113889, 24), (113891, 48), (113892, 48), (113893, 48), (113894, 48), (113895, 48), (113896, 48), (113897, 48), (113898, 48), (113899, 48), (113900, 48), (113901, 48), (113902, 48), (113903, 48), (113907, 24), (113908, 48), (113909, 48), (113910, 48), (113911, 48), (113912, 48), (113913, 48), (113914, 48), (113915, 48), (113916, 48), (113917, 48), (113918, 48), (113919, 48), (114116, 48), (114117, 48), (114118, 48), (114119, 48), (114120, 24), (114121, 48), (114122, 48), (114123, 48), (114124, 48), (114125, 48), (114126, 48), (114127, 48), (114132, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 426, 439, 0, 0, 432, 0, 0, 0, 426, 439, 0, 0, 0, 0, 0, 0, 426, 502, 426, 663, 432, 432, 663, 663, 439, 439, 663, 663, 502, 502, 663, 663, 432, 426, 669, 0, 0, 0, 0, 439, 439, 669, 669, 0, 0, 0, 0, 502, 663, 432, 432, 0, 0, 439, 439, 614, 614, 502, 502, 614, 614, 0, 0, 0, 0, 0, 439, 439, 0, 0, 0, 0, 0, 0, 424, 432, 424, 614, 418, 418, 614, 614, 418, 418, 424, 614, 424]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(113634, 40), (113635, 48), (113638, 198), (113639, 324), (113642, 80), (113643, 144), (113646, 302), (113647, 492), (113650, 88), (113651, 100), (113653, 334), (113654, 376), (113655, 672), (113658, 136), (113659, 280), (113660, 112), (113661, 418), (113662, 476), (113663, 896), (113876, 0), (113877, 72), (113878, 84), (113879, 168), (113884, 0), (113885, 136), (113886, 156), (113887, 312), (113894, 0), (113895, 0), (113907, 64), (113908, 10), (113909, 100), (113910, 140), (113911, 288), (113914, 80), (113915, 160), (113916, 26), (113917, 168), (113918, 200), (113919, 440)]

theorem l113634 : P.leaf 18 113634 = 40 := by decide +kernel

theorem l113635 : P.leaf 18 113635 = 48 := by decide +kernel

theorem l113638 : P.leaf 18 113638 = 198 := by decide +kernel

theorem l113639 : P.leaf 18 113639 = 324 := by decide +kernel

theorem l113642 : P.leaf 18 113642 = 80 := by decide +kernel

theorem l113643 : P.leaf 18 113643 = 144 := by decide +kernel

theorem l113646 : P.leaf 18 113646 = 302 := by decide +kernel

theorem l113647 : P.leaf 18 113647 = 492 := by decide +kernel

theorem l113650 : P.leaf 18 113650 = 88 := by decide +kernel

theorem l113651 : P.leaf 18 113651 = 100 := by decide +kernel

theorem l113653 : P.leaf 18 113653 = 334 := by decide +kernel

theorem l113654 : P.leaf 18 113654 = 376 := by decide +kernel

theorem l113655 : P.leaf 18 113655 = 672 := by decide +kernel

theorem l113658 : P.leaf 18 113658 = 136 := by decide +kernel

theorem l113659 : P.leaf 18 113659 = 280 := by decide +kernel

theorem l113660 : P.leaf 18 113660 = 112 := by decide +kernel

theorem l113661 : P.leaf 18 113661 = 418 := by decide +kernel

theorem l113662 : P.leaf 18 113662 = 476 := by decide +kernel

theorem l113663 : P.leaf 18 113663 = 896 := by decide +kernel

theorem l113876 : P.leaf 18 113876 = 0 := by decide +kernel

theorem l113877 : P.leaf 18 113877 = 72 := by decide +kernel

theorem l113878 : P.leaf 18 113878 = 84 := by decide +kernel

theorem l113879 : P.leaf 18 113879 = 168 := by decide +kernel

theorem l113884 : P.leaf 18 113884 = 0 := by decide +kernel

theorem l113885 : P.leaf 18 113885 = 136 := by decide +kernel

theorem l113886 : P.leaf 18 113886 = 156 := by decide +kernel

theorem l113887 : P.leaf 18 113887 = 312 := by decide +kernel

theorem l113894 : P.leaf 18 113894 = 0 := by decide +kernel

theorem l113895 : P.leaf 18 113895 = 0 := by decide +kernel

theorem l113907 : P.leaf 18 113907 = 64 := by decide +kernel

theorem l113908 : P.leaf 18 113908 = 10 := by decide +kernel

theorem l113909 : P.leaf 18 113909 = 100 := by decide +kernel

theorem l113910 : P.leaf 18 113910 = 140 := by decide +kernel

theorem l113911 : P.leaf 18 113911 = 288 := by decide +kernel

theorem l113914 : P.leaf 18 113914 = 80 := by decide +kernel

theorem l113915 : P.leaf 18 113915 = 160 := by decide +kernel

theorem l113916 : P.leaf 18 113916 = 26 := by decide +kernel

theorem l113917 : P.leaf 18 113917 = 168 := by decide +kernel

theorem l113918 : P.leaf 18 113918 = 200 := by decide +kernel

theorem l113919 : P.leaf 18 113919 = 440 := by decide +kernel

theorem segOK : checkSeg 20 perms 113634 114133 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 388224 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 113634 114133 4728 388224 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l113634 (.cons l113635 (.cons l113638 (.cons l113639 (.cons l113642 (.cons l113643 (.cons l113646 (.cons l113647 (.cons l113650 (.cons l113651 (.cons l113653 (.cons l113654 (.cons l113655 (.cons l113658 (.cons l113659 (.cons l113660 (.cons l113661 (.cons l113662 (.cons l113663 (.cons l113876 (.cons l113877 (.cons l113878 (.cons l113879 (.cons l113884 (.cons l113885 (.cons l113886 (.cons l113887 (.cons l113894 (.cons l113895 (.cons l113907 (.cons l113908 (.cons l113909 (.cons l113910 (.cons l113911 (.cons l113914 (.cons l113915 (.cons l113916 (.cons l113917 (.cons l113918 (.cons l113919 (.nil))))))))))))))))))))))))))))))))))))))))))

end S42

end RACert.S0N3.C0
