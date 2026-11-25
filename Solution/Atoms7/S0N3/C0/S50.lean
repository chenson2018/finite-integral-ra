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

namespace S50

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(124842, 48), (124843, 48), (124844, 48), (124845, 48), (124846, 48), (124847, 48), (124848, 48), (124849, 48), (124850, 48), (124851, 48), (124852, 48), (124853, 48), (124854, 48), (124855, 48), (124856, 48), (124857, 48), (124858, 48), (124859, 48), (124860, 48), (124861, 48), (124862, 48), (124863, 48), (124864, 48), (124865, 48), (124866, 48), (124867, 48), (124868, 48), (124869, 48), (124870, 48), (124871, 48), (124872, 48), (124873, 48), (124874, 48), (124875, 48), (124876, 48), (124877, 48), (124878, 48), (124879, 48), (124880, 48), (124881, 48), (124882, 48), (124883, 48), (124884, 48), (124885, 48), (124886, 48), (124887, 48), (124888, 48), (124889, 48), (124890, 48), (124891, 48), (124892, 48), (124893, 48), (124894, 48), (124895, 48), (124896, 48), (124897, 48), (124898, 48), (124899, 48), (124900, 48), (124901, 48), (124902, 48), (124903, 48), (124904, 48), (124905, 48), (124906, 48), (124907, 48), (124908, 48), (124909, 48), (124910, 48), (124911, 48), (124912, 48), (124913, 48), (124914, 48), (124915, 48), (124916, 48), (124917, 48), (124918, 48), (124919, 48), (124920, 48), (124921, 48), (124922, 48), (124923, 48), (124924, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 418, 418, 0, 0, 602, 439, 602, 602, 602, 602, 602, 602, 0, 439, 0, 0, 0, 0, 0, 0, 424, 432, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 503, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(124842, 32), (124843, 66), (124846, 358), (124847, 696), (124856, 0), (124858, 108), (124859, 216), (124860, 260), (124861, 660), (124862, 1164), (124863, 2460), (124867, 8), (124871, 134), (124875, 28), (124879, 248), (124883, 94), (124885, 360), (124887, 1112), (124891, 252), (124893, 555), (124895, 1922), (124898, 16), (124899, 24), (124902, 282), (124903, 478), (124906, 48), (124907, 88), (124910, 480), (124911, 860), (124912, 0), (124914, 40), (124915, 94), (124916, 120), (124917, 512), (124918, 900), (124919, 1652), (124920, 0), (124922, 160), (124923, 268), (124924, 280)]

theorem l124842 : P.leaf 18 124842 = 32 := by decide +kernel

theorem l124843 : P.leaf 18 124843 = 66 := by decide +kernel

theorem l124846 : P.leaf 18 124846 = 358 := by decide +kernel

theorem l124847 : P.leaf 18 124847 = 696 := by decide +kernel

theorem l124856 : P.leaf 18 124856 = 0 := by decide +kernel

theorem l124858 : P.leaf 18 124858 = 108 := by decide +kernel

theorem l124859 : P.leaf 18 124859 = 216 := by decide +kernel

theorem l124860 : P.leaf 18 124860 = 260 := by decide +kernel

theorem l124861 : P.leaf 18 124861 = 660 := by decide +kernel

theorem l124862 : P.leaf 18 124862 = 1164 := by decide +kernel

theorem l124863 : P.leaf 18 124863 = 2460 := by decide +kernel

theorem l124867 : P.leaf 18 124867 = 8 := by decide +kernel

theorem l124871 : P.leaf 18 124871 = 134 := by decide +kernel

theorem l124875 : P.leaf 18 124875 = 28 := by decide +kernel

theorem l124879 : P.leaf 18 124879 = 248 := by decide +kernel

theorem l124883 : P.leaf 18 124883 = 94 := by decide +kernel

theorem l124885 : P.leaf 18 124885 = 360 := by decide +kernel

theorem l124887 : P.leaf 18 124887 = 1112 := by decide +kernel

theorem l124891 : P.leaf 18 124891 = 252 := by decide +kernel

theorem l124893 : P.leaf 18 124893 = 555 := by decide +kernel

theorem l124895 : P.leaf 18 124895 = 1922 := by decide +kernel

theorem l124898 : P.leaf 18 124898 = 16 := by decide +kernel

theorem l124899 : P.leaf 18 124899 = 24 := by decide +kernel

theorem l124902 : P.leaf 18 124902 = 282 := by decide +kernel

theorem l124903 : P.leaf 18 124903 = 478 := by decide +kernel

theorem l124906 : P.leaf 18 124906 = 48 := by decide +kernel

theorem l124907 : P.leaf 18 124907 = 88 := by decide +kernel

theorem l124910 : P.leaf 18 124910 = 480 := by decide +kernel

theorem l124911 : P.leaf 18 124911 = 860 := by decide +kernel

theorem l124912 : P.leaf 18 124912 = 0 := by decide +kernel

theorem l124914 : P.leaf 18 124914 = 40 := by decide +kernel

theorem l124915 : P.leaf 18 124915 = 94 := by decide +kernel

theorem l124916 : P.leaf 18 124916 = 120 := by decide +kernel

theorem l124917 : P.leaf 18 124917 = 512 := by decide +kernel

theorem l124918 : P.leaf 18 124918 = 900 := by decide +kernel

theorem l124919 : P.leaf 18 124919 = 1652 := by decide +kernel

theorem l124920 : P.leaf 18 124920 = 0 := by decide +kernel

theorem l124922 : P.leaf 18 124922 = 160 := by decide +kernel

theorem l124923 : P.leaf 18 124923 = 268 := by decide +kernel

theorem l124924 : P.leaf 18 124924 = 280 := by decide +kernel

theorem segOK : checkSeg 20 perms 124842 124925 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 817680 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 124842 124925 3984 817680 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l124842 (.cons l124843 (.cons l124846 (.cons l124847 (.cons l124856 (.cons l124858 (.cons l124859 (.cons l124860 (.cons l124861 (.cons l124862 (.cons l124863 (.cons l124867 (.cons l124871 (.cons l124875 (.cons l124879 (.cons l124883 (.cons l124885 (.cons l124887 (.cons l124891 (.cons l124893 (.cons l124895 (.cons l124898 (.cons l124899 (.cons l124902 (.cons l124903 (.cons l124906 (.cons l124907 (.cons l124910 (.cons l124911 (.cons l124912 (.cons l124914 (.cons l124915 (.cons l124916 (.cons l124917 (.cons l124918 (.cons l124919 (.cons l124920 (.cons l124922 (.cons l124923 (.cons l124924 (.nil))))))))))))))))))))))))))))))))))))))))))

end S50

end RACert.S0N3.C0
