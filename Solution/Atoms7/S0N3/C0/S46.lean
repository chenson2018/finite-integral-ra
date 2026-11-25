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

namespace S46

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(123775, 48), (123776, 48), (123777, 48), (123778, 48), (123779, 48), (123780, 48), (123781, 48), (123782, 48), (123783, 48), (123784, 48), (123785, 48), (123786, 48), (123787, 48), (123788, 48), (123789, 48), (123790, 48), (123791, 48), (123792, 48), (123793, 48), (123794, 48), (123795, 48), (123796, 48), (123797, 48), (123798, 48), (123799, 48), (123800, 48), (123801, 48), (123802, 48), (123803, 48), (123804, 48), (123805, 48), (123806, 48), (123807, 48), (123808, 48), (123809, 48), (123810, 48), (123811, 48), (123812, 48), (123813, 48), (123814, 48), (123815, 48), (123816, 48), (123817, 48), (123818, 48), (123819, 48), (123820, 48), (123821, 48), (123822, 48), (123823, 48), (123824, 48), (123825, 48), (123826, 48), (123827, 48), (123828, 48), (123829, 48), (123830, 48), (123831, 48), (123832, 48), (123833, 48), (123834, 48), (123835, 48), (123836, 48), (123837, 48), (123838, 48), (123839, 48), (123840, 48), (123841, 48), (123842, 48), (123843, 48), (123844, 48), (123845, 48), (123846, 48), (123847, 48), (123848, 48), (123849, 48), (123850, 48), (123851, 48), (123852, 48), (123853, 48), (123854, 48), (123855, 48), (123856, 48), (123857, 48), (123858, 48), (123859, 48), (123860, 48), (123861, 48), (123862, 48), (123863, 48), (123864, 48), (123865, 48), (123866, 48), (123867, 48), (123868, 48), (123869, 48), (123870, 48), (123871, 48), (123872, 48), (123873, 48), (123874, 48), (123875, 48), (123876, 48), (123877, 48), (123878, 48), (123879, 48), (123880, 48), (123881, 48), (123882, 48), (123883, 48), (123884, 48), (123885, 48), (123886, 48), (123887, 48), (123888, 48), (123889, 48), (123890, 48), (123891, 48), (123892, 48), (123893, 48), (123894, 48), (123895, 48), (123896, 48), (123897, 48), (123898, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 424, 432, 550, 602, 418, 418, 550, 602, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 602, 550, 602, 550, 602, 550, 439, 550, 0, 550, 628, 550, 0, 503, 432, 602, 602, 418, 418, 602, 602, 418, 418, 0, 0, 418, 418, 0, 0, 602, 439, 602, 602, 602, 602, 602, 602, 628, 439, 0, 0, 628, 628, 0, 0, 424, 432, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 503, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(123775, 104), (123787, 7), (123791, 36), (123803, 68), (123807, 240), (123818, 12), (123819, 22), (123822, 56), (123823, 108), (123834, 42), (123835, 72), (123838, 132), (123839, 240), (123843, 6), (123847, 118), (123851, 19), (123855, 228), (123859, 86), (123861, 270), (123863, 958), (123867, 208), (123869, 459), (123871, 1739), (123874, 16), (123875, 22), (123878, 245), (123879, 390), (123882, 44), (123883, 66), (123886, 447), (123887, 771), (123888, 0), (123890, 34), (123891, 86), (123892, 116), (123893, 376), (123894, 732), (123895, 1456), (123896, 0), (123898, 138)]

theorem l123775 : P.leaf 18 123775 = 104 := by decide +kernel

theorem l123787 : P.leaf 18 123787 = 7 := by decide +kernel

theorem l123791 : P.leaf 18 123791 = 36 := by decide +kernel

theorem l123803 : P.leaf 18 123803 = 68 := by decide +kernel

theorem l123807 : P.leaf 18 123807 = 240 := by decide +kernel

theorem l123818 : P.leaf 18 123818 = 12 := by decide +kernel

theorem l123819 : P.leaf 18 123819 = 22 := by decide +kernel

theorem l123822 : P.leaf 18 123822 = 56 := by decide +kernel

theorem l123823 : P.leaf 18 123823 = 108 := by decide +kernel

theorem l123834 : P.leaf 18 123834 = 42 := by decide +kernel

theorem l123835 : P.leaf 18 123835 = 72 := by decide +kernel

theorem l123838 : P.leaf 18 123838 = 132 := by decide +kernel

theorem l123839 : P.leaf 18 123839 = 240 := by decide +kernel

theorem l123843 : P.leaf 18 123843 = 6 := by decide +kernel

theorem l123847 : P.leaf 18 123847 = 118 := by decide +kernel

theorem l123851 : P.leaf 18 123851 = 19 := by decide +kernel

theorem l123855 : P.leaf 18 123855 = 228 := by decide +kernel

theorem l123859 : P.leaf 18 123859 = 86 := by decide +kernel

theorem l123861 : P.leaf 18 123861 = 270 := by decide +kernel

theorem l123863 : P.leaf 18 123863 = 958 := by decide +kernel

theorem l123867 : P.leaf 18 123867 = 208 := by decide +kernel

theorem l123869 : P.leaf 18 123869 = 459 := by decide +kernel

theorem l123871 : P.leaf 18 123871 = 1739 := by decide +kernel

theorem l123874 : P.leaf 18 123874 = 16 := by decide +kernel

theorem l123875 : P.leaf 18 123875 = 22 := by decide +kernel

theorem l123878 : P.leaf 18 123878 = 245 := by decide +kernel

theorem l123879 : P.leaf 18 123879 = 390 := by decide +kernel

theorem l123882 : P.leaf 18 123882 = 44 := by decide +kernel

theorem l123883 : P.leaf 18 123883 = 66 := by decide +kernel

theorem l123886 : P.leaf 18 123886 = 447 := by decide +kernel

theorem l123887 : P.leaf 18 123887 = 771 := by decide +kernel

theorem l123888 : P.leaf 18 123888 = 0 := by decide +kernel

theorem l123890 : P.leaf 18 123890 = 34 := by decide +kernel

theorem l123891 : P.leaf 18 123891 = 86 := by decide +kernel

theorem l123892 : P.leaf 18 123892 = 116 := by decide +kernel

theorem l123893 : P.leaf 18 123893 = 376 := by decide +kernel

theorem l123894 : P.leaf 18 123894 = 732 := by decide +kernel

theorem l123895 : P.leaf 18 123895 = 1456 := by decide +kernel

theorem l123896 : P.leaf 18 123896 = 0 := by decide +kernel

theorem l123898 : P.leaf 18 123898 = 138 := by decide +kernel

theorem segOK : checkSeg 20 perms 123775 123899 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 488112 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 123775 123899 5952 488112 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l123775 (.cons l123787 (.cons l123791 (.cons l123803 (.cons l123807 (.cons l123818 (.cons l123819 (.cons l123822 (.cons l123823 (.cons l123834 (.cons l123835 (.cons l123838 (.cons l123839 (.cons l123843 (.cons l123847 (.cons l123851 (.cons l123855 (.cons l123859 (.cons l123861 (.cons l123863 (.cons l123867 (.cons l123869 (.cons l123871 (.cons l123874 (.cons l123875 (.cons l123878 (.cons l123879 (.cons l123882 (.cons l123883 (.cons l123886 (.cons l123887 (.cons l123888 (.cons l123890 (.cons l123891 (.cons l123892 (.cons l123893 (.cons l123894 (.cons l123895 (.cons l123896 (.cons l123898 (.nil))))))))))))))))))))))))))))))))))))))))))

end S46

end RACert.S0N3.C0
