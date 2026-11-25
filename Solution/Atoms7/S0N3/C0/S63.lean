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

namespace S63

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(129991, 48), (129992, 48), (129993, 48), (129994, 48), (129995, 48), (129996, 48), (129997, 48), (129998, 48), (129999, 48), (130000, 48), (130001, 48), (130002, 48), (130003, 48), (130004, 48), (130005, 48), (130006, 48), (130007, 48), (130008, 48), (130009, 48), (130010, 48), (130011, 48), (130012, 48), (130013, 48), (130014, 48), (130015, 48), (130016, 48), (130017, 48), (130018, 48), (130019, 48), (130020, 48), (130021, 48), (130022, 48), (130023, 48), (130024, 48), (130025, 48), (130026, 48), (130027, 48), (130028, 48), (130029, 48), (130030, 48), (130031, 48), (130032, 48), (130033, 48), (130034, 48), (130035, 48), (130036, 48), (130037, 48), (130038, 48), (130039, 48), (130040, 48), (130041, 48), (130042, 48), (130043, 48), (130044, 48), (130045, 48), (130046, 48), (130047, 48), (130816, 24), (130817, 48), (130818, 48), (130819, 48), (130821, 48), (130822, 24), (130823, 48), (130825, 24), (130827, 48), (130831, 24), (130832, 48), (130833, 48), (130834, 48), (130835, 48), (130836, 48), (130837, 48), (130838, 48), (130839, 48), (130840, 48), (130841, 48), (130842, 48), (130843, 48), (130844, 48), (130845, 48), (130846, 48), (130847, 48), (130848, 48), (130849, 48), (130850, 48), (130851, 48), (130852, 48), (130853, 48), (130854, 48), (130855, 48), (130856, 48), (130857, 48), (130858, 48), (130859, 48), (130860, 48), (130861, 48), (130862, 48), (130863, 48), (130864, 48), (130865, 48), (130866, 48), (130867, 48), (130868, 48), (130869, 48), (130870, 48), (130871, 48), (130872, 48), (130873, 48), (130874, 48), (130875, 48), (130876, 48), (130877, 48), (130878, 48), (130879, 48), (130896, 48), (130897, 48), (130898, 48), (130899, 48), (130900, 48), (130901, 48), (130902, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 439, 439, 550, 0, 550, 0, 550, 0, 502, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 439, 439, 0, 0, 0, 0, 0, 0, 424, 432, 438, 440, 418, 550, 602, 418, 440, 0, 434, 439, 438, 440, 550, 602, 550, 602, 438, 439, 438, 440, 550, 0, 550, 0, 434, 432, 438, 440, 418, 418, 602, 602, 418, 418, 438, 440, 418, 418, 0, 0, 434, 439, 438, 440, 602, 602, 602, 602, 438, 439, 438, 440, 0, 0, 0, 0, 550, 439, 438, 440, 550, 0, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(129991, 252), (129995, 166), (129999, 508), (130003, 208), (130005, 742), (130007, 1456), (130011, 724), (130013, 1385), (130015, 2958), (130018, 104), (130019, 144), (130022, 494), (130023, 880), (130026, 360), (130027, 540), (130030, 1128), (130031, 1942), (130032, 0), (130034, 120), (130035, 208), (130036, 268), (130037, 922), (130038, 992), (130039, 2172), (130042, 438), (130043, 780), (130044, 488), (130045, 1664), (130046, 1906), (130047, 4520), (130831, 232), (130845, 486), (130847, 852), (130862, 352), (130863, 576), (130876, 160), (130877, 544), (130878, 464), (130879, 1040), (130901, 982)]

theorem l129991 : P.leaf 18 129991 = 252 := by decide +kernel

theorem l129995 : P.leaf 18 129995 = 166 := by decide +kernel

theorem l129999 : P.leaf 18 129999 = 508 := by decide +kernel

theorem l130003 : P.leaf 18 130003 = 208 := by decide +kernel

theorem l130005 : P.leaf 18 130005 = 742 := by decide +kernel

theorem l130007 : P.leaf 18 130007 = 1456 := by decide +kernel

theorem l130011 : P.leaf 18 130011 = 724 := by decide +kernel

theorem l130013 : P.leaf 18 130013 = 1385 := by decide +kernel

theorem l130015 : P.leaf 18 130015 = 2958 := by decide +kernel

theorem l130018 : P.leaf 18 130018 = 104 := by decide +kernel

theorem l130019 : P.leaf 18 130019 = 144 := by decide +kernel

theorem l130022 : P.leaf 18 130022 = 494 := by decide +kernel

theorem l130023 : P.leaf 18 130023 = 880 := by decide +kernel

theorem l130026 : P.leaf 18 130026 = 360 := by decide +kernel

theorem l130027 : P.leaf 18 130027 = 540 := by decide +kernel

theorem l130030 : P.leaf 18 130030 = 1128 := by decide +kernel

theorem l130031 : P.leaf 18 130031 = 1942 := by decide +kernel

theorem l130032 : P.leaf 18 130032 = 0 := by decide +kernel

theorem l130034 : P.leaf 18 130034 = 120 := by decide +kernel

theorem l130035 : P.leaf 18 130035 = 208 := by decide +kernel

theorem l130036 : P.leaf 18 130036 = 268 := by decide +kernel

theorem l130037 : P.leaf 18 130037 = 922 := by decide +kernel

theorem l130038 : P.leaf 18 130038 = 992 := by decide +kernel

theorem l130039 : P.leaf 18 130039 = 2172 := by decide +kernel

theorem l130042 : P.leaf 18 130042 = 438 := by decide +kernel

theorem l130043 : P.leaf 18 130043 = 780 := by decide +kernel

theorem l130044 : P.leaf 18 130044 = 488 := by decide +kernel

theorem l130045 : P.leaf 18 130045 = 1664 := by decide +kernel

theorem l130046 : P.leaf 18 130046 = 1906 := by decide +kernel

theorem l130047 : P.leaf 18 130047 = 4520 := by decide +kernel

theorem l130831 : P.leaf 18 130831 = 232 := by decide +kernel

theorem l130845 : P.leaf 18 130845 = 486 := by decide +kernel

theorem l130847 : P.leaf 18 130847 = 852 := by decide +kernel

theorem l130862 : P.leaf 18 130862 = 352 := by decide +kernel

theorem l130863 : P.leaf 18 130863 = 576 := by decide +kernel

theorem l130876 : P.leaf 18 130876 = 160 := by decide +kernel

theorem l130877 : P.leaf 18 130877 = 544 := by decide +kernel

theorem l130878 : P.leaf 18 130878 = 464 := by decide +kernel

theorem l130879 : P.leaf 18 130879 = 1040 := by decide +kernel

theorem l130901 : P.leaf 18 130901 = 982 := by decide +kernel

theorem segOK : checkSeg 20 perms 129991 130903 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1633968 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 129991 130903 5760 1633968 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l129991 (.cons l129995 (.cons l129999 (.cons l130003 (.cons l130005 (.cons l130007 (.cons l130011 (.cons l130013 (.cons l130015 (.cons l130018 (.cons l130019 (.cons l130022 (.cons l130023 (.cons l130026 (.cons l130027 (.cons l130030 (.cons l130031 (.cons l130032 (.cons l130034 (.cons l130035 (.cons l130036 (.cons l130037 (.cons l130038 (.cons l130039 (.cons l130042 (.cons l130043 (.cons l130044 (.cons l130045 (.cons l130046 (.cons l130047 (.cons l130831 (.cons l130845 (.cons l130847 (.cons l130862 (.cons l130863 (.cons l130876 (.cons l130877 (.cons l130878 (.cons l130879 (.cons l130901 (.nil))))))))))))))))))))))))))))))))))))))))))

end S63

end RACert.S0N3.C0
