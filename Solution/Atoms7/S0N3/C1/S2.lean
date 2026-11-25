/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

namespace S2

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(846, 4), (847, 4), (852, 4), (853, 4), (854, 4), (855, 4), (856, 4), (857, 4), (858, 4), (859, 4), (860, 8), (861, 8), (862, 8), (863, 8), (892, 2), (893, 2), (894, 2), (895, 2), (960, 1), (961, 2), (963, 1), (964, 4), (965, 8), (967, 4), (972, 4), (973, 4), (974, 4), (975, 4), (984, 2), (985, 4), (987, 2), (988, 4), (989, 8), (991, 4), (1020, 1), (1021, 2), (1023, 1), (1024, 1), (1025, 2), (1027, 1), (1028, 4), (1029, 8), (1031, 4), (1036, 4), (1037, 4), (1038, 4), (1039, 4), (1048, 2), (1049, 4), (1051, 2), (1052, 4), (1053, 8), (1055, 4), (1084, 1), (1085, 2), (1087, 1), (1088, 2)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 622, 580, 601, 627, 601, 627, 0, 531, 531, 433, 628, 628, 433, 1217, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(846, 256), (847, 1836), (854, 379), (855, 1354), (856, 0), (857, 0), (858, 543), (859, 1992), (862, 1446), (863, 4764), (892, 3193), (893, 7672), (894, 5476), (895, 22432), (960, 598), (961, 238), (963, 876), (964, 45), (965, 128), (967, 1452), (972, 218), (973, 1290), (974, 628), (975, 3860), (984, 652), (985, 2435), (987, 8060), (988, 1474), (989, 3696), (991, 9796), (1020, 5058), (1021, 8970), (1023, 26413), (1024, 482), (1025, 65), (1027, 71), (1028, 2), (1048, 164), (1087, 1318), (1088, 30)]

theorem l846 : P.leaf 17 846 = 256 := by decide +kernel

theorem l847 : P.leaf 17 847 = 1836 := by decide +kernel

theorem l854 : P.leaf 17 854 = 379 := by decide +kernel

theorem l855 : P.leaf 17 855 = 1354 := by decide +kernel

theorem l856 : P.leaf 17 856 = 0 := by decide +kernel

theorem l857 : P.leaf 17 857 = 0 := by decide +kernel

theorem l858 : P.leaf 17 858 = 543 := by decide +kernel

theorem l859 : P.leaf 17 859 = 1992 := by decide +kernel

theorem l862 : P.leaf 17 862 = 1446 := by decide +kernel

theorem l863 : P.leaf 17 863 = 4764 := by decide +kernel

theorem l892 : P.leaf 17 892 = 3193 := by decide +kernel

theorem l893 : P.leaf 17 893 = 7672 := by decide +kernel

theorem l894 : P.leaf 17 894 = 5476 := by decide +kernel

theorem l895 : P.leaf 17 895 = 22432 := by decide +kernel

theorem l960 : P.leaf 17 960 = 598 := by decide +kernel

theorem l961 : P.leaf 17 961 = 238 := by decide +kernel

theorem l963 : P.leaf 17 963 = 876 := by decide +kernel

theorem l964 : P.leaf 17 964 = 45 := by decide +kernel

theorem l965 : P.leaf 17 965 = 128 := by decide +kernel

theorem l967 : P.leaf 17 967 = 1452 := by decide +kernel

theorem l972 : P.leaf 17 972 = 218 := by decide +kernel

theorem l973 : P.leaf 17 973 = 1290 := by decide +kernel

theorem l974 : P.leaf 17 974 = 628 := by decide +kernel

theorem l975 : P.leaf 17 975 = 3860 := by decide +kernel

theorem l984 : P.leaf 17 984 = 652 := by decide +kernel

theorem l985 : P.leaf 17 985 = 2435 := by decide +kernel

theorem l987 : P.leaf 17 987 = 8060 := by decide +kernel

theorem l988 : P.leaf 17 988 = 1474 := by decide +kernel

theorem l989 : P.leaf 17 989 = 3696 := by decide +kernel

theorem l991 : P.leaf 17 991 = 9796 := by decide +kernel

theorem l1020 : P.leaf 17 1020 = 5058 := by decide +kernel

theorem l1021 : P.leaf 17 1021 = 8970 := by decide +kernel

theorem l1023 : P.leaf 17 1023 = 26413 := by decide +kernel

theorem l1024 : P.leaf 17 1024 = 482 := by decide +kernel

theorem l1025 : P.leaf 17 1025 = 65 := by decide +kernel

theorem l1027 : P.leaf 17 1027 = 71 := by decide +kernel

theorem l1028 : P.leaf 17 1028 = 2 := by decide +kernel

theorem l1048 : P.leaf 17 1048 = 164 := by decide +kernel

theorem l1087 : P.leaf 17 1087 = 1318 := by decide +kernel

theorem l1088 : P.leaf 17 1088 = 30 := by decide +kernel

theorem segOK : checkSeg 11 perms 846 1089 seg = true := by decide +kernel

theorem evOK : P.checkEv 17 seg ev live 0 339232 = true := by decide +kernel

theorem total : OrbitSeg 11 perms (P.leaf 17) 846 1089 210 339232 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l846 (.cons l847 (.cons l854 (.cons l855 (.cons l856 (.cons l857 (.cons l858 (.cons l859 (.cons l862 (.cons l863 (.cons l892 (.cons l893 (.cons l894 (.cons l895 (.cons l960 (.cons l961 (.cons l963 (.cons l964 (.cons l965 (.cons l967 (.cons l972 (.cons l973 (.cons l974 (.cons l975 (.cons l984 (.cons l985 (.cons l987 (.cons l988 (.cons l989 (.cons l991 (.cons l1020 (.cons l1021 (.cons l1023 (.cons l1024 (.cons l1025 (.cons l1027 (.cons l1028 (.cons l1048 (.cons l1087 (.cons l1088 (.nil))))))))))))))))))))))))))))))))))))))))))

end S2

end RACert.S0N3.C1
