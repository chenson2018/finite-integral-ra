/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C5.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

namespace S4

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(861, 24), (862, 24), (863, 24), (884, 6), (885, 24), (887, 12), (888, 6), (889, 24), (891, 12), (892, 12), (893, 24), (895, 12), (963, 2), (967, 12), (975, 6), (981, 24), (982, 24), (983, 24), (989, 12), (990, 12), (991, 12), (1013, 24), (1015, 12), (1020, 3), (1021, 12), (1023, 6), (1365, 8), (1366, 12), (1367, 24), (1369, 12), (1370, 24), (1371, 24), (1373, 24), (1374, 24), (1375, 24), (1399, 12), (1401, 24), (1402, 24), (1403, 24), (1405, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(861, 1492), (862, 1051), (863, 2240), (884, 539), (885, 1063), (887, 1559), (888, 517), (889, 836), (891, 1230), (892, 1160), (893, 1726), (895, 2719), (963, 1214), (967, 1940), (975, 2744), (981, 2057), (982, 1417), (983, 2923), (989, 3071), (990, 1984), (991, 4621), (1013, 2605), (1015, 3856), (1020, 2415), (1021, 3825), (1023, 6296), (1365, 1197), (1366, 837), (1367, 2073), (1369, 848), (1370, 553), (1371, 1211), (1373, 2113), (1374, 1274), (1375, 2890), (1399, 3448), (1401, 1553), (1402, 1312), (1403, 2058), (1405, 3257)]

theorem l861 : P.leaf 16 861 = 1492 := by decide +kernel

theorem l862 : P.leaf 16 862 = 1051 := by decide +kernel

theorem l863 : P.leaf 16 863 = 2240 := by decide +kernel

theorem l884 : P.leaf 16 884 = 539 := by decide +kernel

theorem l885 : P.leaf 16 885 = 1063 := by decide +kernel

theorem l887 : P.leaf 16 887 = 1559 := by decide +kernel

theorem l888 : P.leaf 16 888 = 517 := by decide +kernel

theorem l889 : P.leaf 16 889 = 836 := by decide +kernel

theorem l891 : P.leaf 16 891 = 1230 := by decide +kernel

theorem l892 : P.leaf 16 892 = 1160 := by decide +kernel

theorem l893 : P.leaf 16 893 = 1726 := by decide +kernel

theorem l895 : P.leaf 16 895 = 2719 := by decide +kernel

theorem l963 : P.leaf 16 963 = 1214 := by decide +kernel

theorem l967 : P.leaf 16 967 = 1940 := by decide +kernel

theorem l975 : P.leaf 16 975 = 2744 := by decide +kernel

theorem l981 : P.leaf 16 981 = 2057 := by decide +kernel

theorem l982 : P.leaf 16 982 = 1417 := by decide +kernel

theorem l983 : P.leaf 16 983 = 2923 := by decide +kernel

theorem l989 : P.leaf 16 989 = 3071 := by decide +kernel

theorem l990 : P.leaf 16 990 = 1984 := by decide +kernel

theorem l991 : P.leaf 16 991 = 4621 := by decide +kernel

theorem l1013 : P.leaf 16 1013 = 2605 := by decide +kernel

theorem l1015 : P.leaf 16 1015 = 3856 := by decide +kernel

theorem l1020 : P.leaf 16 1020 = 2415 := by decide +kernel

theorem l1021 : P.leaf 16 1021 = 3825 := by decide +kernel

theorem l1023 : P.leaf 16 1023 = 6296 := by decide +kernel

theorem l1365 : P.leaf 16 1365 = 1197 := by decide +kernel

theorem l1366 : P.leaf 16 1366 = 837 := by decide +kernel

theorem l1367 : P.leaf 16 1367 = 2073 := by decide +kernel

theorem l1369 : P.leaf 16 1369 = 848 := by decide +kernel

theorem l1370 : P.leaf 16 1370 = 553 := by decide +kernel

theorem l1371 : P.leaf 16 1371 = 1211 := by decide +kernel

theorem l1373 : P.leaf 16 1373 = 2113 := by decide +kernel

theorem l1374 : P.leaf 16 1374 = 1274 := by decide +kernel

theorem l1375 : P.leaf 16 1375 = 2890 := by decide +kernel

theorem l1399 : P.leaf 16 1399 = 3448 := by decide +kernel

theorem l1401 : P.leaf 16 1401 = 1553 := by decide +kernel

theorem l1402 : P.leaf 16 1402 = 1312 := by decide +kernel

theorem l1403 : P.leaf 16 1403 = 2058 := by decide +kernel

theorem l1405 : P.leaf 16 1405 = 3257 := by decide +kernel

theorem segOK : checkSeg 12 perms 861 1406 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 1309897 = true := by decide +kernel

theorem total : OrbitSeg 12 perms (P.leaf 16) 861 1406 673 1309897 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l861 (.cons l862 (.cons l863 (.cons l884 (.cons l885 (.cons l887 (.cons l888 (.cons l889 (.cons l891 (.cons l892 (.cons l893 (.cons l895 (.cons l963 (.cons l967 (.cons l975 (.cons l981 (.cons l982 (.cons l983 (.cons l989 (.cons l990 (.cons l991 (.cons l1013 (.cons l1015 (.cons l1020 (.cons l1021 (.cons l1023 (.cons l1365 (.cons l1366 (.cons l1367 (.cons l1369 (.cons l1370 (.cons l1371 (.cons l1373 (.cons l1374 (.cons l1375 (.cons l1399 (.cons l1401 (.cons l1402 (.cons l1403 (.cons l1405 (.nil))))))))))))))))))))))))))))))))))))))))))

end S4

end RACert.S0N3.C5
