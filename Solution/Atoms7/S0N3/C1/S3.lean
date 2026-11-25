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

namespace S3

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1089, 2), (1090, 2), (1091, 2), (1092, 8), (1093, 8), (1094, 8), (1095, 8), (1100, 4), (1101, 4), (1102, 4), (1103, 4), (1108, 4), (1109, 4), (1110, 4), (1111, 4), (1112, 4), (1113, 4), (1114, 4), (1115, 4), (1116, 8), (1117, 8), (1118, 8), (1119, 8), (1148, 2), (1149, 2), (1150, 2), (1151, 2), (1216, 1), (1217, 2), (1219, 1), (1220, 4), (1221, 8), (1223, 4), (1228, 4), (1229, 4), (1230, 4), (1231, 4), (1240, 2), (1241, 4), (1243, 2), (1244, 4), (1245, 8), (1247, 4), (1276, 1), (1277, 2), (1279, 1), (1280, 2), (1281, 2), (1282, 2), (1283, 2), (1284, 8), (1285, 8), (1286, 8), (1287, 8), (1292, 4), (1293, 4), (1294, 4), (1295, 4), (1300, 4), (1301, 4), (1302, 4), (1303, 4), (1304, 4), (1305, 4), (1306, 4), (1307, 4), (1308, 8), (1309, 8), (1310, 8), (1311, 8), (1340, 2), (1341, 2), (1342, 2), (1343, 2), (1344, 2), (1345, 2), (1346, 2), (1347, 2), (1348, 8), (1349, 8), (1350, 8), (1351, 8), (1356, 4), (1357, 4), (1358, 4), (1359, 4), (1364, 4), (1365, 4), (1366, 4), (1367, 4), (1368, 4), (1369, 4), (1370, 4), (1371, 4), (1372, 8), (1373, 8), (1374, 8), (1375, 8), (1404, 2), (1405, 2), (1406, 2), (1407, 2), (1408, 2), (1409, 2), (1410, 2), (1411, 2), (1412, 8), (1413, 8), (1414, 8), (1415, 8), (1420, 4), (1421, 4), (1422, 4), (1423, 4), (1428, 4), (1429, 4), (1430, 4), (1431, 4), (1432, 4), (1433, 4)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 1315, 622, 581, 581, 602, 627, 602, 627, 434, 1301, 434, 581, 1315, 532, 532, 532, 434, 628, 434, 628, 434, 1218, 434, 1315, 0, 0, 0, 0, 623, 581, 602, 627, 602, 627, 0, 532, 532, 434, 628, 628, 434, 1218, 0, 433, 0, 433, 0, 433, 622, 433, 580, 433, 634, 433, 634, 433, 1301, 433, 580, 433, 531, 433, 531, 433, 635, 433, 635, 433, 1217, 433, 1315, 0, 0, 0, 0, 1315, 622, 622, 622, 0, 0, 0, 0, 1301, 1301, 1315, 1315, 0, 0, 0, 0, 1301, 1301, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 622, 622, 622, 602, 0, 602, 0, 1302, 1302, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1089, 12), (1090, 63), (1091, 12), (1216, 564), (1217, 96), (1219, 162), (1220, 21), (1240, 203), (1279, 4096), (1281, 12), (1283, 12), (1344, 24), (1345, 57), (1346, 60), (1347, 57), (1356, 8), (1357, 345), (1358, 12), (1359, 924), (1368, 0), (1369, 45), (1370, 492), (1371, 1449), (1374, 1133), (1375, 3266), (1404, 1882), (1405, 5333), (1406, 4115), (1407, 11433), (1408, 4), (1409, 24), (1410, 0), (1411, 0), (1412, 0), (1421, 327), (1423, 706), (1430, 300), (1431, 578), (1432, 0), (1433, 22)]

theorem l1089 : P.leaf 17 1089 = 12 := by decide +kernel

theorem l1090 : P.leaf 17 1090 = 63 := by decide +kernel

theorem l1091 : P.leaf 17 1091 = 12 := by decide +kernel

theorem l1216 : P.leaf 17 1216 = 564 := by decide +kernel

theorem l1217 : P.leaf 17 1217 = 96 := by decide +kernel

theorem l1219 : P.leaf 17 1219 = 162 := by decide +kernel

theorem l1220 : P.leaf 17 1220 = 21 := by decide +kernel

theorem l1240 : P.leaf 17 1240 = 203 := by decide +kernel

theorem l1279 : P.leaf 17 1279 = 4096 := by decide +kernel

theorem l1281 : P.leaf 17 1281 = 12 := by decide +kernel

theorem l1283 : P.leaf 17 1283 = 12 := by decide +kernel

theorem l1344 : P.leaf 17 1344 = 24 := by decide +kernel

theorem l1345 : P.leaf 17 1345 = 57 := by decide +kernel

theorem l1346 : P.leaf 17 1346 = 60 := by decide +kernel

theorem l1347 : P.leaf 17 1347 = 57 := by decide +kernel

theorem l1356 : P.leaf 17 1356 = 8 := by decide +kernel

theorem l1357 : P.leaf 17 1357 = 345 := by decide +kernel

theorem l1358 : P.leaf 17 1358 = 12 := by decide +kernel

theorem l1359 : P.leaf 17 1359 = 924 := by decide +kernel

theorem l1368 : P.leaf 17 1368 = 0 := by decide +kernel

theorem l1369 : P.leaf 17 1369 = 45 := by decide +kernel

theorem l1370 : P.leaf 17 1370 = 492 := by decide +kernel

theorem l1371 : P.leaf 17 1371 = 1449 := by decide +kernel

theorem l1374 : P.leaf 17 1374 = 1133 := by decide +kernel

theorem l1375 : P.leaf 17 1375 = 3266 := by decide +kernel

theorem l1404 : P.leaf 17 1404 = 1882 := by decide +kernel

theorem l1405 : P.leaf 17 1405 = 5333 := by decide +kernel

theorem l1406 : P.leaf 17 1406 = 4115 := by decide +kernel

theorem l1407 : P.leaf 17 1407 = 11433 := by decide +kernel

theorem l1408 : P.leaf 17 1408 = 4 := by decide +kernel

theorem l1409 : P.leaf 17 1409 = 24 := by decide +kernel

theorem l1410 : P.leaf 17 1410 = 0 := by decide +kernel

theorem l1411 : P.leaf 17 1411 = 0 := by decide +kernel

theorem l1412 : P.leaf 17 1412 = 0 := by decide +kernel

theorem l1421 : P.leaf 17 1421 = 327 := by decide +kernel

theorem l1423 : P.leaf 17 1423 = 706 := by decide +kernel

theorem l1430 : P.leaf 17 1430 = 300 := by decide +kernel

theorem l1431 : P.leaf 17 1431 = 578 := by decide +kernel

theorem l1432 : P.leaf 17 1432 = 0 := by decide +kernel

theorem l1433 : P.leaf 17 1433 = 22 := by decide +kernel

theorem segOK : checkSeg 11 perms 1089 1434 seg = true := by decide +kernel

theorem evOK : P.checkEv 17 seg ev live 0 107728 = true := by decide +kernel

theorem total : OrbitSeg 11 perms (P.leaf 17) 1089 1434 526 107728 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1089 (.cons l1090 (.cons l1091 (.cons l1216 (.cons l1217 (.cons l1219 (.cons l1220 (.cons l1240 (.cons l1279 (.cons l1281 (.cons l1283 (.cons l1344 (.cons l1345 (.cons l1346 (.cons l1347 (.cons l1356 (.cons l1357 (.cons l1358 (.cons l1359 (.cons l1368 (.cons l1369 (.cons l1370 (.cons l1371 (.cons l1374 (.cons l1375 (.cons l1404 (.cons l1405 (.cons l1406 (.cons l1407 (.cons l1408 (.cons l1409 (.cons l1410 (.cons l1411 (.cons l1412 (.cons l1421 (.cons l1423 (.cons l1430 (.cons l1431 (.cons l1432 (.cons l1433 (.nil))))))))))))))))))))))))))))))))))))))))))

end S3

end RACert.S0N3.C1
