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

namespace S4

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1434, 4), (1435, 4), (1436, 8), (1437, 8), (1438, 8), (1439, 8), (1468, 2), (1469, 2), (1470, 2), (1471, 2), (1472, 2), (1473, 2), (1474, 2), (1475, 2), (1476, 8), (1477, 8), (1478, 8), (1479, 8), (1484, 4), (1485, 4), (1486, 4), (1487, 4), (1492, 4), (1493, 4), (1494, 4), (1495, 4), (1496, 4), (1497, 4), (1498, 4), (1499, 4), (1500, 8), (1501, 8), (1502, 8), (1503, 8), (1532, 2), (1533, 2), (1534, 2), (1535, 2), (1792, 1), (1793, 2), (1795, 1), (1796, 4), (1797, 8), (1799, 4), (1804, 4), (1805, 4), (1806, 4), (1807, 4), (1816, 2), (1817, 4), (1819, 2), (1820, 4), (1821, 8), (1823, 4), (1852, 1), (1853, 2), (1855, 1), (1856, 2), (1857, 2), (1858, 2), (1859, 2), (1860, 8), (1861, 8), (1862, 8), (1863, 8)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 602, 1302, 602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 433, 531, 531, 433, 580, 580, 433, 634, 433, 634, 433, 531, 531, 433, 635, 635, 433, 1217, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1434, 30), (1435, 563), (1439, 2186), (1468, 1815), (1469, 4914), (1470, 4604), (1471, 18076), (1472, 48), (1473, 127), (1474, 56), (1475, 282), (1476, 3), (1477, 9), (1478, 32), (1479, 374), (1484, 210), (1485, 1290), (1486, 320), (1487, 2004), (1494, 340), (1495, 1002), (1496, 18), (1497, 58), (1498, 660), (1499, 1824), (1502, 1810), (1503, 4398), (1532, 4568), (1533, 8464), (1534, 6744), (1535, 24962), (1855, 16452), (1856, 0), (1857, 0), (1858, 56), (1859, 282), (1860, 0), (1861, 0), (1862, 32), (1863, 374)]

theorem l1434 : P.leaf 17 1434 = 30 := by decide +kernel

theorem l1435 : P.leaf 17 1435 = 563 := by decide +kernel

theorem l1439 : P.leaf 17 1439 = 2186 := by decide +kernel

theorem l1468 : P.leaf 17 1468 = 1815 := by decide +kernel

theorem l1469 : P.leaf 17 1469 = 4914 := by decide +kernel

theorem l1470 : P.leaf 17 1470 = 4604 := by decide +kernel

theorem l1471 : P.leaf 17 1471 = 18076 := by decide +kernel

theorem l1472 : P.leaf 17 1472 = 48 := by decide +kernel

theorem l1473 : P.leaf 17 1473 = 127 := by decide +kernel

theorem l1474 : P.leaf 17 1474 = 56 := by decide +kernel

theorem l1475 : P.leaf 17 1475 = 282 := by decide +kernel

theorem l1476 : P.leaf 17 1476 = 3 := by decide +kernel

theorem l1477 : P.leaf 17 1477 = 9 := by decide +kernel

theorem l1478 : P.leaf 17 1478 = 32 := by decide +kernel

theorem l1479 : P.leaf 17 1479 = 374 := by decide +kernel

theorem l1484 : P.leaf 17 1484 = 210 := by decide +kernel

theorem l1485 : P.leaf 17 1485 = 1290 := by decide +kernel

theorem l1486 : P.leaf 17 1486 = 320 := by decide +kernel

theorem l1487 : P.leaf 17 1487 = 2004 := by decide +kernel

theorem l1494 : P.leaf 17 1494 = 340 := by decide +kernel

theorem l1495 : P.leaf 17 1495 = 1002 := by decide +kernel

theorem l1496 : P.leaf 17 1496 = 18 := by decide +kernel

theorem l1497 : P.leaf 17 1497 = 58 := by decide +kernel

theorem l1498 : P.leaf 17 1498 = 660 := by decide +kernel

theorem l1499 : P.leaf 17 1499 = 1824 := by decide +kernel

theorem l1502 : P.leaf 17 1502 = 1810 := by decide +kernel

theorem l1503 : P.leaf 17 1503 = 4398 := by decide +kernel

theorem l1532 : P.leaf 17 1532 = 4568 := by decide +kernel

theorem l1533 : P.leaf 17 1533 = 8464 := by decide +kernel

theorem l1534 : P.leaf 17 1534 = 6744 := by decide +kernel

theorem l1535 : P.leaf 17 1535 = 24962 := by decide +kernel

theorem l1855 : P.leaf 17 1855 = 16452 := by decide +kernel

theorem l1856 : P.leaf 17 1856 = 0 := by decide +kernel

theorem l1857 : P.leaf 17 1857 = 0 := by decide +kernel

theorem l1858 : P.leaf 17 1858 = 56 := by decide +kernel

theorem l1859 : P.leaf 17 1859 = 282 := by decide +kernel

theorem l1860 : P.leaf 17 1860 = 0 := by decide +kernel

theorem l1861 : P.leaf 17 1861 = 0 := by decide +kernel

theorem l1862 : P.leaf 17 1862 = 32 := by decide +kernel

theorem l1863 : P.leaf 17 1863 = 374 := by decide +kernel

theorem segOK : checkSeg 11 perms 1434 1868 seg = true := by decide +kernel

theorem evOK : P.checkEv 17 seg ev live 0 273468 = true := by decide +kernel

theorem total : OrbitSeg 11 perms (P.leaf 17) 1434 1868 280 273468 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1434 (.cons l1435 (.cons l1439 (.cons l1468 (.cons l1469 (.cons l1470 (.cons l1471 (.cons l1472 (.cons l1473 (.cons l1474 (.cons l1475 (.cons l1476 (.cons l1477 (.cons l1478 (.cons l1479 (.cons l1484 (.cons l1485 (.cons l1486 (.cons l1487 (.cons l1494 (.cons l1495 (.cons l1496 (.cons l1497 (.cons l1498 (.cons l1499 (.cons l1502 (.cons l1503 (.cons l1532 (.cons l1533 (.cons l1534 (.cons l1535 (.cons l1855 (.cons l1856 (.cons l1857 (.cons l1858 (.cons l1859 (.cons l1860 (.cons l1861 (.cons l1862 (.cons l1863 (.nil))))))))))))))))))))))))))))))))))))))))))

end S4

end RACert.S0N3.C1
