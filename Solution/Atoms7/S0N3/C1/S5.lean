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

namespace S5

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1868, 4), (1869, 4), (1870, 4), (1871, 4), (1876, 4), (1877, 4), (1878, 4), (1879, 4), (1880, 4), (1881, 4), (1882, 4), (1883, 4), (1884, 8), (1885, 8), (1886, 8), (1887, 8), (1916, 2), (1917, 2), (1918, 2), (1919, 2), (1984, 1), (1985, 2), (1987, 1), (1988, 4), (1989, 8), (1991, 4), (1996, 4), (1997, 4), (1998, 4), (1999, 4), (2008, 2), (2009, 4), (2011, 2), (2012, 4), (2013, 8), (2015, 4), (2044, 1), (2045, 2), (2047, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1868, 172), (1869, 1227), (1870, 256), (1871, 1836), (1878, 379), (1879, 1354), (1880, 0), (1881, 0), (1882, 543), (1883, 1992), (1886, 1446), (1887, 4768), (1916, 3193), (1917, 7854), (1918, 5544), (1919, 24778), (1984, 357), (1985, 208), (1987, 876), (1988, 45), (1989, 128), (1991, 1452), (1996, 218), (1997, 1290), (1998, 628), (1999, 3860), (2008, 654), (2009, 2436), (2011, 8060), (2012, 1474), (2013, 3696), (2015, 9820), (2044, 5058), (2045, 9164), (2047, 31725)]

theorem l1868 : P.leaf 17 1868 = 172 := by decide +kernel

theorem l1869 : P.leaf 17 1869 = 1227 := by decide +kernel

theorem l1870 : P.leaf 17 1870 = 256 := by decide +kernel

theorem l1871 : P.leaf 17 1871 = 1836 := by decide +kernel

theorem l1878 : P.leaf 17 1878 = 379 := by decide +kernel

theorem l1879 : P.leaf 17 1879 = 1354 := by decide +kernel

theorem l1880 : P.leaf 17 1880 = 0 := by decide +kernel

theorem l1881 : P.leaf 17 1881 = 0 := by decide +kernel

theorem l1882 : P.leaf 17 1882 = 543 := by decide +kernel

theorem l1883 : P.leaf 17 1883 = 1992 := by decide +kernel

theorem l1886 : P.leaf 17 1886 = 1446 := by decide +kernel

theorem l1887 : P.leaf 17 1887 = 4768 := by decide +kernel

theorem l1916 : P.leaf 17 1916 = 3193 := by decide +kernel

theorem l1917 : P.leaf 17 1917 = 7854 := by decide +kernel

theorem l1918 : P.leaf 17 1918 = 5544 := by decide +kernel

theorem l1919 : P.leaf 17 1919 = 24778 := by decide +kernel

theorem l1984 : P.leaf 17 1984 = 357 := by decide +kernel

theorem l1985 : P.leaf 17 1985 = 208 := by decide +kernel

theorem l1987 : P.leaf 17 1987 = 876 := by decide +kernel

theorem l1988 : P.leaf 17 1988 = 45 := by decide +kernel

theorem l1989 : P.leaf 17 1989 = 128 := by decide +kernel

theorem l1991 : P.leaf 17 1991 = 1452 := by decide +kernel

theorem l1996 : P.leaf 17 1996 = 218 := by decide +kernel

theorem l1997 : P.leaf 17 1997 = 1290 := by decide +kernel

theorem l1998 : P.leaf 17 1998 = 628 := by decide +kernel

theorem l1999 : P.leaf 17 1999 = 3860 := by decide +kernel

theorem l2008 : P.leaf 17 2008 = 654 := by decide +kernel

theorem l2009 : P.leaf 17 2009 = 2436 := by decide +kernel

theorem l2011 : P.leaf 17 2011 = 8060 := by decide +kernel

theorem l2012 : P.leaf 17 2012 = 1474 := by decide +kernel

theorem l2013 : P.leaf 17 2013 = 3696 := by decide +kernel

theorem l2015 : P.leaf 17 2015 = 9820 := by decide +kernel

theorem l2044 : P.leaf 17 2044 = 5058 := by decide +kernel

theorem l2045 : P.leaf 17 2045 = 9164 := by decide +kernel

theorem l2047 : P.leaf 17 2047 = 31725 := by decide +kernel

theorem segOK : checkSeg 11 perms 1868 2048 seg = true := by decide +kernel

theorem evOK : P.checkEv 17 seg ev live 0 353158 = true := by decide +kernel

theorem total : OrbitSeg 11 perms (P.leaf 17) 1868 2048 152 353158 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1868 (.cons l1869 (.cons l1870 (.cons l1871 (.cons l1878 (.cons l1879 (.cons l1880 (.cons l1881 (.cons l1882 (.cons l1883 (.cons l1886 (.cons l1887 (.cons l1916 (.cons l1917 (.cons l1918 (.cons l1919 (.cons l1984 (.cons l1985 (.cons l1987 (.cons l1988 (.cons l1989 (.cons l1991 (.cons l1996 (.cons l1997 (.cons l1998 (.cons l1999 (.cons l2008 (.cons l2009 (.cons l2011 (.cons l2012 (.cons l2013 (.cons l2015 (.cons l2044 (.cons l2045 (.cons l2047 (.nil)))))))))))))))))))))))))))))))))))))

end S5

end RACert.S0N3.C1
