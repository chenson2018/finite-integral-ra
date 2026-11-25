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

namespace S5

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(1406, 24), (1407, 24), (1525, 24), (1527, 24), (1535, 6), (1626, 4), (1627, 24), (1631, 12), (1641, 4), (1643, 24), (1647, 12), (1659, 12), (1661, 24), (1662, 24), (1663, 24), (1781, 12), (1782, 12), (1783, 24), (1791, 6), (1887, 24), (1903, 24), (1919, 12), (2007, 8), (2011, 8), (2015, 24), (2045, 12), (2047, 12), (4095, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(1406, 3177), (1407, 4796), (1525, 3177), (1527, 4704), (1535, 7034), (1626, 708), (1627, 1074), (1631, 2042), (1641, 530), (1643, 921), (1647, 2500), (1659, 1515), (1661, 1920), (1662, 2032), (1663, 3106), (1781, 1872), (1782, 1677), (1783, 2586), (1791, 3902), (1887, 4550), (1903, 4549), (1919, 7116), (2007, 4595), (2011, 4706), (2015, 6722), (2045, 6485), (2047, 9907), (4095, 14972)]

theorem l1406 : P.leaf 16 1406 = 3177 := by decide +kernel

theorem l1407 : P.leaf 16 1407 = 4796 := by decide +kernel

theorem l1525 : P.leaf 16 1525 = 3177 := by decide +kernel

theorem l1527 : P.leaf 16 1527 = 4704 := by decide +kernel

theorem l1535 : P.leaf 16 1535 = 7034 := by decide +kernel

theorem l1626 : P.leaf 16 1626 = 708 := by decide +kernel

theorem l1627 : P.leaf 16 1627 = 1074 := by decide +kernel

theorem l1631 : P.leaf 16 1631 = 2042 := by decide +kernel

theorem l1641 : P.leaf 16 1641 = 530 := by decide +kernel

theorem l1643 : P.leaf 16 1643 = 921 := by decide +kernel

theorem l1647 : P.leaf 16 1647 = 2500 := by decide +kernel

theorem l1659 : P.leaf 16 1659 = 1515 := by decide +kernel

theorem l1661 : P.leaf 16 1661 = 1920 := by decide +kernel

theorem l1662 : P.leaf 16 1662 = 2032 := by decide +kernel

theorem l1663 : P.leaf 16 1663 = 3106 := by decide +kernel

theorem l1781 : P.leaf 16 1781 = 1872 := by decide +kernel

theorem l1782 : P.leaf 16 1782 = 1677 := by decide +kernel

theorem l1783 : P.leaf 16 1783 = 2586 := by decide +kernel

theorem l1791 : P.leaf 16 1791 = 3902 := by decide +kernel

theorem l1887 : P.leaf 16 1887 = 4550 := by decide +kernel

theorem l1903 : P.leaf 16 1903 = 4549 := by decide +kernel

theorem l1919 : P.leaf 16 1919 = 7116 := by decide +kernel

theorem l2007 : P.leaf 16 2007 = 4595 := by decide +kernel

theorem l2011 : P.leaf 16 2011 = 4706 := by decide +kernel

theorem l2015 : P.leaf 16 2015 = 6722 := by decide +kernel

theorem l2045 : P.leaf 16 2045 = 6485 := by decide +kernel

theorem l2047 : P.leaf 16 2047 = 9907 := by decide +kernel

theorem l4095 : P.leaf 16 4095 = 14972 := by decide +kernel

theorem segOK : checkSeg 12 perms 1406 4096 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 1596852 = true := by decide +kernel

theorem total : OrbitSeg 12 perms (P.leaf 16) 1406 4096 445 1596852 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l1406 (.cons l1407 (.cons l1525 (.cons l1527 (.cons l1535 (.cons l1626 (.cons l1627 (.cons l1631 (.cons l1641 (.cons l1643 (.cons l1647 (.cons l1659 (.cons l1661 (.cons l1662 (.cons l1663 (.cons l1781 (.cons l1782 (.cons l1783 (.cons l1791 (.cons l1887 (.cons l1903 (.cons l1919 (.cons l2007 (.cons l2011 (.cons l2015 (.cons l2045 (.cons l2047 (.cons l4095 (.nil))))))))))))))))))))))))))))))

end S5

end RACert.S0N3.C5
