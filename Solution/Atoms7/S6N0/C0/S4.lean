/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S4

open RACert RACert.Problem

theorem cover1644 : P.CoversSplit 26 10 1644 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1644 : P.leaf 36 1644 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1644) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1644) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1644 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2395 : P.CoversSplit 26 10 2395 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000050000000000000000000004000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 922, 930, 979, 1273, 1322, 1665]) (ps := [(11, [930], [872])]) (by decide +kernel)

theorem h2395 : P.leaf 36 2395 = 6928 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2395) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2395) (weight := fun _ => 1) (xs := [514, 554, 640, 642, 680, 682, 1023]) check rows elimOK (by decide) (by decide) cover2395 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1645 : P.leaf 36 1645 = 6928 :=
  orient4 (v := 2395) (by decide) (by decide +kernel) h2395

theorem cover1646 : P.CoversSplit 26 10 1646 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1646 : P.leaf 36 1646 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1646) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1646) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1646 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1647 : P.CoversSplit 26 10 1647 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h1647 : P.leaf 36 1647 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1647) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1647) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1647 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1662 : P.CoversSplit 26 10 1662 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1662 : P.leaf 36 1662 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1662) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1662) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1662 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1663 : P.CoversSplit 26 10 1663 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h1663 : P.leaf 36 1663 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1663) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1663) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1663 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2450 : P.CoversSplit 26 10 2450 0x8000000000000000000000000000000000000000000000001000000000000000000000000000000044004400000000000000000000000000110011000000000000000000000000000000000000000000000000000020000000000000001100110000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 489, 530, 538, 629, 636, 881, 922, 930, 972, 979, 1315, 1322]) (by decide +kernel)

theorem h2450 : P.leaf 36 2450 = 38926 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 2450) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 2450) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2450) (weight := rowWeight keep3 twice3) (xs := [256, 260, 272, 276, 341, 552, 556, 568, 572, 682, 686, 698, 702, 828, 1023]) check rows elimOK (by decide) (by decide) cover2450 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1700 : P.leaf 36 1700 = 38926 :=
  orient4 (v := 2450) (by decide) (by decide +kernel) h2450

theorem cover1701 : P.CoversSplit 26 10 1701 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1701 : P.leaf 36 1701 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1701) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1701) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1701 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1703 : P.CoversSplit 26 10 1703 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1703 : P.leaf 36 1703 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1703) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1703) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1703 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1704 : P.CoversSplit 26 10 1704 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1704 : P.leaf 36 1704 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1704) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1704) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1704 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1705 : P.CoversSplit 26 10 1705 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1705 : P.leaf 36 1705 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1705) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1705) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1705 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1707 : P.CoversSplit 26 10 1707 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1707 : P.leaf 36 1707 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1707) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1707) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1707 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1708 : P.CoversSplit 26 10 1708 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1708 : P.leaf 36 1708 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1708) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1708) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1708 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1709 : P.CoversSplit 26 10 1709 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1709 : P.leaf 36 1709 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1709) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1709) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1709 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1711 : P.CoversSplit 26 10 1711 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem h1711 : P.leaf 36 1711 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1711) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1711) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1719 : P.CoversSplit 26 10 1719 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1719 : P.leaf 36 1719 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1719) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1719) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1719 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1720 : P.CoversSplit 26 10 1720 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1720 : P.leaf 36 1720 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1720) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1720) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1720 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1721 : P.CoversSplit 26 10 1721 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1721 : P.leaf 36 1721 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1721) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1721) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1721 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1723 : P.CoversSplit 26 10 1723 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1723 : P.leaf 36 1723 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1723) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1723) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1723 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1724 : P.CoversSplit 26 10 1724 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1724 : P.leaf 36 1724 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1724) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1724) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1724 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1725 : P.CoversSplit 26 10 1725 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1725 : P.leaf 36 1725 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1725) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1725) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1725 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1727 : P.CoversSplit 26 10 1727 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1727 : P.leaf 36 1727 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1727) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1727) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1727 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1740 : P.CoversSplit 26 10 1740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1740 : P.leaf 36 1740 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1740) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1740) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1740 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1741 : P.CoversSplit 26 10 1741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1741 : P.leaf 36 1741 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1741) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1741) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1741 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1743 : P.CoversSplit 26 10 1743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1743 : P.leaf 36 1743 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1743) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1743) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1743 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1756 : P.CoversSplit 26 10 1756 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem h1756 : P.leaf 36 1756 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1756) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1756) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1756 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1757 : P.CoversSplit 26 10 1757 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1757 : P.leaf 36 1757 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1757) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1757) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1757 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1759 : P.CoversSplit 26 10 1759 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1759 : P.leaf 36 1759 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1759) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1759) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1759 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1772 : P.CoversSplit 26 10 1772 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1772 : P.leaf 36 1772 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1772) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1772) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1772 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1773 : P.CoversSplit 26 10 1773 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h1773 : P.leaf 36 1773 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1773) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1773) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1773 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1774 : P.CoversSplit 26 10 1774 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1774 : P.leaf 36 1774 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1774) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1774) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1774 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1775 : P.CoversSplit 26 10 1775 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h1775 : P.leaf 36 1775 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1775) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1775) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1775 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1644, 180), (1645, 180), (1646, 360), (1647, 360), (1662, 180), (1663, 180), (1700, 60), (1701, 360), (1703, 360), (1704, 360), (1705, 720), (1707, 360), (1708, 360), (1709, 720), (1711, 360), (1719, 120), (1720, 360), (1721, 720), (1723, 360), (1724, 360), (1725, 720), (1727, 360), (1740, 360), (1741, 720), (1743, 360), (1756, 360), (1757, 720), (1759, 360), (1772, 360), (1773, 360), (1774, 720), (1775, 720)]

theorem segOK : checkSeg 20 perms 1644 1790 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1644 1790 13140 3582600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3582600)
    (SegSum.cons (w := 180) h1644 (SegSum.cons (w := 180) h1645 (SegSum.cons (w := 360) h1646 (SegSum.cons (w := 360) h1647 (SegSum.cons (w := 180) h1662 (SegSum.cons (w := 180) h1663 (SegSum.cons (w := 60) h1700 (SegSum.cons (w := 360) h1701 (SegSum.cons (w := 360) h1703 (SegSum.cons (w := 360) h1704 (SegSum.cons (w := 720) h1705 (SegSum.cons (w := 360) h1707 (SegSum.cons (w := 360) h1708 (SegSum.cons (w := 720) h1709 (SegSum.cons (w := 360) h1711 (SegSum.cons (w := 120) h1719 (SegSum.cons (w := 360) h1720 (SegSum.cons (w := 720) h1721 (SegSum.cons (w := 360) h1723 (SegSum.cons (w := 360) h1724 (SegSum.cons (w := 720) h1725 (SegSum.cons (w := 360) h1727 (SegSum.cons (w := 360) h1740 (SegSum.cons (w := 720) h1741 (SegSum.cons (w := 360) h1743 (SegSum.cons (w := 360) h1756 (SegSum.cons (w := 720) h1757 (SegSum.cons (w := 360) h1759 (SegSum.cons (w := 360) h1772 (SegSum.cons (w := 360) h1773 (SegSum.cons (w := 720) h1774 (SegSum.cons (w := 720) h1775 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S4
