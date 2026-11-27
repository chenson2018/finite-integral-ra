/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S4

open RACert RACert.Problem

theorem cover1644 : P.CoversSplit 26 10 1644 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1644_0 : P.sumLeaves 26 1683456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1644) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1644 (by decide)
  decide +kernel

theorem h1644 : P.leaf 36 1644 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1644_0 (.nil)) (by decide) (by decide))

theorem cover1645 : P.CoversSplit 26 10 1645 0xf0000f0000f00008000000000000000000000000000000000000000000000000f0000a0000f00008000000000000000000000000000000000000000000000000f0000f0000c00008000000000000000000000000000000000000000000000000f0000a0000c00008000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 475, 922, 930, 972, 979, 1265, 1273]) (by decide +kernel)

theorem c1645_0 : P.sumLeaves 26 1684480 1024 = 6928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1645) (lo := 0) (len := 1024) (W := 6928) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem h1645 : P.leaf 36 1645 = 6928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6928)]) (.cons c1645_0 (.nil)) (by decide) (by decide))

theorem cover1646 : P.CoversSplit 26 10 1646 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1646_0 : P.sumLeaves 26 1685504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1646) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1646 (by decide)
  decide +kernel

theorem h1646 : P.leaf 36 1646 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1646_0 (.nil)) (by decide) (by decide))

theorem cover1647 : P.CoversSplit 26 10 1647 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c1647_0 : P.sumLeaves 26 1686528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1647) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1647 (by decide)
  decide +kernel

theorem h1647 : P.leaf 36 1647 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1647_0 (.nil)) (by decide) (by decide))

theorem cover1662 : P.CoversSplit 26 10 1662 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1662_0 : P.sumLeaves 26 1701888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1662) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1662 (by decide)
  decide +kernel

theorem h1662 : P.leaf 36 1662 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1662_0 (.nil)) (by decide) (by decide))

theorem cover1663 : P.CoversSplit 26 10 1663 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c1663_0 : P.sumLeaves 26 1702912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1663) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1663 (by decide)
  decide +kernel

theorem h1663 : P.leaf 36 1663 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1663_0 (.nil)) (by decide) (by decide))

theorem cover1700 : P.CoversSplit 26 10 1700 0xcc00cc0000000000cc00c0000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000030000000000000000000003000000000000000000000000000000000000000003000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 873, 881, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c1700_0 : P.sumLeaves 26 1740800 1024 = 38926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1700) (lo := 0) (len := 1024) (W := 38926) check rows elimOK (by decide) (by decide) cover1700 (by decide)
  decide +kernel

theorem h1700 : P.leaf 36 1700 = 38926 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 38926)]) (.cons c1700_0 (.nil)) (by decide) (by decide))

theorem cover1701 : P.CoversSplit 26 10 1701 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1701_0 : P.sumLeaves 26 1741824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1701) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1701 (by decide)
  decide +kernel

theorem h1701 : P.leaf 36 1701 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1701_0 (.nil)) (by decide) (by decide))

theorem cover1703 : P.CoversSplit 26 10 1703 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1703_0 : P.sumLeaves 26 1743872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1703) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1703 (by decide)
  decide +kernel

theorem h1703 : P.leaf 36 1703 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1703_0 (.nil)) (by decide) (by decide))

theorem cover1704 : P.CoversSplit 26 10 1704 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1704_0 : P.sumLeaves 26 1744896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1704) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1704 (by decide)
  decide +kernel

theorem h1704 : P.leaf 36 1704 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1704_0 (.nil)) (by decide) (by decide))

theorem cover1705 : P.CoversSplit 26 10 1705 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1705_0 : P.sumLeaves 26 1745920 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1705) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1705 (by decide)
  decide +kernel

theorem h1705 : P.leaf 36 1705 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1705_0 (.nil)) (by decide) (by decide))

theorem cover1707 : P.CoversSplit 26 10 1707 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1707_0 : P.sumLeaves 26 1747968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1707) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1707 (by decide)
  decide +kernel

theorem h1707 : P.leaf 36 1707 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1707_0 (.nil)) (by decide) (by decide))

theorem cover1708 : P.CoversSplit 26 10 1708 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1708_0 : P.sumLeaves 26 1748992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1708) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1708 (by decide)
  decide +kernel

theorem h1708 : P.leaf 36 1708 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1708_0 (.nil)) (by decide) (by decide))

theorem cover1709 : P.CoversSplit 26 10 1709 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1709_0 : P.sumLeaves 26 1750016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1709) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1709 (by decide)
  decide +kernel

theorem h1709 : P.leaf 36 1709 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1709_0 (.nil)) (by decide) (by decide))

theorem cover1711 : P.CoversSplit 26 10 1711 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [524]) (by decide +kernel)

theorem c1711_0 : P.sumLeaves 26 1752064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1711) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1711 (by decide)
  decide +kernel

theorem h1711 : P.leaf 36 1711 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1711_0 (.nil)) (by decide) (by decide))

theorem cover1719 : P.CoversSplit 26 10 1719 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1719_0 : P.sumLeaves 26 1760256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1719) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1719 (by decide)
  decide +kernel

theorem h1719 : P.leaf 36 1719 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1719_0 (.nil)) (by decide) (by decide))

theorem cover1720 : P.CoversSplit 26 10 1720 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1720_0 : P.sumLeaves 26 1761280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1720) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1720 (by decide)
  decide +kernel

theorem h1720 : P.leaf 36 1720 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1720_0 (.nil)) (by decide) (by decide))

theorem cover1721 : P.CoversSplit 26 10 1721 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1721_0 : P.sumLeaves 26 1762304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1721) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1721 (by decide)
  decide +kernel

theorem h1721 : P.leaf 36 1721 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1721_0 (.nil)) (by decide) (by decide))

theorem cover1723 : P.CoversSplit 26 10 1723 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1723_0 : P.sumLeaves 26 1764352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1723) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1723 (by decide)
  decide +kernel

theorem h1723 : P.leaf 36 1723 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1723_0 (.nil)) (by decide) (by decide))

theorem cover1724 : P.CoversSplit 26 10 1724 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1724_0 : P.sumLeaves 26 1765376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1724) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1724 (by decide)
  decide +kernel

theorem h1724 : P.leaf 36 1724 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1724_0 (.nil)) (by decide) (by decide))

theorem cover1725 : P.CoversSplit 26 10 1725 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1725_0 : P.sumLeaves 26 1766400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1725) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1725 (by decide)
  decide +kernel

theorem h1725 : P.leaf 36 1725 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1725_0 (.nil)) (by decide) (by decide))

theorem cover1727 : P.CoversSplit 26 10 1727 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1727_0 : P.sumLeaves 26 1768448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1727) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1727 (by decide)
  decide +kernel

theorem h1727 : P.leaf 36 1727 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1727_0 (.nil)) (by decide) (by decide))

theorem cover1740 : P.CoversSplit 26 10 1740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1740_0 : P.sumLeaves 26 1781760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1740) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1740 (by decide)
  decide +kernel

theorem h1740 : P.leaf 36 1740 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1740_0 (.nil)) (by decide) (by decide))

theorem cover1741 : P.CoversSplit 26 10 1741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1741_0 : P.sumLeaves 26 1782784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1741) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1741 (by decide)
  decide +kernel

theorem h1741 : P.leaf 36 1741 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1741_0 (.nil)) (by decide) (by decide))

theorem cover1743 : P.CoversSplit 26 10 1743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1743_0 : P.sumLeaves 26 1784832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1743) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1743 (by decide)
  decide +kernel

theorem h1743 : P.leaf 36 1743 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1743_0 (.nil)) (by decide) (by decide))

theorem cover1756 : P.CoversSplit 26 10 1756 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [880]) (by decide +kernel)

theorem c1756_0 : P.sumLeaves 26 1798144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1756) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1756 (by decide)
  decide +kernel

theorem h1756 : P.leaf 36 1756 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1756_0 (.nil)) (by decide) (by decide))

theorem cover1757 : P.CoversSplit 26 10 1757 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1757_0 : P.sumLeaves 26 1799168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1757) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1757 (by decide)
  decide +kernel

theorem h1757 : P.leaf 36 1757 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1757_0 (.nil)) (by decide) (by decide))

theorem cover1759 : P.CoversSplit 26 10 1759 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1759_0 : P.sumLeaves 26 1801216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1759) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1759 (by decide)
  decide +kernel

theorem h1759 : P.leaf 36 1759 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1759_0 (.nil)) (by decide) (by decide))

theorem cover1772 : P.CoversSplit 26 10 1772 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1772_0 : P.sumLeaves 26 1814528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1772) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1772 (by decide)
  decide +kernel

theorem h1772 : P.leaf 36 1772 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1772_0 (.nil)) (by decide) (by decide))

theorem cover1773 : P.CoversSplit 26 10 1773 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c1773_0 : P.sumLeaves 26 1815552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1773) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1773 (by decide)
  decide +kernel

theorem h1773 : P.leaf 36 1773 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1773_0 (.nil)) (by decide) (by decide))

theorem cover1774 : P.CoversSplit 26 10 1774 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1774_0 : P.sumLeaves 26 1816576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1774) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1774 (by decide)
  decide +kernel

theorem h1774 : P.leaf 36 1774 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1774_0 (.nil)) (by decide) (by decide))

theorem cover1775 : P.CoversSplit 26 10 1775 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c1775_0 : P.sumLeaves 26 1817600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1775) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1775 (by decide)
  decide +kernel

theorem h1775 : P.leaf 36 1775 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1775_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1644, 180), (1645, 180), (1646, 360), (1647, 360), (1662, 180), (1663, 180), (1700, 60), (1701, 360), (1703, 360), (1704, 360), (1705, 720), (1707, 360), (1708, 360), (1709, 720), (1711, 360), (1719, 120), (1720, 360), (1721, 720), (1723, 360), (1724, 360), (1725, 720), (1727, 360), (1740, 360), (1741, 720), (1743, 360), (1756, 360), (1757, 720), (1759, 360), (1772, 360), (1773, 360), (1774, 720), (1775, 720)]

theorem segOK : checkSeg 20 perms 1644 1790 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1644 1790 13140 3582600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3582600)
    (SegSum.cons (w := 180) h1644 (SegSum.cons (w := 180) h1645 (SegSum.cons (w := 360) h1646 (SegSum.cons (w := 360) h1647 (SegSum.cons (w := 180) h1662 (SegSum.cons (w := 180) h1663 (SegSum.cons (w := 60) h1700 (SegSum.cons (w := 360) h1701 (SegSum.cons (w := 360) h1703 (SegSum.cons (w := 360) h1704 (SegSum.cons (w := 720) h1705 (SegSum.cons (w := 360) h1707 (SegSum.cons (w := 360) h1708 (SegSum.cons (w := 720) h1709 (SegSum.cons (w := 360) h1711 (SegSum.cons (w := 120) h1719 (SegSum.cons (w := 360) h1720 (SegSum.cons (w := 720) h1721 (SegSum.cons (w := 360) h1723 (SegSum.cons (w := 360) h1724 (SegSum.cons (w := 720) h1725 (SegSum.cons (w := 360) h1727 (SegSum.cons (w := 360) h1740 (SegSum.cons (w := 720) h1741 (SegSum.cons (w := 360) h1743 (SegSum.cons (w := 360) h1756 (SegSum.cons (w := 720) h1757 (SegSum.cons (w := 360) h1759 (SegSum.cons (w := 360) h1772 (SegSum.cons (w := 360) h1773 (SegSum.cons (w := 720) h1774 (SegSum.cons (w := 720) h1775 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S4
