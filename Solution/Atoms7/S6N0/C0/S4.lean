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

theorem c1644_0 : P.sumLeaves 26 1683456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1644) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1644 (by decide)
  decide +kernel

theorem h1644 : P.leaf 36 1644 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1644_0 (.nil)) (by decide) (by decide))

theorem cover1645 : P.CoversSplit 26 10 1645 0xf0000f0000f00008000000000000000000000000000000000000000000000000f0000a0000f00008000000000000000000000000000000000000000000000000f0000f0000c00008000000000000000000000000000000000000000000000000f0000a0000c00008000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 475, 922, 930, 972, 979, 1265, 1273]) (by decide +kernel)

theorem c1645_0 : P.sumLeaves 26 1684480 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1645) (lo := 0) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_1 : P.leaf 32 26323 = 340 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 26323) (ss := [(22, 1, 433), (4, 1, 480), (7, 1, 825), (20, 12, 866), (21, 13, 867), (17, 12, 872), (18, 13, 879), (8, 1, 1217), (13, 0, 1658), (12, 0, 573), (15, 0, 572), (19, 0, 473), (9, 0, 915), (28, 1, 972), (29, 1, 979)]) (ids := [0, 1, 3, 4, 8, 9, 12, 14, 21, 22, 23, 24, 25, 28, 29, 30, 31]) (cs := [2, 3, 1, 4, 5, 1, 1, 0, 6, 7, 0, 0, 8, 0, 9, 0, 0, 0, 0, 0, 1, 10, 11, 12, 13, 14, 1, 1, 15, 16, 17, 18]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1645_1 : P.sumLeaves 26 1684672 64 = 340 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 26323) rows (by decide) (by decide)).symm.trans contract1645_1

theorem c1645_2 : P.sumLeaves 26 1684736 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1645) (lo := 256) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_3 : P.leaf 32 26327 = 1560 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 26327) (ss := [(4, 1, 480), (20, 12, 866), (21, 13, 867), (17, 12, 872), (18, 13, 879), (12, 0, 1665), (13, 0, 572), (15, 0, 572), (19, 0, 473), (7, 1, 810), (8, 1, 859), (9, 0, 915), (29, 1, 979)]) (ids := [0, 1, 3, 4, 8, 9, 12, 14, 20, 21, 22, 23, 25, 26, 28, 29, 30, 31, 24]) (cs := [2, 3, 1, 4, 5, 1, 1, 0, 6, 7, 0, 0, 8, 0, 9, 0, 0, 0, 0, 0, 10, 11, 12, 13, 20, 14, 15, 1, 16, 17, 18, 19]) (bs := [18, 1]) (W := 1560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1645_3 : P.sumLeaves 26 1684928 64 = 1560 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 26327) rows (by decide) (by decide)).symm.trans contract1645_3

theorem c1645_4 : P.sumLeaves 26 1684992 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1645) (lo := 512) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem contract1645_5 : P.leaf 32 26331 = 1560 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 26331) (ss := [(4, 1, 480), (20, 12, 866), (21, 13, 867), (17, 12, 872), (18, 13, 879), (13, 0, 1658), (12, 0, 573), (15, 0, 572), (19, 0, 473), (7, 1, 810), (8, 1, 859), (9, 0, 915), (28, 1, 972)]) (ids := [0, 1, 3, 4, 8, 9, 12, 14, 20, 21, 22, 23, 24, 27, 28, 29, 30, 31, 25]) (cs := [2, 3, 1, 4, 5, 1, 1, 0, 6, 7, 0, 0, 8, 0, 9, 0, 0, 0, 0, 0, 10, 11, 12, 13, 14, 20, 1, 15, 16, 17, 18, 19]) (bs := [18, 1]) (W := 1560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1645_5 : P.sumLeaves 26 1685184 64 = 1560 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 26331) rows (by decide) (by decide)).symm.trans contract1645_5

theorem c1645_6 : P.sumLeaves 26 1685248 256 = 3468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1645) (lo := 768) (len := 256) (W := 3468) check rows elimOK (by decide) (by decide) cover1645 (by decide)
  decide +kernel

theorem h1645 : P.leaf 36 1645 = 6928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 0), (64, 340), (192, 0), (64, 1560), (192, 0), (64, 1560), (256, 3468)]) (.cons c1645_0 (.cons c1645_1 (.cons c1645_2 (.cons c1645_3 (.cons c1645_4 (.cons c1645_5 (.cons c1645_6 (.nil)))))))) (by decide) (by decide))

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

noncomputable def f1700 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (1740800 + i)

theorem c1700_0 : rowSum f1700 0 1024 = 38926 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1700) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover1700 (by decide)
  decide +kernel

theorem sum1700 : rowSum f1700 0 1024 = 38926 :=
  c1700_0

theorem h1700 : P.leaf 36 1700 = 38926 :=
  leaf_weighted (k := 26) (d := 10) (H := 1700) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 1700) (by decide) (by decide +kernel)) sum1700

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
